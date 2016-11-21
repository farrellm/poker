{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Lib where

import BasicPrelude

import Control.Monad.ST
import Control.Monad.State.Strict
       (MonadState, get, put, evalStateT, runState)
import Data.Bits
import qualified Data.Text.Format as F
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Lens.Micro.Platform
import System.Random.MWC

newtype Suit = Suit { _suit :: Int }
  deriving (Eq, Ord)

instance Show Suit where
  show (Suit 0) = "♧"
  show (Suit 1) = "♢"
  show (Suit 2) = "♡"
  show (Suit _) = "♤"

newtype Rank = Rank { _rank :: Int }
  deriving (Eq, Ord, Enum)

instance Show Rank where
  show (Rank  9) = "T"
  show (Rank 10) = "J"
  show (Rank 11) = "Q"
  show (Rank 12) = "K"
  show (Rank 13) = "A"
  show (Rank r) = show (r+1)

type Card = (Rank, Suit)

rank :: (a, b) -> a
rank = fst

suit :: (a, b) -> b
suit = snd

newtype BitVector = BitVector { _bits :: Word32 }
  deriving (Show, Eq, Ord, Bits, FiniteBits)

data Partial
  = PNull
  | PHighCard
  | PPair Rank
  | PTwoPair Rank Rank
  | PTrips Rank
  | PFullHouse Rank Rank
  | PQuads Rank
  deriving (Show)

data Result
  = HighCard BitVector
  | Pair Rank BitVector
  | TwoPair Rank Rank BitVector
  | Trips Rank BitVector
  | Straight Int
  | Flush BitVector
  | FullHouse Rank Rank
  | Quads Rank BitVector
  | StraightFlush Int
  deriving (Show,Eq,Ord)

suits :: [Suit]
suits = map Suit [0..3]

[club, diamond, heart, spade] = suits
[one,two,three,four,five,six,seven,eight,nine,ten,jack,queen,king,ace] =
  map Rank [0..13]

ranks :: [Rank]
ranks = [two .. ace]

type Deck = V.Vector Card

data PokerState =
  PokerState {_poker_seed :: Seed}
  deriving (Show)

makeLenses ''PokerState

data TrialState =
  TrialState {_trial_deck :: Deck
             ,_trial_poker :: PokerState}
  deriving (Show)

makeLenses ''TrialState

newDeck :: Deck
newDeck = V.fromList $ do
  r <- ranks
  s <- suits
  pure (r, s)

shuffle :: (MonadState TrialState m) => m ()
shuffle =
  do seed <- use (trial_poker . poker_seed)
     let (seed',swaps) = runST (randSwaps seed)
     trial_deck %= doSwaps (zip [0 .. 51] swaps)
     (trial_poker . poker_seed) .= seed'

  where randSwaps seed =
          do gen <- restore seed
             ss <- mapM (\i -> uniformR (i,51) gen) [0 .. 51]
             seed <- save gen
             pure (seed,ss)

        doSwaps ss d =
           V.create $
           do md <- V.thaw d
              mapM_ (uncurry (MV.swap md)) ss
              pure md

draw :: (MonadState TrialState m) => Card -> Card -> m ()
draw c1 c2 = trial_deck %= V.filter (\c -> c /= c1 && c /= c2)

deal :: (MonadState TrialState m) => Int -> m Deck
deal n = do
  (h, d) <- V.splitAt n <$> use trial_deck
  trial_deck .= d
  pure h

rankHand :: Deck -> Result
rankHand cs =
  let suits =
        V.create $
        do s <- MV.replicate 4 0
           V.mapM_ (MV.modify s (+ 1) . _suit)
                   (suit $ V.unzip cs)
           pure s
      isFlush = V.maximum suits >= 5
      sFlush = Suit (V.maxIndex suits)
      csFlush = V.filter ((== sFlush) . suit) cs

      bv =
        BitVector (V.foldl' (\v r -> setBit v (_rank r))
                            0
                            (rank $ V.unzip cs))

      bvFlush =
        BitVector (V.foldl' (\v r -> setBit v (_rank r))
                            0
                            (rank $ V.unzip csFlush))

      bvStraight0 =
        if isFlush
           then bvFlush
           else bv
      bvStraight = bvStraight0 .|. (bvStraight0 `shift` (-13))  -- ace -> one

      bvStraightTest = bvStraight
                       .&. (bvStraight `shift` 1) .&. (bvStraight `shift` 2)
                       .&. (bvStraight `shift` 3) .&. (bvStraight `shift` 4)
      isStraight = bvStraightTest /= BitVector 0
      straightNum = -(countLeadingZeros bvStraightTest)

      ranks =
        V.create $
        do r <- MV.replicate 14 0
           V.mapM_ (MV.modify r (+ 1) . _rank)
                   (rank $ V.unzip cs)
           pure r

      pRes = V.ifoldl' (\p r c -> accRank p (Rank r) c) PNull ranks
      res = normalize pRes bv
  in case (isFlush, isStraight, res) of
    (True, True, _) -> StraightFlush straightNum
    (_, _, r@(Quads _ _)) -> r
    (_, _, r@(FullHouse _ _)) -> r
    (True, _, _) -> Flush bv
    (_, True, _) -> Straight straightNum
    (_, _, r) -> r

  where clearLast1 bv = bv `clearBit` countTrailingZeros bv
        clearLast2 = clearLast1 . clearLast1

        accRank :: Partial -> Rank -> Int -> Partial
        accRank res r c =
          case (res, c) of
            (_, 0) -> res

            (PNull, 1) -> PHighCard
            (PNull, 2) -> PPair r
            (PNull, 3) -> PTrips r
            (PNull, 4) -> PQuads r

            (_, 1) -> res

            (PHighCard, 2) -> PPair r
            (PHighCard, 3) -> PTrips r
            (PHighCard, 4) -> PQuads r

            (PPair p, 2) | p > r -> PTwoPair p r
                           | otherwise -> PTwoPair r p
            (PPair t, 3) -> PFullHouse r t
            (PPair _, 4) -> PQuads r

            (PTrips t, 2) -> PFullHouse t r
            (PTrips t, 3) | t > r -> PFullHouse t r
                          | otherwise -> PFullHouse r t
            (PTrips _, 4) -> PQuads r

            (PQuads _, _) -> res

            (PTwoPair p1 p2, 2) | r > p1 -> PTwoPair r p1
                                | r > p2 -> PTwoPair p1 r
                                | otherwise -> res
            (PTwoPair p1 _, 3) -> PFullHouse r p1

            (PFullHouse t p, 2) | p > r -> res
                                | otherwise -> PFullHouse t r

            _ -> error ("accRank: " ++ show (res, r, c))

        normalize :: Partial -> BitVector -> Result
        normalize res bv =
          case res of
            PNull -> error "cannot normalize null hand"

            PHighCard -> HighCard (clearLast2 bv)

            (PPair p) ->
              let bv' = bv `clearBit` _rank p
              in Pair p (clearLast2 bv')

            (PTwoPair p1 p2) ->
              let bv' = bv `clearBit` _rank p1 `clearBit` _rank p2
              in case popCount bv' of
                   2 -> TwoPair p1 p2 (clearLast1 bv')
                   _ -> TwoPair p1 p2 (clearLast2 bv')

            (PTrips t) ->
              let bv' = bv `clearBit` _rank t
              in Trips t (clearLast2 bv')

            (PFullHouse t p) -> FullHouse t p

            (PQuads q) ->
              let bv' = bv `clearBit` _rank q
              in case popCount bv' of
                   1 -> Quads q bv'
                   2 -> Quads q (clearLast1 bv')
                   _ -> Quads q (clearLast2 bv')


analyze :: (MonadState PokerState m)
        => Card -> Card -> Int -> Int -> m Double
analyze c1 c2 nOpps nTries =
  do res <- replicateM nTries trial
     pure (sum res / fromIntegral nTries)
  where trial =
          do pt <- get
             let (res,st') = runState inner (TrialState newDeck pt)
             put (st' ^. trial_poker)
             pure res
        inner =
          do shuffle
             draw c1 c2
             let hole = V.fromList [c1,c2]
             oppHoles <-
               replicateM nOpps
                          (deal 2)
             common <- deal 5
             let hands = map (V.++ common) (hole : oppHoles)
                 allRes@(res:_) = map rankHand hands
                 maxRes = maximum allRes
                 nWin = length (filter (== maxRes) allRes)
             pure (if res == maxRes
                      then recip (fromIntegral nWin)
                      else 0)

nTries = 1000

someFunc :: IO ()
someFunc =
  do seed <- createSystemRandom >>= asGenIO save
     putStrLn ("*** " ++ tshow nTries ++ " samples ***")
     putStrLn ""
     evalStateT (mapM_ doSet [0..8]) (PokerState seed)
     putStrLn ""

  where doSet i =
          do doLine i "AAo" (ace, club)   (ace, heart)
             doLine i "KKo" (king, club)  (king, heart)
             doLine i "QQo" (queen, club) (queen, heart)
             doLine i "JJo" (jack, club)  (jack, heart)
             doLine i "TTo" (ten, club)   (ten, heart)
             doLine i "AKs" (ace, club)   (king, club)
             doLine i "AKo" (ace, club)   (king, heart)
             doLine i "22o" (two, club)   (two, heart)
             doLine i "72o" (seven, club) (two, heart)
             putStrLn ""

        doLine i (l :: Text) c1 c2 =
          do r <- analyze c1 c2 (i + 1) nTries
             F.print "({} {}) {} \t" (l
                                     ,i + 1
                                     ,F.left 5 ' ' $ F.fixed 2 (100 * r))
