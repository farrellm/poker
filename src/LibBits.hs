{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, ScopedTypeVariables #-}
{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module LibBits  where

import BasicPrelude

import Control.Monad.ST
import Control.Monad.State.Strict
       (MonadState, get, put, evalStateT, runState)
import Data.Bits
import qualified Data.Text.Format as F
import qualified Data.Vector.Unboxed as V
import Lens.Micro.Platform
import System.Random.MWC
import System.Random.MWC.Distributions

import qualified BitVector as BV

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

type Card = (Int, Int)

fromCard :: (Rank, Suit) -> (Int, Int)
fromCard (r, s) = (_rank r, _suit s)

toCard :: (Int, Int) -> (Rank, Suit)
toCard (r, s) = (Rank r, Suit s)

rank :: (a, b) -> a
rank = fst

suit :: (a, b) -> b
suit = snd

rankMajorIndex :: Card -> Int
rankMajorIndex (r, s) = r * 4 + s

suitMajorIndex :: Card -> Int
suitMajorIndex (r, s) = s * 16 + r

data Result
  = HighCard (BV.Elem 16)
  | Pair Rank (BV.Elem 16)
  | TwoPair Rank Rank (BV.Elem 16)
  | Trips Rank (BV.Elem 16)
  | Straight Int
  | Flush (BV.Elem 16)
  | FullHouse Rank Rank
  | Quads Rank (BV.Elem 16)
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
  pure (_rank r, _suit s)

shuffle :: (MonadState TrialState m) => m ()
shuffle =
  do seed <- use (trial_poker . poker_seed)
     d <- use trial_deck
     let (seed', d') = runST $ do
           gen <- restore seed
           d' <- uniformShuffle d gen
           seed' <- save gen
           pure (seed', d')
     trial_deck .= d'
     (trial_poker . poker_seed) .= seed'

draw :: (MonadState TrialState m) => Card -> Card -> m ()
draw c1 c2 =
  trial_deck %= V.filter (\c -> c /= c1 && c /= c2)

deal :: (MonadState TrialState m) => Int -> m Deck
deal n = do
  (h, d) <- V.splitAt n <$> use trial_deck
  trial_deck .= d
  pure h

rankHand :: Deck -> Result
rankHand cs =
  let suitMajor = mkSuitMajor cs
      flush = isFlush suitMajor

      rankFlags = orSuits suitMajor
      stRankFlags =
        case flush of
          Just (Suit s) ->
            (BV.reshape suitMajor :: BV.BitVector 16 4) BV.! s
          Nothing -> rankFlags

      straight = isStraight stRankFlags

      rankMajor = mkRankMajor cs
      rankCount = sumRanks rankMajor

      quads = isQuads rankCount
      trips = isTrips rankCount
      pairs = isPairs rankCount

  in case (flush, straight, quads, trips, pairs) of
    (Just _, Just straightNum, _, _, _) ->
      StraightFlush straightNum
    (_, _, Just q, _, _) ->
      Quads (Rank q) $
      clearLeastTo 1 (clearBit rankFlags q)
    (_, _, _, Just t, p:_) ->
      FullHouse (Rank t) (Rank p)
    (Just _, _, _, _, _) ->
      Flush (clearLeastTo 5 stRankFlags)
    (_, Just straightNum, _, _, _) ->
      Straight straightNum
    (_, _, _, Just t, _) ->
      Trips (Rank t) (clearLeastTo 2 (clearBit rankFlags t))
    (_, _, _, _, p1:p2:_) ->
      TwoPair (Rank p1) (Rank p2)  $
      clearLeastTo 1 (clearBit (clearBit rankFlags p2) p1)
    (_, _, _, _, [p]) ->
      Pair (Rank p) (clearLeastTo 3 (clearBit rankFlags p))
    _ ->
      HighCard (clearLeastTo 5 rankFlags)

  where isFlush suitMajor =
          let suitMask :: BV.BitVector 64 1 =
                BV.reshape $
                (BV.fromList (replicate 4 1) :: BV.BitVector 16 4)
              goS i = (suitMajor .&. (suitMask `shift` i)) `shift` (-i)
              sv = sum $ map goS [0..13]
              ss = BV.toList (BV.reshape sv :: BV.BitVector 16 4)

              (flCount, flSuit) = maximum (zip ss $ map Suit [0..])
          in if flCount >= 5
             then Just flSuit
             else Nothing

        mkSuitMajor cs =
          let go v i = v `setBit` suitMajorIndex (cs V.! i)
          in foldl' go (zeroBits :: BV.BitVector 64 1) [0..6]

        mkRankMajor cs =
          let go v i = v `setBit` rankMajorIndex (cs V.! i)
          in foldl' go (zeroBits :: BV.BitVector 64 1) [0..6]

        orSuits v =
          (BV.reshape $
           ((v `shift` (-16 * _suit club)) .|.
            (v `shift` (-16 * _suit diamond)) .|.
            (v `shift` (-16 * _suit heart)) .|.
            (v `shift` (-16 * _suit spade))
           ) :: BV.BitVector 16 4) BV.! 0

        sumRanks rankMajor =
          let rankMask =
                BV.reshape $
                (BV.fromList (replicate 16 1) :: BV.BitVector 4 16)
              go s i = ((rankMajor .&. (rankMask `shift` i))
                       `shift` (-i)) + s
          in foldl' go zeroBits [0..3]

        isStraight r0 =
          let r1 = r0 .|. (r0 `shift` (-13))
              rs = r1
                   .&. (r1 `shift` 1)
                   .&. (r1 `shift` 2)
                   .&. (r1 `shift` 3)
                   .&. (r1 `shift` 4)
          in if rs == zeroBits
             then Nothing
             else Just (- countLeadingZeros rs)

        isQuads rc =
          let quadMask :: BV.BitVector 64 1 =
                BV.reshape
                (BV.fromList (replicate 16 4) :: BV.BitVector 4 16)
              q = rc .&. quadMask
              s = (64 - countLeadingZeros q) `div` 4
          in if q == zeroBits
             then Nothing
             else Just s

        isTrips rc =
          let tripMask :: BV.BitVector 64 1 =
                BV.reshape $
                (BV.fromList (replicate 16 1) :: BV.BitVector 4 16)
              q = (rc `shift` (-1)) .&. rc .&. tripMask
              s = (64 - countLeadingZeros q) `div` 4
          in if q == zeroBits
             then Nothing
             else Just s

        isPairs rc =
          let pairMask :: BV.BitVector 64 1 =
                BV.reshape $
                (BV.fromList (replicate 16 2) :: BV.BitVector 4 16)
              q = complement (rc `shift` 1) .&. rc .&. pairMask
              l = countLeadingZeros q
              b = 64 - l - 1
              s = (64 - l) `div` 4
              t = (64 - countLeadingZeros (clearBit q b)) `div` 4
          in if q == zeroBits
             then []
             else if t == 0
                  then [s]
                  else [s, t]

        clearLeast :: BV.Elem 16 -> BV.Elem 16
        clearLeast bv = bv `clearBit` countTrailingZeros bv
        clearLeastTo n bv =
          case popCount bv - n of
            0 -> bv
            1 -> clearLeast bv
            2 -> clearLeast $ clearLeast bv
            m | m > 0 -> clearLeastTo (n - 1) (clearLeast bv)
            _ -> error ("cannot clear least to " ++
                        show n ++ " from bitset with " ++ show (popCount bv))


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
             let hole = V.fromList [c1, c2]
             oppHoles <- replicateM nOpps (deal 2)
             common <- deal 5

             let hands = map (<> common) (hole : oppHoles)
                 allRes@(res:_) = map rankHand hands
                 -- allRes@(res:_) = [0]

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
     evalStateT (mapM_ doSet [1..8]) (PokerState seed)
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
          do r <- analyze (fromCard c1) (fromCard c2) i nTries
             F.print "({} {}) {} \t" (l
                                     ,i
                                     ,F.left 5 ' ' $ F.fixed 2 (100 * r))
