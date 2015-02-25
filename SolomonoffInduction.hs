module SolomonoffInduction where
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import Prelude hiding (Real)
import Control.Applicative
import System.Random (randomRIO)

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM p t e = p >>= \x -> if x then t else e

data Bit = Zero | One deriving (Eq, Ord, Show, Enum)

toBool :: Bit -> Bool
toBool One = True
toBool Zero = False

fromBool :: Bool -> Bit
fromBool True = One
fromBool False = Zero

newtype Machine = M Integer

len :: Machine -> Integer
len (M i) = ceiling (logBase 2 (fromIntegral i) :: Double)

allMachines :: Stream Machine
allMachines = M <$> makeStream (+1) 0

machineEncodingReal :: POM m => Real m -> Machine
machineEncodingReal = undefined

data Stream a = a :! Stream a
instance Functor Stream where
	fmap f (x :! xs) = f x :! fmap f xs
instance Applicative Stream where
	pure x = x :! pure x
	(f :! fs) <*> (x :! xs) = f x :! (fs <*> xs)

makeStream :: (a -> a) -> a -> Stream a
makeStream f x = x :! makeStream f (f x)

streamGet :: Int -> Stream a -> a
streamGet 0 (x:!_) = x
streamGet n (_:!xs) = streamGet (n-1) xs

streamTake :: Int -> Stream a -> [a]
streamTake 0 _ = []
streamTake n (x:!xs) = x : streamTake (n-1) xs

streamFind :: (a -> Bool) -> Stream a -> a
streamFind f (x:!xs) = if f x then x else streamFind f xs

streamZipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
streamZipWith f (x :! xs) (y :! ys) = f x y :! streamZipWith f xs ys

streamZip :: Stream a -> Stream b -> Stream (a, b)
streamZip = streamZipWith (,)

first :: Stream (Maybe a) -> a
first (Nothing:!xs) = first xs
first (Just x:!_) = x

type Bounds = (Rational, Rational)

compareBounds :: Bounds -> Bounds -> Maybe Ordering
compareBounds (a, b) (c, d)
	| b > c = Just GT
	| a < d = Just LT
	| otherwise = Nothing

class OracleMachine m where
	oracle :: Machine -> [Bit] -> Rational -> m Bit

class ProbabilisticMachine m where
	tossCoin :: m Bit

instance ProbabilisticMachine IO where
	tossCoin = fromBool <$> randomRIO (False, True)

type POM m = (Functor m, Applicative m, Monad m, OracleMachine m, ProbabilisticMachine m)

genCoinSequence :: POM m => Stream (m Bit)
genCoinSequence = tossCoin :! genCoinSequence

type Real m = Stream (m Bounds)

liftR2 :: POM m => (Rational -> Rational -> Rational) -> Real m -> Real m -> Real m
liftR2 op (x:!xs) (y:!ys) = newBounds :! liftR2 op xs ys where
	newBounds = do
		(a, b) <- x
		(c, d) <- y
		let (e, f) = (op a c, op b d)
		pure (max e f, min e f)

liftR1 :: POM m => (Rational -> Rational) -> Real m -> Real m
liftR1 op (x:!xs) = newBounds :! liftR1 op xs where
	newBounds = do
		(a, b) <- x
		let (c, d) = (op a, op b)
		pure (max c d, min c d)

zeroR :: POM m => Real m
zeroR = pure (0, 0) :! zeroR

oneR :: POM m => Real m
oneR = pure (1, 1) :! oneR

------------- Begin.

refineR :: POM m => Bounds -> m (Real m)
refineR (hi, lo) = do
	bit <- tossCoin
	let med = (hi + lo) / 2
	let bounds = if bit == One then (hi, med) else (med, lo)
	rest <- refineR bounds
	pure $ pure bounds :! rest

genRandomReal :: POM m => m (Real m)
genRandomReal = refineR (1, 0)

flipR :: POM m => Real m -> m Bit
flipR r = do
	rand <- genRandomReal
	comp <- compareR rand r
	case comp of
		LT -> pure Zero
		GT -> pure One
		EQ -> error "A real generated from coin tosses can never equal another real."

compareR :: POM m => Real m -> Real m -> m Ordering
compareR (x:!xs) (y:!ys) = do
	bx <- x
	by <- y
	case compareBounds bx by of
		Just LT -> pure LT
		Just GT -> pure GT
		_ -> compareR xs ys

restrictBounds :: POM m => Machine -> [Bit] -> m (Rational, Rational) -> m (Rational, Rational)
restrictBounds m bs pbs = do
	(hi, lo) <- pbs
	let mid = (hi + lo) / 2
	ans <- oracle m bs mid
	pure $ if ans == One then (hi, mid) else (mid, lo)

getProb :: POM m => Machine -> [Bit] -> Bit -> Real m
getProb m bs b
	| b == One = prob1
	| otherwise = oneMinus prob1
	where prob1 = makeStream (restrictBounds m bs) (pure (1, 0))

getStringProb :: POM m => Machine -> [Bit] -> Real m
getStringProb m bs = realProduct [getProb m bs' b' | (bs', b') <- observations bs]
	where observations xs = [(take n xs, xs !! n) | n <- [0 .. length xs - 1]]

realProduct :: POM m => [Real m] -> Real m
realProduct = foldr (liftR2 (*)) oneR

realSum :: POM m => [Real m] -> Real m
realSum = foldr (liftR2 (+)) zeroR

oneMinus :: POM m => Real m -> Real m
oneMinus = liftR1 (1-)

dropZeroBounds :: POM m => Real m -> m (Real m)
dropZeroBounds r@(x:!xs) = do
	(_, lo) <- x
	if lo == 0 then dropZeroBounds xs else pure r

realDiv :: POM m => Real m -> Real m -> Real m
realDiv = liftR2 (/)

pOverMachines :: POM m => (Machine -> x -> Real m) -> x -> Real m
pOverMachines f x = nthApprox <$> makeStream (+1) 0 where
	nthApprox n = do
		let ms = streamTake n allMachines
		let measures = [2 ^ negate (len m) | m <- ms]
		bounds <- sequence [streamGet n $ f m x | m <- ms]
		let upper = sum [m * hi | (m, (hi, _)) <- zip measures bounds]
		let lower = sum [m * lo | (m, (_, lo)) <- zip measures bounds]
		pure (1 - sum measures + upper, lower)

solomonoffInduction :: POM m => [Bit] -> m Bit
solomonoffInduction bs = pickM >>= \m -> flipR (getProb m bs One) where
	pickM = do
		normalizationFactor <- dropZeroBounds $ pOverMachines getStringProb bs
		rand <- genRandomReal
		let likelihood m = getStringProb m bs `realDiv` normalizationFactor
		let machineProb m = liftR1 (2 ^ negate (len m) *) (likelihood m)
		let probs = machineProb <$> allMachines
		let cutoffs = go zeroR probs where
			go k (x:!xs) = let k' = liftR2 (+) k x in k' :! go k' xs
		let decisions = (fmap (== LT) . compareR rand) <$> cutoffs
		let findMachine ((m, isSelected):!xs) = ifM isSelected (pure m) (findMachine xs)
		findMachine $ streamZip allMachines decisions

type Action = Bit
newtype Observation = O
	{ sense :: Int
	, reward :: Int
	} deriving (Eq, Ord, Enum, Num, Read, Show)
obsToBits :: Observation -> [Bit]
obsToBit = undefined

type History = (Observation, [(Observation, Action)])

type Environment = [(Observation, Action)] -> Observation
castToEnv :: Machine -> Environment
castToEnv = undefined

type Agent = History -> Action

getEnvProb :: POM m => Machine -> [(Observation, Action)] -> Observation -> Real m
getEnvProb m h o = undefined

getHistProb :: POM m => Machine -> History -> Real m
getHistProb m h = realProduct [getEnvProb m h' o | (h', o) <- observations h]
	where observations xs = [(take n xs, xs !! n) | n <- [0 .. length xs - 1]]
