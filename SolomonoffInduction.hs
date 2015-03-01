{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
module SolomonoffInduction (solomonoffInduction, aixi) where
import Prelude hiding (Real, interact)
import Control.Applicative
import System.Random (randomRIO)

-- Helper functions
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM p t e = p >>= \x -> if x then t else e

-- An infinite list datatype.
-- We could just use lists, but it's nice to avoid the [] cases.
-- Streams of nested intervals will be used to represent real numbers.
data Stream a = a :! Stream a

instance Functor Stream where
	fmap f (x :! xs) = f x :! fmap f xs

instance Applicative Stream where
	pure x = x :! pure x
	(f :! fs) <*> (x :! xs) = f x :! (fs <*> xs)

makeStream :: (a -> a) -> a -> Stream a
makeStream f x = x :! makeStream f (f x)

streamGet :: Integer -> Stream a -> a
streamGet 0 (x:!_) = x
streamGet n (_:!xs) = streamGet (n-1) xs

streamTake :: Integer -> Stream a -> [a]
streamTake 0 _ = []
streamTake n (x:!xs) = x : streamTake (n-1) xs

streamZipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
streamZipWith f (x :! xs) (y :! ys) = f x y :! streamZipWith f xs ys

streamZip :: Stream a -> Stream b -> Stream (a, b)
streamZip = streamZipWith (,)

-- A bit datatype.
-- We could just use Bool, but it's nice to leverage the type system where possible.
data Bit = Zero | One deriving (Eq, Ord, Read, Show, Enum)
fromBool :: Bool -> Bit
fromBool True = One
fromBool False = Zero

-- A Machine datatype.
-- This will be used to encode probabilistic oracle machines.
-- Assume any machine can be encoded as an integer.
newtype Machine = M Integer deriving (Eq, Read, Show)

-- This will be used to define a simplicity prior.
-- We should be careful to pick an encoding of machines such that the sum of
-- 2^(- len m) for all m sums to 1. Right now we won't worry too much about that.
len :: Machine -> Integer
len (M i) = ceiling (logBase 2 (fromIntegral i) :: Double)

-- TODO: this violates the condition that sum [2^(- len m) | m <-
-- allMachines] == 1 assumption.
allMachines :: Stream Machine
allMachines = M <$> makeStream (+1) 0

-- Probabilistic oracle machines.
-- Remember, these are Turing machines that can flip coins and call oracles.
-- We will consider oracle than answer questions of the form
-- "Is the probability that M(bits) == 1 > p?", where M is a machine, bits is
-- a finite bitstring used as input, and p is a rational probability,

-- It may be somewhat difficult (read: uncomputable) to implement a reflective
-- oracle, but you can implement other "wrong" oracles if you want to test the
-- code, as seen below.
class OracleMachine m where
	oracle :: Machine -> [Bit] -> Rational -> m Bit

newtype OptimisticOracle a = OO a
instance OracleMachine OptimisticOracle where
	oracle _ _ _ = OO One

newtype PessimisticOracle a = PO a
instance OracleMachine PessimisticOracle where
	oracle _ _ _ = PO Zero

class ProbabilisticMachine m where
	tossCoin :: m Bit

-- The IO monad can implement the probabilistic part of POMs.
instance ProbabilisticMachine IO where
	tossCoin = fromBool <$> randomRIO (False, True)

-- A probabilistic oracle machine is a monad that lets you toss coins and call oracles.
type POM m = (Functor m, Applicative m, Monad m, OracleMachine m, ProbabilisticMachine m)

-- Reals will be represented by a series ofnested intervals.
type Interval = (Rational, Rational)
compareInterval :: Interval -> Interval -> Maybe Ordering
compareInterval (a, b) (c, d)
	| b > c = Just GT
	| a < d = Just LT
	| otherwise = Nothing

-- Actually, just kidding: reals are represented by a process (read: Monad)
-- which generates successive nested intervals.
-- Well, because this is haskell, we don't actually require that the intervals
-- be nested. Everything will blow up if you generate a "real" with expanding
-- intervals. So don't do that.
type Real m = Stream (m Interval)

makeReal :: Applicative m => Rational -> Real m
makeReal r = pure (r, r) :! makeReal r

zeroR :: Applicative m => Real m
zeroR = makeReal 0

oneR :: Applicative m => Real m
oneR = makeReal 1

liftR2 :: (Monad m, Applicative m) =>
	(Rational -> Rational -> Rational) -> Real m -> Real m -> Real m
liftR2 op (x:!xs) (y:!ys) = newInterval :! liftR2 op xs ys where
	newInterval = do
		(a, b) <- x
		(c, d) <- y
		let (e, f) = (op a c, op b d)
		return (max e f, min e f)

liftR1 :: (Monad m, Applicative m) => (Rational -> Rational) -> Real m -> Real m
liftR1 op (x:!xs) = newInterval :! liftR1 op xs where
	newInterval = do
		(a, b) <- x
		let (c, d) = (op a, op b)
		return (max c d, min c d)

realProduct :: (Monad m, Applicative m) => [Real m] -> Real m
realProduct = foldr realMul oneR

oneMinus :: (Monad m, Applicative m) => Real m -> Real m
oneMinus = liftR1 (1-)

-- Drops intervals that have 0 as a lower bound.
-- This makes division work. (Without this, division would fail on reals that
-- have zero as a lower-bound at some point, even if they eventually move away
-- from that lower bound.)
-- However, this function loops forever if the real is zero.
dropZeroIntervals :: Monad m => Real m -> m (Real m)
dropZeroIntervals r@(x:!xs) = do
	(_, lo) <- x
	if lo == 0 then dropZeroIntervals xs else return r

realDiv :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realDiv = liftR2 (/)

realAdd :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realAdd = liftR2 (+)

realMul :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realMul = liftR2 (*)

compareR :: Monad m => Real m -> Real m -> m Ordering
compareR (x:!xs) (y:!ys) = do
	bx <- x
	by <- y
	case compareInterval bx by of
		Just LT -> return LT
		Just GT -> return GT
		_ -> compareR xs ys

refineR :: (Monad m, ProbabilisticMachine m) => Interval -> m (Real m)
refineR (hi, lo) = do
	bit <- tossCoin
	let med = (hi + lo) / 2
	let bounds = if bit == One then (hi, med) else (med, lo)
	rest <- refineR bounds
	return $ return bounds :! rest

-- Probabilistic oracle machine functions for manipulating reals:

-- Generates a real using a sequence of coin flips.
-- Each coin toss halves the interval. On a 1, we keep the top half, on a 0, we
-- keep the bottom half.
genRandomReal :: (Monad m, ProbabilisticMachine m) => m (Real m)
genRandomReal = refineR (1, 0)

-- This allows probabilistic oracle machines to create a branch that has some
-- real probability of going either way.
-- That is, flipR (real 0.8)
flipR :: (Monad m, ProbabilisticMachine m) => Real m -> m Bit
flipR r = do
	rand <- genRandomReal
	comp <- compareR rand r
	case comp of
		LT -> return Zero
		GT -> return One
		EQ -> error "A real generated from coin tosses can never equal another real."

-- Finds the probability that a machine, run on a given input, outputs a given bit.
-- Basically does binary refinement using the oracle.
-- Generates a series of nested intervals.
getProb :: POM m => Machine -> [Bit] -> Bit -> Real m
getProb m bits bit = if bit == One then prob1 else oneMinus prob1 where
	prob1 = makeStream restrictInterval (pure (1, 0))
	restrictInterval pbounds = do
		(hi, lo) <- pbounds
		let mid = (hi + lo) / 2
		ans <- oracle m bits mid
		return $ if ans == One then (hi, mid) else (mid, lo)

-- Finds the probability that a machine would have output a given bit sequence.
getStringProb :: POM m => Machine -> [Bit] -> Real m
getStringProb m bs = realProduct [getProb m bs' b' | (bs', b') <- observations]
	where observations = [(take n bs, bs !! n) | n <- [0 .. length bs - 1]]

-- Given a measure of how likely each machine is to accept x (in some abstract
-- fashion) and x, this function generates the generic probability (over all
-- machines) of ``accepting x."
-- Translation: this can be used to figure out the probability of a given
-- string being generated *in general*.
pOverMachines :: POM m => (Machine -> x -> Real m) -> x -> Real m
pOverMachines f x = nthApprox <$> makeStream (+1) 0 where
	nthApprox n = do
		let ms = streamTake n allMachines
		let measures = [2 ^ negate (len m) | m <- ms]
		bounds <- sequence [streamGet n $ f m x | m <- ms]
		let upper = sum [m * hi | (m, (hi, _)) <- zip measures bounds]
		let lower = sum [m * lo | (m, (_, lo)) <- zip measures bounds]
		pure (1 - sum measures + upper, lower)

-- Finally, the definition of Solomonoff induction.
-- Basically, it selects a machine according to both its simplicity-weighted
-- probability and its probability of generating the bits seen so far, and then
-- acts as that machine acts.
-- Thus, this machine defines a probability distribution over bits that
-- predicts the behavior of each machine in proportion to its posterior
-- probability.
solomonoffInduction :: POM m => [Bit] -> m Bit
solomonoffInduction bs = pickM >>= \m -> flipR (getProb m bs One) where
	pickM = do
		normalizationFactor <- dropZeroIntervals $ pOverMachines getStringProb bs
		rand <- genRandomReal
		let likelihood m = getStringProb m bs `realDiv` normalizationFactor
		let machineProb m = liftR1 (2 ^ negate (len m) *) (likelihood m)
		let probs = machineProb <$> allMachines
		let cutoffs = go zeroR probs where
			go k (x:!xs) = let k' = k `realAdd` x in k' :! go k' xs
		let decisions = (fmap (== LT) . compareR rand) <$> cutoffs
		let findMachine ((m, isSelected):!xs) = ifM isSelected (pure m) (findMachine xs)
		findMachine $ streamZip allMachines decisions


type Action = [Bit]
type Observation = [Bit]

rewardFrom :: Observation -> Rational
rewardFrom = undefined

-- Actions and Observations must use prefix-free encodings.
-- (These should return true if any prefix of Bit is an action;
-- this is not precisely indicated by the name.)
-- Except bits and observations are encoded from the back.
-- So I guess it's a postfix-free encoding?
-- Just say we build on the left and that it must be prefix free.
isAction :: [Bit] -> Bool
isAction = undefined

isObservation :: [Bit] -> Bool
isObservation = undefined

type History = [(Observation, Action)]
data AgentHistory = AgentHistory [Bit] Observation History deriving (Eq, Show)
data EnvHistory = EnvHistory [Bit] (Maybe Machine) History deriving (Eq, Show)

-- We'd like to add constraints saying that the bitstrings produced will always
-- form an observation/action, but for now we just assume that this is the case.
type Environment m = EnvHistory -> m (Machine, Bit)
type Agent m = AgentHistory -> m Bit

gamma :: Rational
gamma = undefined -- TODO: Consider parameterizing this.

maxDiscountedReward :: Integer -> Rational
maxDiscountedReward = undefined -- TODO: Find the closed form equation for \sum_{t=n}^{\infty} \gamma^t

discount :: Integer -> Rational
discount n = gamma ^ n

getEnvProb :: POM m => Machine -> History -> Observation -> Real m
getEnvProb m hist o = realProduct [getProb m bs b | (bs, b) <- envActs] where
	envActs :: [([Bit], Bit)]
	envActs = concatMap (uncurry acts) ohs
	rh :: History
	rh = reverse hist
	ohs :: [(History, Observation)]
	ohs = [(take n rh, fst $ rh !! n) | n <- [0 .. length rh - 1]] ++ [(rh, o)]
	acts :: History -> Observation -> [([Bit], Bit)]
	acts h ob = addOActs ob (histStr h)
	addOActs :: Observation -> [Bit] -> [([Bit], Bit)]
	addOActs ob bs = [(bs ++ (take n ob), ob !! n) | n <- [0 .. length ob - 1]]

getHistProb :: POM m => Machine -> History -> Real m
getHistProb m h = realProduct [getEnvProb m h' o | (h', o) <- observations]
	where observations = [(take n h, fst $ h !! n) | n <- [0 .. length h - 1]]

histStr :: History -> [Bit]
histStr hist = concat [o ++ a | (o, a) <- reverse hist]

-- Unexpressed guarantee: Always picks the machine in EnvHistory if there was one.
envInductor :: POM m => EnvHistory -> m (Machine, Bit)
envInductor (EnvHistory bits mm hist) = getM >>= \m -> (m,) <$> predict m where
	getM = maybe pick return mm
	-- Assertion: if we're calling pick, bits are nil.
	pick = do
		normalizationFactor <- dropZeroIntervals $ pOverMachines getHistProb hist
		rand <- genRandomReal
		let likelihood m = getHistProb m hist `realDiv` normalizationFactor
		let machineProb m = liftR1 (2 ^ negate (len m) *) (likelihood m)
		let probs = machineProb <$> allMachines
		let cutoffs = go zeroR probs where
			go k (x:!xs) = let k' = k `realAdd` x in k' :! go k' xs
		let decisions = (fmap (== LT) . compareR rand) <$> cutoffs
		let findMachine ((m, isSelected):!xs) = ifM isSelected (pure m) (findMachine xs)
		findMachine $ streamZip allMachines decisions
	predict m = flipR (getProb m (histStr hist ++ bits) One)

interactE :: POM m => Agent m -> Environment m -> EnvHistory
	-> m (Stream (Observation, Action))
interactE agent env eHist@(EnvHistory bits _ hist)
	| isObservation bits = interactA agent env (AgentHistory [] bits hist)
	| otherwise = do
		(m, bit) <- env eHist
		interactE agent env (EnvHistory (bit:bits) (Just m) hist)

interactA :: POM m => Agent m -> Environment m -> AgentHistory
	-> m (Stream (Observation, Action))
interactA agent env aHist@(AgentHistory bits o hist)
	| isAction bits = do
		let next = (o, bits)
		rest <- interactE agent env (EnvHistory [] Nothing (next:hist))
		return (next:!rest)
	| otherwise = do
		bit <- agent aHist
		interactA agent env (AgentHistory (bit:bits) o hist)

interact :: POM m => Agent m -> Environment m -> AgentHistory
	-> m (Stream (Observation, Action))
interact agent env aHist@(AgentHistory bits o hist)
	| isAction bits = interactE agent env (EnvHistory [] Nothing ((o, bits):hist))
	| otherwise = interactA agent env aHist

reward :: POM m => Agent m -> Environment m -> AgentHistory -> (Real m)
reward agent env hist = approx <$> makeStream (+1) (0 :: Integer) where
	approx n = do
		future <- interact agent env hist
		let relevant = streamTake n future
		return (rewardsIn n relevant + maxDiscountedReward n, rewardsIn n relevant)
	rewardsIn :: Integer -> History -> Rational
	rewardsIn _ [] = 0
	rewardsIn n ((o, _):rest) = ((discount n) * (rewardFrom o)) + rewardsIn (n+1) rest

-- f and g had better be in [0, 1]! TODO: Explain this better.
-- If f in [0, 1] and g in [0, 1] then this is a number in [0, 1] that is >1/2
-- if f is larger, and less than 1/2 if g is larger.
bias :: POM m => (Real m) -> (Real m) -> (Real m)
bias x y = (liftR1 (/ 2) (liftR1 (+1) (x `realAdd` y)))

-- Finds a machine that outputs this real number.
coinflipM :: (Real m) -> Machine
coinflipM = undefined

aixiTemplate :: POM m => Agent m -> Environment m -> AgentHistory -> m Bit
aixiTemplate agent env (AgentHistory bits o hist)
	| isAction bits = error "Agent called with malformed history."
	| otherwise = do
		let r x = reward agent env $ AgentHistory (bits ++ [x]) o hist
		oracle (coinflipM $ bias (r One) (r Zero)) [] (1/2)

aixi :: POM m => Agent m
aixi = aixiTemplate aixi envInductor
