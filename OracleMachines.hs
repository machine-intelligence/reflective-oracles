{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
module OracleMachines where
import Prelude hiding (Real, interact)
import Control.Arrow (first, second)
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

streamFindM :: Monad m => (a -> m Bool) -> Stream a -> m a
streamFindM predM (x:!xs) = ifM (predM x) (return x) (streamFindM predM xs)

streamConcat :: [a] -> Stream a -> Stream a
streamConcat [] xs = xs
streamConcat (x:xs) ys = x :! streamConcat xs ys

naturals :: Stream Integer
naturals = makeStream succ 0

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

-- Probabilistic orcale machines returning bits can be encoded as machines.
-- In theory. You have to provide your own encoding, though.
encodeB :: POM m => m Bit -> Machine
encodeB = undefined

-- This will be used to define a simplicity prior.
-- We should be careful to pick an encoding of machines such that the sum of
-- 2^(- len m) for all m sums to 1. Right now we won't worry too much about that.
len :: Machine -> Integer
len (M i) = ceiling (logBase 2 (fromIntegral i) :: Double)

-- The prior of a given machine according to a simplicity prior (with respect to `len`).
prior :: Machine -> Rational
prior m = 2 ^ negate (len m)

-- TODO: this violates the condition that sum [2^(- len m) | m <-
-- allMachines] == 1 assumption.
allMachines :: Stream Machine
allMachines = M <$> naturals

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

realAdd :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realAdd = liftR2 (+)

realSub :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realSub = liftR2 (-)

realMul :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realMul = liftR2 (*)

realDiv :: (Monad m, Applicative m) => Real m -> Real m -> Real m
realDiv = liftR2 (/)

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
getProb :: POM m => Bit -> [Bit] -> Machine -> Real m
getProb bit bits m = if bit == One then prob1 else oneMinus prob1 where
	prob1 = makeStream restrictInterval (pure (1, 0))
	restrictInterval pbounds = do
		(hi, lo) <- pbounds
		let mid = (hi + lo) / 2
		ans <- oracle m bits mid
		return $ if ans == One then (hi, mid) else (mid, lo)

-- Finds the probability that a machine would have output a given bit sequence.
getStringProb :: POM m => [Bit] -> Machine -> Real m
getStringProb bits m = realProduct [getProb bit prev m | (prev, bit) <- events bits]

-- Given a measure of how likely each machine is to accept x (in some abstract
-- fashion) and x, this function generates the generic probability (over all
-- machines) of ``accepting x."
-- Translation: this can be used to figure out the probability of a given
-- string being generated *in general*.
pOverMachines :: POM m => (Machine -> Real m) -> Real m
pOverMachines bias = nthApprox <$> naturals where
	nthApprox n = do
		let machines = streamTake n allMachines
		bounds <- sequence [streamGet n $ bias m | m <- machines]
		let upper = sum [prior m * hi | (m, (hi, _)) <- zip machines bounds]
		let lower = sum [prior m * lo | (m, (_, lo)) <- zip machines bounds]
		pure (1 - sum (prior <$> machines) + upper, lower)

-- Samples machines according to a simplicity prior biased by some measure on machines.
-- The biaser should return a probability in [0, 1] for each machine.
sampleMachine :: POM m => (Machine -> Real m) -> m Machine
sampleMachine bias = do
	normalizationFactor <- dropZeroIntervals $ pOverMachines bias
	rand <- genRandomReal
	let likelihood m = liftR1 (prior m *) (bias m `realDiv` normalizationFactor)
	let cascade prev (x:!xs) = let next = prev `realAdd` x in next :! cascade next xs
	let cutoffs = cascade zeroR (likelihood <$> allMachines)
	let isLessThanRand = fmap (== LT) . compareR rand
	let decisionStream = streamZip allMachines (isLessThanRand <$> cutoffs)
	fst <$> streamFindM snd decisionStream

-- Finally, the definition of Solomonoff induction.
-- Basically, it selects a machine according to both its simplicity-weighted
-- probability and its probability of generating the bits seen so far, and then
-- acts as that machine acts.
-- Thus, this machine defines a probability distribution over bits that
-- predicts the behavior of each machine in proportion to its posterior
-- probability given the bits seen so far.
solomonoffInduction :: POM m => [Bit] -> m Bit
solomonoffInduction bs = flipR . getProb One bs =<< sampleMachine (getStringProb bs)

-- Actions and Observations are bitstrings.
-- You must use a prefix-free encoding.
-- Here we represent them as lists *built from the left*, which means that they
-- must be prefix-free when *read from the right*.
type Action = [Bit]
type Observation = [Bit]

-- You must define your action/observation encodings yourself.
isAction, isObservation :: [Bit] -> Bool
isAction = undefined
isObservation = undefined

-- After defining your observation format, you must also define the encoding of
-- rewards within observations.
rewardFrom :: Observation -> Rational
rewardFrom = undefined

-- The history generated will be a series of OA pairs.
-- Note that history is generated from the left, so the oldest pair is at the
-- end of the list.
type OA = (Observation, Action)
type History = [OA]

-- Agents are run on a OAOA..OAO string (note the trailing O), and also the
-- environment will be run until it finishes outputting an entire observation
-- (bit by bit) before control is switched to the agent (which outputs an
-- action bit by bit, etc.). We track those states with these two datatypes.
data AgentHistory = AgentHistory
	{ partialA :: [Bit]
	, currentO :: Observation
	, prevHistA :: History
	} deriving (Eq, Show)

-- Constraint: The first field should be [] iff the second field is Nothing.
data EnvHistory = EnvHistory
	{ partialO :: [Bit]
	, currentM :: Maybe Machine
	, prevHistE :: History
	} deriving (Eq, Show)

type Agent m = AgentHistory -> m Bit
-- An environment is a distribution over machines. Basically, the environment
-- starts by sampling a machine from some distribution and acting like that
-- machine, and it continues acting like that machine (rather than sampling
-- a new one) until it finishes outputting an entire (multibit) observation.
-- Constraint: If the second field in the EnvHistory is (Just machine) then
-- that machine should be lifted into the first position of the tuple. (The
-- envirnoment only picks new machines when it is between whole observations.)
type Environment m = EnvHistory -> m (Machine, Bit)

-- TODO: Consider parameterizing this.
discountFactor :: Rational
discountFactor = undefined

-- TODO: What's the closed form equation for \sum_{t=n}^{\infty} \gamma^t, again?
maxDiscountedReward :: Integer -> Rational
maxDiscountedReward = undefined

discount :: Integer -> Rational
discount n = discountFactor ^ n

-- Given the list xs, walks back through it, generating
-- (for each element x of xs) the pair (xs before x, x).
-- This is useful when computing the probability that xs was generated, when
-- P(x|xs before x) is known for each x.
events :: [a] -> [([a], a)]
events xs = [(take n xs, xs !! n) | n <- [0 .. pred $ length xs]]

-- Given a machine and a list of OA pairs, compute the probability that that
-- machine would have produced those observations (given those actions).
getHistProb :: POM m => History -> Machine -> Real m
getHistProb rhist m = realProduct [getProb b bs m | (bs, b) <- bitEvents] where
	obsEvents = second fst <$> events (reverse rhist)
	bitEvents = concatMap (uncurry o2b) obsEvents
	o2b h o = first (histStr h ++) <$> events o

-- The bitstring corresponding to a OA sequence.
-- Note that we can just append all the observations and actions together,
-- because we assume prefix-free encodings.
histStr :: History -> [Bit]
histStr hist = concat [o ++ a | (o, a) <- reverse hist]

-- If we're between observations, this will sample a machine and start acting
-- like that machine. Otherwise, it will continue outputting an observation
-- (given the history) as if it was the chosen machine.
envInductor :: POM m => EnvHistory -> m (Machine, Bit)
envInductor (EnvHistory bits mm hist) = getM >>= \m -> (m,) <$> predict m where
	-- Note that if we need to sample a new machine, bits must be [].
	getM = maybe (sampleMachine $ getHistProb hist) return mm
	predict = flipR . getProb One (histStr hist ++ bits)

-- Runs the interaction of an agent with an environment, starting with an
-- environment (which may be partway through outputting an observation).
stepE :: POM m => Agent m -> Environment m -> EnvHistory -> m (Stream OA)
stepE agent env hist = if isObservation $ partialO hist then a else e where
	a = stepA agent env newAhist
	e = env hist >>= stepE agent env . newEhist
	newAhist = AgentHistory [] (partialO hist) (prevHistE hist)
	newEhist (m, bit) = hist{partialO = bit : partialO hist, currentM = Just m}

-- Runs the interaction of an agent with an environment, starting with an agent
-- (which may be partway through outputting an action.)
stepA :: POM m => Agent m -> Environment m -> AgentHistory -> m (Stream OA)
stepA agent env hist = if isAction $ partialA hist then e else a where
	e = ((currentO hist, partialA hist):!) <$> stepE agent env newEhist
	a = agent hist >>= stepA agent env . newAhist
	newEhist = EnvHistory [] Nothing $ (currentO hist, partialA hist) : prevHistA hist
	newAhist bit = hist{partialA = bit : partialA hist}

-- Runs the interaction of an agent with an environment, starting with the
-- environment outputting a fresh observation.
interact :: POM m => Agent m -> Environment m -> History -> m (Stream OA)
interact agent env hist = stepE agent env (EnvHistory [] Nothing hist)

-- Computes the reward of an agent interacting with an environment.
-- Computes better and better approximations to this sum (as a series of nested
-- intervals). Guaranteed to converge (if rewards are on [0, 1]) due to
-- time-discounting.
reward :: POM m => Agent m -> Environment m -> AgentHistory -> m (Real m)
reward agent env hist = ((<$> naturals) . approx) <$> stepA agent env hist where
	approx oas n = pure (x + maxDiscountedReward n, x) where x = rewardsIn 0 (streamTake n oas)
	rewardsIn i ((o, _):rest) = (discount i * rewardFrom o) + rewardsIn (succ i) rest
	rewardsIn _ [] = 0

-- Finds a machine that outputs 1 with probability equal to the given real
coinflipM :: POM m => m (Real m) -> Machine
coinflipM rM = encodeB $ do
	r <- rM
	randR <- genRandomReal
	order <- compareR randR r
	return $ if order == GT then One else Zero

-- Outputs 1 if x > y, 0 if x < y, where x and y are expected utilities in [0,
-- 1], using the oracle to check.
chooseBetween :: POM m => m (Real m) -> m (Real m) -> m Bit
chooseBetween xM yM = oracle (coinflipM biasedM) [] (1 / 2) where
	biasedM = do
		x <- xM
		y <- yM
		return $ liftR1 (/ 2) (liftR1 (+1) (x `realSub` y))

-- Outputs the bit with higher expected reward assuming that the future agent
-- and environment act as given.
aixiTemplate :: POM m => Agent m -> Environment m -> AgentHistory -> m Bit
aixiTemplate agent env hist = chooseBetween (xr One) (xr Zero) where
	xr bit = reward agent env $ hist{partialA = bit : partialA hist}

-- AIXI that expects itself to remain AIXI, starting with a Solomnooff distribution.
aixi :: POM m => Agent m
aixi = aixiTemplate aixi envInductor
