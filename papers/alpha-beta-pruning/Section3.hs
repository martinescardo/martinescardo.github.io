-- Section 3: adding alpha-beta pruning via the reader monad.
-- The code of Sections 3.1, 3.2 and 3.3 of the paper, in that order,
-- with the outcome function q' of Section 2.2.
-- Departures from the paper are marked ADDED.

-- Section 3.1

import K
import Control.Monad.Trans.Reader
import Debug.Trace

import Utils

type Move = Int     -- ADDED: "as above", Section 2.1.
type Path = [Move]  -- ADDED
type Moves = [Int]  -- ADDED
type R = Int        -- ADDED

-- Value to be used as -inf and +inf
inf :: Int
inf = 1000

-- Reader Monad
type T = Reader (Int, Int)

phiMax :: Moves -> (Move -> T R) -> T R
phiMax xs p = do
    (_, b) <- ask
    rs <- l xs
    return $ maximum $ takeUntil (>= b) rs
  where
    l :: Moves -> T [R]
    l [] = return []
    l (x:xs) = do
      (a, b) <- ask
      r <- p x
      rs <- local (const (max a r, b)) (l xs)
      return (r : rs)

phiMin :: Moves -> (Move -> T R) -> T R
phiMin xs p = do
    (a, _) <- ask
    rs <- l xs
    return $ minimum $ takeUntil (<= a) rs
  where
    l :: Moves -> T [R]
    l [] = return []
    l (x:xs) = do
      (a, b) <- ask
      r <- p x
      rs <- local (const (a, min b r)) (l xs)
      return (r : rs)

-- Section 3.2

-- game quantifiers for max-min game trees
phisT :: [K (T R) Move]
phisT = [K (phiMax [0,1,2]), K (phiMin [0,1]),
         K (phiMax [0,1]), K (phiMin [0,1,2])]

-- sequencing quantifier to obtain 'global' game quantifier
bigPhi :: K (T R) Path
bigPhi = sequence phisT

-- Section 3.3

-- ADDED: the outcome function q' of Section 2.2.
q' :: Path -> R
q' [0,0,0,0] = 5
q' [0,0,0,_] = 6
q' [0,0,1,0] = 7
q' [0,0,1,1] = 4
q' [0,0,1,2] = 5  -- can be pruned
q' [0,1,_,_] = 3  -- can be partially pruned
q' [1,0,0,_] = 6
q' [1,0,1,0] = 6
q' [1,0,1,_] = 9  -- can be pruned
q' [1,1,_,_] = 7  -- can be partially pruned
q' [2,0,_,_] = 5  -- can be partially pruned
q' [2,_,_,_] = 9  -- can be pruned

-- Make it monadic and add tracing to monitor evaluated branches
-- and order of evaluation
q :: Path -> T R
q xs = return $ let r = q' xs in
  trace (show xs ++ " -> " ++ show r) r

optimal_outcome :: R
optimal_outcome = (runReader $ quantifier bigPhi q) (-inf, inf)

-- ADDED: to run it as a program.
main :: IO ()
main = print optimal_outcome
