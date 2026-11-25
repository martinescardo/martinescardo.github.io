-- Section 5: computing optimal plays.
-- The code of Section 3 with the changes of Section 5.
-- Departures from the paper are marked ADDED.

import K
import Control.Monad.Trans.Reader
import Utils
import Debug.Trace

type Move = Int
type Path = [Move]
type Moves = [Int]

-- Extended outcome type to include play leading to the outcome
type R = (Int, Path)

inf :: Int
inf = 1000

type T = Reader (Int, Int)

phiMax :: Moves -> K (T R) Move
phiMax = K . phiMax'
  where
    phiMax' :: Moves -> (Move -> T R) -> T R
    phiMax' xs p = do
      (_, b) <- ask
      rs <- results xs p
      -- changed (>=b) to \(r, ms) -> r >= b
      -- changed maximum to pickMax
      return $ pickMax $ takeUntil (\(r, ms) -> r >= b) rs

    results :: Moves -> (Move -> T R) -> T [R]
    results [] _ = return []
    results (y:ys) p = do
      (a, b) <- ask
      -- changed r <- p y to (r, ms) <- p y
      (r, ms) <- p y
      rs <- local (const (max a r, b)) (results ys p)
      -- changed r to (r, ms)
      return ((r, ms) : rs)

-- ADDED: the paper doesn't show the amended min quantifier. It is the
-- dual of phiMax above, as phiMin of Section 3.1 is the dual of phiMax.
phiMin :: Moves -> K (T R) Move
phiMin = K . phiMin'
  where
    phiMin' :: Moves -> (Move -> T R) -> T R
    phiMin' xs p = do
      (a, _) <- ask
      rs <- results xs p
      return $ pickMin $ takeUntil (\(r, ms) -> r <= a) rs

    results :: Moves -> (Move -> T R) -> T [R]
    results [] _ = return []
    results (y:ys) p = do
      (a, b) <- ask
      (r, ms) <- p y
      rs <- local (const (a, min b r)) (results ys p)
      return ((r, ms) : rs)

phisT :: [K (T R) Move]
phisT = [phiMax [0,1,2], phiMin [0,1], phiMax [0,1], phiMin [0,1,2]]

bigPhi :: K (T R) Path
bigPhi = sequence phisT

-- ADDED: the values of the outcome function q' of Section 2.2.
q' :: Path -> Int
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
         trace (show xs ++ " -> " ++ show r) (r, xs)

optimal_outcome_and_play :: R
optimal_outcome_and_play =
    (runReader $ quantifier bigPhi q) (-inf, inf)

-- ADDED: to run it as a program.
main :: IO ()
main = print optimal_outcome_and_play
