-- Section 6: Tic-Tac-Toe.
-- The code of Section 6 of the paper, with the min and max quantifiers
-- of Section 5. Departures from the paper are marked ADDED.

import K                           -- ADDED: imports
import Control.Monad.Trans.Reader  -- ADDED
import Utils                       -- ADDED
import Debug.Trace                 -- ADDED

type Move = Int
type Path = [Move]
type Moves = [Int]

type Board = ([Move], [Move])
data Player = X | O

type Three = Int

type R = (Three, Path)

type T = Reader (Int, Int) -- Reader Monad

-- In this case +1 and -1 can work as upper and lower
-- bounds for the possible game outcomes
inf :: Int
inf = 1

-- Defining the outcome function q for Tic-Tac-Toe

wins :: Path -> Bool
wins xs = some
  [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]]
    (\ys -> contained ys xs)

value :: Board -> Three
value (x,o) = if wins x then 1 else if wins o then -1 else 0

outcome :: Player -> [Move] -> Board -> Board
outcome whoever [] board = board
outcome X (m : ms) (x, o) =
  if wins o then (x, o) else outcome O ms (m : x, o)
outcome O (m : ms) (x, o) =
  if wins x then (x, o) else outcome X ms (x, m : o)

q' :: Path -> Three
q' ms = value $ outcome X ms ([],[])

q :: Path -> T R
q xs = return $ let r = q' xs in
  trace (show xs ++ " -> " ++ show r) (r, xs)

-- ADDED: the min and max quantifiers of Section 5. hsequence, used
-- below, is in K (Appendix B).

phiMax :: Moves -> K (T R) Move
phiMax = K . phiMax'
  where
    phiMax' :: Moves -> (Move -> T R) -> T R
    phiMax' xs p = do
      (_, b) <- ask
      rs <- results xs p
      return $ pickMax $ takeUntil (\(r, ms) -> r >= b) rs

    results :: Moves -> (Move -> T R) -> T [R]
    results [] _ = return []
    results (y:ys) p = do
      (a, b) <- ask
      (r, ms) <- p y
      rs <- local (const (max a r, b)) (results ys p)
      return ((r, ms) : rs)

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

-- Defining the (history-dependent) quantifiers

-- game quantifiers for max-min players
phisT :: [Path -> K (T R) Move]
phisT = (phiMax . minus [0..8]) : (phiMin . minus [0..8]) : phisT

-- global quantifier for the game tree
-- we use hsequence since the available moves at any point in
-- the game depend on what has been played before
bigPhi :: K (T R) Path
bigPhi = hsequence $ take 9 phisT

-- Calculating optimal outcome and an optimal play
optimal_outcome_and_play :: R
optimal_outcome_and_play = (runReader $ quantifier bigPhi q) (-inf, inf)

-- ADDED: to run it as a program.
main :: IO ()
main = print optimal_outcome_and_play
