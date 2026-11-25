-- Section 2: exhaustive search via the continuation monad.
-- The code of Sections 2.1, 2.2 and 2.3 of the paper, in that order,
-- with the imports of 2.1 and 2.2 first, as Haskell requires.
-- Departures from the paper are marked ADDED.

import Debug.Trace
import K

-- Section 2.1

type Move = Int
type Path = [Move]
type Moves = [Int]
type R = Int

-- maximising player quantifier
phiMax :: Moves -> K R Move
phiMax xs = K (\p -> maximum $ map p xs)

-- minimising player quantifier
phiMin :: Moves -> K R Move
phiMin xs = K (\p -> minimum $ map p xs)

-- Section 2.2

-- Example, based on:
-- https://en.wikipedia.org/w/index.php?oldid=1380302874

-- Outcome function for the game tree in Example
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

-- Add tracing to monitor evaluated branches
-- and order of evaluation
q :: Path -> R
q xs = trace (show xs ++ " -> " ++ show (q' xs)) (q' xs)

-- Section 2.3

-- game quantifiers for the max-min experiment game trees
phis :: [K R Move]
phis = [phiMax [0,1,2], phiMin [0,1], phiMax [0,1], phiMin [0,1,2]]

-- sequencing quantifiers to obtain a 'global' game quantifier
bigPhi :: K R Path
bigPhi = sequence phis

optimal_outcome :: R
optimal_outcome = quantifier bigPhi q

-- ADDED: to run it as a program.
main :: IO ()
main = print optimal_outcome
