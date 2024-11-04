module Play (gameName, optimalPlay, optimalOutcome, optimalStrategy) where

import DependentBigotimes    

-- Choose one of the following games:

import TicTacToe
-- import SubTicTacToe
-- import CoTicTacToe
-- import NQueens        
-- import Game15           
-- import SortGame         
-- import Reachability
-- import HamiltonianPath  
---import HamiltonianCycle 
-- import ShortestPath     
-- import EulerianPath     
-- import ExactCover       
-- import ExactHittingSet  


optimalPlay :: [Move]
optimalPlay = bigotimes epsilons p

optimalOutcome :: R
optimalOutcome = p optimalPlay

optimalStrategy :: [Move] -> Move
optimalStrategy as = head(bigotimes epsilons' p')
   where epsilons' = drop (length as) epsilons
         p' xs = p(as ++ xs)
