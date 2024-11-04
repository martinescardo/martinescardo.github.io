module CoTicTacToe (gameName, R, Move, p, epsilons) where

import Set
import InfSupSelections

gameName = "co-tic-tac-toe"

-- The board and moves are
--                                    012
--                                    345
--                                    678
-- R is the set 3 = {-1,0,1}

type R = Three 
type Move = Int
type Board = ([Move], [Move])
data Player = X | O

loses :: [Move] -> Bool
loses = 
 someContained [[0,1,2],[3,4,5],[6,7,8],[0,3,6],[1,4,7],[2,5,8],[0,4,8],[2,4,6]]

value :: Board -> R
value (x,o) = if loses x then -1 else if loses o then 1 else 0

outcome :: Player -> [Move] -> Board -> Board
outcome whoever [] board = board
outcome X (m : ms) (x, o) = 
    if loses o then (x, o) else outcome O ms (insert m x, o)
outcome O (m : ms) (x, o) = 
    if loses x then (x, o) else outcome X ms (x, insert m o)
   
p :: [Move] -> R
p ms = value(outcome X ms ([],[]))

epsilons :: [[Move] -> ((Move -> R) -> Move)]
epsilons = take 9 allepsilons
    where allepsilons = epsilonX : epsilonO : allepsilons
          epsilonX played = epsilonSup ([0..8] `setMinus` played) 
          epsilonO played = epsilonInf ([0..8] `setMinus` played) 
