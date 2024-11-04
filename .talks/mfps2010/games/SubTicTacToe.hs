module SubTicTacToe (SubTicTacToe.gameName, 
                     R, 
                     Move, 
                     SubTicTacToe.p, 
                     SubTicTacToe.epsilons) where

import TicTacToe

gameName = "sub-tic-tac-toe"

s = [0,2]

p moves = TicTacToe.p(s ++ moves)

epsilons = 
 [ \moves -> epsilon(s ++ moves) | epsilon <- drop(length s) TicTacToe.epsilons]

