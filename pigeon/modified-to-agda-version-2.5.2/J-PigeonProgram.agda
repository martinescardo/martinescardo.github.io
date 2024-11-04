module J-PigeonProgram where

open import Cantor
open import Naturals
open import Two
open import Logic
open import J-FinitePigeon
open import DataStructures

-- Given an infinite boolean sequence α and a natural number m, find a
-- boolean b and a finite list of length n with the indices of a
-- finite constant subsequence of α with value b at all
-- positions. 
-- 
-- This is usually how such programs are specified in functional
-- programming (if they are at all). Here Theorem (defined in the
-- module FinitePigeon) is the program with the formal specification,
-- also formally checked. Once this is done we can erase the
-- specification.

pigeon-program : ₂ℕ →  ℕ  →  ₂  ×  List ℕ
pigeon-program α m = f(Theorem α m)
 where f : Finite-Pigeonhole α m → ₂ × List ℕ
       f(∃-intro b (∃-intro s proof)) = (b , list s)
