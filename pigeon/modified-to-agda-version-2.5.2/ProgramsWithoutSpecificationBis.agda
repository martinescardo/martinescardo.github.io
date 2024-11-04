module ProgramsWithoutSpecificationBis where

open import Cantor
open import Naturals
open import Addition
open import Two
open import Finite
open import Logic
open import FinitePigeon

program₁ : ₂ℕ → ℕ → ₂
program₁ α m = f(Theorem α m)
 where f : Finite-Pigeonhole α m → ₂
       f(∃-intro b proof) = b

program₂ : ₂ℕ → (m : ℕ) → (smaller(m + 1) → ℕ)
program₂ α m = f(Theorem α m)
 where f : Finite-Pigeonhole α m → (smaller(m + 1) → ℕ)
       f(∃-intro b (∃-intro s proof)) = s
