module ProgramsWithoutSpecification where

open import Cantor
open import Naturals
open import Addition
open import Two
open import Finite
open import Logic
open import FinitePigeon

program₁ : ₂ℕ → ℕ → ₂
program₁ α m = ∃-witness(Theorem α m)

program₂ : ₂ℕ → (m : ℕ) → (smaller(m + 1) → ℕ)
program₂ α m = ∃-witness(∃-elim (Theorem α m))
