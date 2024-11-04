module Order where

open import Logic
open import Naturals
open import Addition
open import Equality

_≤_ : ℕ → ℕ → Ω
x ≤ y = ∃ \(n : ℕ) → x + n ≡ y 

_<_ : ℕ → ℕ → Ω
x < y = ∃ \(n : ℕ) → x + n + 1 ≡ y 

infix 30 _<_
infix 30 _≤_

-- This is how we are going to write inequality proofs (when possible):

less-proof : {x : ℕ} → (n : ℕ) → x < x + n + 1
less-proof n = ∃-intro n reflexivity

