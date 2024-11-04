module K-Shift-from-J-Shift where

open import Logic
open import LogicalFacts
open import Naturals
open import JK-Monads
open import J-Shift

K-∀-shift : {R : Ω} {A : ℕ → Ω} → 
---------
            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift efqs φs = J-K(J-∀-shift(λ n → K-J(efqs n) (φs n)))
