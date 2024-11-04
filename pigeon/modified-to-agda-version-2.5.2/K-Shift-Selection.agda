module K-Shift-Selection where

open import Logic
open import Naturals
open import JK-Monads
open import J-Shift-Selection


K-∀-shift-selection : {R : Ω} {A : ℕ → Ω} → 
-------------------

            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-selection efqs φs = J-K(J-∀-shift-selection(λ n → K-J(efqs n) (φs n)))
