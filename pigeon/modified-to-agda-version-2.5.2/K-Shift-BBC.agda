module K-Shift-BBC where

open import Logic
open import Naturals
open import JK-Monads
open import J-Shift-BBC


K-∀-shift-bbc : {R : Ω} {A : ℕ → Ω} → 
-------------

            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-bbc efqs φs = J-K(J-∀-shift-bbc(λ n → K-J(efqs n) (φs n)))
