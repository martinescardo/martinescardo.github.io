module J-Shift where

-- Import one of J-Shift-BBC or J-Shift-Selection.

open import Logic
open import Naturals
open import JK-Monads
open import J-Shift-Selection        -- Choose here...

-- Use one of K-∀-shift-bbc or K-∀-shift-mbr or K-∀-shift-selection:

J-∀-shift : {R : Ω} {A : ℕ → Ω} → 
---------

   (∀(n : ℕ) → J(A n)) → J {R} (∀(n : ℕ) → A n)

J-∀-shift = J-∀-shift-selection     -- ... and here accordingly.



