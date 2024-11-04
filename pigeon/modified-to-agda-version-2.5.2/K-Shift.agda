module K-Shift where

-- This is a wrapper module. Perform a choice below.

open import Logic
open import Naturals
open import JK-Monads
open import K-Shift-Selection     
open import K-Shift-MBR        
open import K-Shift-BBC        


K-∀-shift : {R : Ω} {A : ℕ → Ω} → 
---------

   (∀(n : ℕ) → R → A n) →                             -- efqs,
   (∀(n : ℕ) → K {R} (A n)) → K {R} (∀(n : ℕ) → A n)  -- shift.


-- Choose here:

K-∀-shift = K-∀-shift-selection     
-- K-∀-shift = K-∀-shift-mbr
-- K-∀-shift = K-∀-shift-bbc      




