{-# OPTIONS --no-termination-check #-}

-- We use Berger's modified bar recursion functional to realize the
-- K-Shift.

module K-Shift-MBR where

open import Logic
open import LogicalFacts
open import Naturals
open import JK-Monads
open import Finite

K-∀-shift-mbr : {R : Ω} {A : ℕ → Ω} → 
-------------
            (∀(n : ℕ) → R → A n) →                   -- efqs,
            (∀(n : ℕ) → K(A n)) → K(∀(n : ℕ) → A n)  -- shift.

K-∀-shift-mbr {R} {A} efqs φs p = mbr {0} (λ ())
  where 
   mbr : {m : ℕ} → (∀(i : smaller m) → A(embed i)) → R
   mbr {m} s = p(override s (λ n → efqs n (φs m (λ x → mbr(append {A} s x)))))
