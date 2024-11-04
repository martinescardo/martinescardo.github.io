module K-AC-N where

open import Logic
open import LogicalFacts
open import JK-LogicalFacts
open import Naturals
open import JK-Monads
open import Choice
open import K-Shift

-----------------------------------------------------------------------
-- The K-translation of countable choice AC-N can be proved only for --
-- certain formulas, including those that are in the image of the    --
-- K-translation.                                                    --
--                                                                   --
-- Hence we have a restriction efq (ex falso quadlibet).             --
--                                                                   --
-- This is because there is no general K-∀-shift.                    --
-----------------------------------------------------------------------


K-AC-ℕ : {R : Ω} {X : ℕ → Set} {P : (n : ℕ) → X n → Ω} →
-------
        (∀(n : ℕ) → R → ∃ \(m : X n) → P n m)               -- efqs,
      → (∀(n : ℕ) → K∃ \(m : X n) → P n m)                  -- premise,
      → K∃ \(f : ((n : ℕ) → X n)) → ∀(n : ℕ) → P n (f n)    -- conclusion.

K-AC-ℕ efqs = (K-functor AC) ∘ (K-∀-shift efqs)
