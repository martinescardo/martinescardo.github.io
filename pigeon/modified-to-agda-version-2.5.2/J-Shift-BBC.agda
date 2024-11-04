{-# OPTIONS --no-termination-check #-}

-- We use the Berardi-Bezem-Coquand functional to realize the J-Shift
-- (and hence the K-Shift in another module).

module J-Shift-BBC where

open import Logic
open import LogicalFacts
open import Naturals
open import JK-Monads


J-∀-shift-bbc : {R : Ω} {A : ℕ → Ω} → 
-------------

      (∀(n : ℕ) → J(A n)) → J(∀(n : ℕ) → A n)

J-∀-shift-bbc {R} {A} ε = bbc
  where 
   bbc : J {R} (∀(n : ℕ) → A n)
   bbc p i = ε i (λ x → J-K bbc (p ∘ mapsto {A} i x))
