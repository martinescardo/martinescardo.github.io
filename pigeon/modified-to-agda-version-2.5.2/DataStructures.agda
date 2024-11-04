module DataStructures where

-- Some definitions of standard things
-- (sorry for not using libraries).

open import Naturals
open import Addition
open import Finite
open import LogicalFacts


data List (X : Set) : Set where
 [] : List X
 _::_  : X → List X → List X

infixr 30 _::_


-- Transforms a finite list given as a map to an enumerated finite
-- list:

list : {m : ℕ} {X : Set} → (smaller m → X) → List X
list {0} s = []
list {succ m} s = s fzero :: list {m} (s ∘ fsucc)


-- Binary products:

data _×_ (X Y : Set) : Set where
 _,_ : X → Y → X × Y


infixr 20 _,_


-- The cons operation for the Cantor space:

open import Cantor
open import Two

_^_ : ℕ → ₂ℕ → ₂ℕ
(0 ^ α) 0 = ₀
((succ n) ^ α) 0 = ₁
(b ^ α) (succ n) = α n

infixr 30 _^_


-- Take a finite initial sublist of an infinite sequence.

take : (m : ℕ) {X : Set} → (ℕ → X) → List X
take 0 α = []
take (succ m) α = α 0 :: take m (α ∘ succ)

-- Index a finite sequence:

_!_ : {m : ℕ} → (smaller(m + 1) → ℕ) → ℕ → ℕ
_!_ {m} s n = s(fmin m n)

