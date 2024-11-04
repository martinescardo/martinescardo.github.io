module Equality where

infix  2 _≡_
infix  2 _≠_

open import Logic

data _≡_ {X : Set} : X → X → Ω where
  reflexivity : {x : X} -> x ≡ x

_≠_ : {X : Set} → X → X → Ω
x ≠ y = ¬(x ≡ y)

two-things-equal-to-a-third-are-equal : {X : Set} →
             ∀(x y z : X) → x ≡ y ∧ x ≡ z → y ≡ z

two-things-equal-to-a-third-are-equal x .x .x (∧-intro reflexivity reflexivity) = reflexivity
