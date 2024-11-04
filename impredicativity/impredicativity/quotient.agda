-- Martin Escardo, 3rd August 2015

{-# OPTIONS --without-K #-}

module quotient where

open import preliminaries
open import prop
open import proptrunc

image : {X A : U} → (X → A) → U
image {X} {A} f = Σ \(a : A) → ∥(Σ \(x : X) → f x ≡ a)∥ 

_/_ : (X : U) (R : X → X → Prp) → U
X / R = image R

_mod_ : {X : U} (x : X) (R : X → X → Prp) → X / R
x mod R = R x , ∣ x , refl(R x) ∣

-- Elimination from a quotient takes more work. I will complete this later:
{-
 /-elim : {X A : U} (R : X → X → Prp) (f : X → A) 
       → isSet A → ((x y : X) → (R x y) holds → f x ≡ f y) → X / R → A
/-elim {X} {A} R f iss ext (φ , P) = ?
-}


