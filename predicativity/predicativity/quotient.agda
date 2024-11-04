-- Martin Escardo, 7th August 2015

{-# OPTIONS --without-K #-}

module quotient where

open import preliminaries
open import prop
open import proptrunc

image : {i j : L} {X : U i} {A : U j} → (X → A) → U (i ⊔ j)
image {i} {j} {X} {A} f = Σ \(a : A) → ∥(Σ \(x : X) → f x ≡ a)∥ 

_/_ : {i j : L} (X : U i) (R : X → X → Prp j) → U (i ⊔ lsuc j)
X / R = image R

_mod_ : {i j : L} {X : U i} (x : X) (R : X → X → Prp j) → X / R
x mod R = R x , ∣ x , refl(R x) ∣

-- Elimination from a quotient takes more work. I will complete this later:
{-
 /-elim : {X A : U} (R : X → X → Prp) (f : X → A) 
       → isSet A → ((x y : X) → (R x y) holds → f x ≡ f y) → X / R → A
/-elim {X} {A} R f iss ext (φ , P) = ?
-}


