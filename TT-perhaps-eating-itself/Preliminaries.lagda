Chuangjie Xu & Martin Escardo, 2014

\begin{code}

module Preliminaries where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)

data [] {i : Level} : Set i where
 ⋆ : [] 

record Σ {i j : Level}{A : Set i}(B : A → Set j) : Set(i ⊔ j) where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

data _≡_ {i : Level}{A : Set i} : A → A → Set i where
 refl : {a : A} → a ≡ a

J : {i j : Level} {A : Set i} {a b : A} →
    (C : (x y : A) → x ≡ y → Set j) →
    ((x : A) → C x x refl) →
    (c : a ≡ b) → C a b c
J {i} {j} {A} {a} {.a} C f refl = f a

\end{code}
