Chuangjie Xu, 2014

(Changed all uses of pattern matching on refl by uses of J, 9th Nov 2017.)

\begin{code}

{-# OPTIONS --without-K #-}

module Preliminaries.HSet where

open import Preliminaries.SetsAndFunctions

\end{code}

The following proof is from

http://www.cs.bham.ac.uk/~mhe/agda/HSets.html

\begin{code}

collapsible : Set → Set
collapsible X = Σ \(f : X → X) → constant f

path-collapsible : Set → Set
path-collapsible X = {x y : X} → collapsible(x ≡ y)

path-collapsible-is-hset : {X : Set} → path-collapsible X → hset X
path-collapsible-is-hset {X} pc p q = (claim₀ p) · claim₁ · (claim₀ q)⁻¹
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f = pr₁ pc
  g : {x y : X} (p q : x ≡ y) → f p ≡ f q
  g = pr₂ pc
  claim₀ : {x y : X} (r : x ≡ y) → r ≡ (f refl)⁻¹ · (f r)
  claim₀ = J (λ {x} {y} r → r ≡ (f refl)⁻¹ · (f r)) λ {x} → sym-is-inverse (f refl) 
  claim₁ : (f refl)⁻¹ · (f p) ≡ (f refl)⁻¹ · (f q)
  claim₁ = ap (λ h → (f refl)⁻¹ · h) (g p q)

∅-is-collapsible : collapsible ∅
∅-is-collapsible = (λ x → x) , (λ x → λ ())

inhabited-is-collapsible : {X : Set} → X → collapsible X
inhabited-is-collapsible x = ((λ y → x) , λ y y' → refl)

empty : Set → Set
empty X = X → ∅

empty-is-collapsible : {X : Set} → empty X → collapsible X
empty-is-collapsible u = ((λ x → x) , (λ x x' → ∅-elim(u x)))

decidable-is-collapsible : {X : Set} → decidable X → collapsible X
decidable-is-collapsible (inl x) = inhabited-is-collapsible x
decidable-is-collapsible (inr u) = empty-is-collapsible u

discrete-is-path-collapsible : {X : Set} → discrete X → path-collapsible X
discrete-is-path-collapsible d = decidable-is-collapsible (d _ _)

discrete-is-hset : {X : Set} → discrete X → hset X
discrete-is-hset d = path-collapsible-is-hset(discrete-is-path-collapsible d)

\end{code}
