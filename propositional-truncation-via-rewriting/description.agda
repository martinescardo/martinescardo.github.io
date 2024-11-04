-- Martin Escardo, 7th August 2015.

{-# OPTIONS --without-K #-}

module description where

open import preliminaries
open import prop
open import proptrunc
open import logic

-- First we need a Prp-valued equality to be able to define ∃!:

infix 34 _≡[_]_

_≡[_]_ : {i : 𝕃} {X : U i} → X → isSet X → X → Prp{i}
x ≡[ s ] y = (x ≡ y) , s

∃! : {i : 𝕃} {X : U i} → isSet X → (X → Prp{i}) → Prp{i}
∃! s p = (∃̇ p) ∧ ∀̇ \x → ∀̇ \y → p x ⇒ p y ⇒ x ≡[ s ] y

description : {i : 𝕃} (X : U i) (s : isSet X) (p : X → Prp{i})
            → (∃! s p) holds → Σ \(x : X) → p x holds
description {i} X s p eu = ∥∥-rec h (λ x → x) e
 where
  P : X → U i
  P x = p x holds
  e : ∥(Σ \(x : X) → P x)∥
  e = ∧-elim-L {i} {∃̇ p} {∀̇ \x → ∀̇ \y → p x ⇒ p y ⇒ x ≡[ s ] y} eu
  u : (x y : X) → P x → P y → x ≡ y
  u = ∧-elim-R {i} {∃̇ p} {∀̇ \x → ∀̇ \y → p x ⇒ p y ⇒ x ≡[ s ] y} eu
  h : isProp(Σ \(x : X) → P x)
  h (x , r) (y , s) = Σ-≡ (u x y r s) (holdsIsProp (p y) (transport P (u x y r s) r) s)
