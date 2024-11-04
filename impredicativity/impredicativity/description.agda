-- Martin Escardo, 6th August 2015.

{-
   We prove the axiom of description: for any set X and any
   p:X→Prp,

       (∃! p) = true → Σ(x:X).p(x)=true.
-}

{-# OPTIONS --without-K #-}

module description where

open import preliminaries
open import prop
open import proptrunc
open import logic

-- First we need a Prp-valued equality to be able to define ∃!:

infix 54 _≡[_]_

_≡[_]_ : {X : U} → X → isSet X → X → Prp
x ≡[ s ] y = ₍ x ≡ y , s ₎

∃! : {X : U} → isSet X → (X → Prp) → Prp
∃! s p = (∃̇ p) ∧ ∀̇ \x → ∀̇ \y → p x ⇒ p y ⇒ (x ≡[ s ] y)

description : (X : U) (s : isSet X) (p : X → Prp)
            → (∃! s p) holds → Σ \(x : X) → p x holds
description X s p eu = ∥∥-rec h (λ x → x) e
 where
  P : X → U
  P x = p x holds
  e : ∥(Σ \(x : X) → P x)∥
  e = ∧-elim-L {∃̇ p} {∀̇ \x → ∀̇ \y → p x ⇒ p y ⇒ x ≡[ s ] y} eu
  u : (x y : X) → P x → P y → x ≡ y
  u = ∧-elim-R {∃̇ p} {∀̇ \x → ∀̇ \y → p x ⇒ p y ⇒ x ≡[ s ] y} eu
  h : isProp(Σ \(x : X) → P x)
  h (x , r) (y , s) = Σ-≡ (u x y r s) (holdsIsProp (p y) (transport P (u x y r s) r) s)

-- Perhaps the following formulation is more suggestive:

Description : (X : U) (s : isSet X) (p : X → Prp)
            → (∃! s p) ≡ true → Σ \(x : X) → (p x ≡ true)
Description X s p eu = (pr₁ d , holds→equal-true (pr₂ d))
 where
  d : Σ \(x : X) → (p x holds)
  d = description X s p (equal-true→holds eu)
