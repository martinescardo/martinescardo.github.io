-- Martin Escardo, 3rd August 2015

-- Propositional truncation.

{-# OPTIONS --without-K #-}

module proptrunc where

open import preliminaries
open import prop

-- Propositional truncation first:

∥_∥ : U → U
∥ X ∥ = (p : Prp) → (X → p holds) → p holds

infix 1 ∥_∥
infix 1 ∣_∣

-- Here ∥ X ∥ is ranged over by s and t.

∣_∣ : {X : U} → X → ∥ X ∥
∣ x ∣ = λ _ f → f x

∥∥-rec : {X P : U} → isProp P → (X → P) → ∥ X ∥ → P
∥∥-rec {X} {P} isp φ s = s ₍ P , isp ₎ φ

∥∥-rec-comp : {X P : U} → {isp : isProp P} (φ : X → P) (x : X) →  ∥∥-rec isp φ ∣ x ∣ ≡ φ x
∥∥-rec-comp φ x = refl(φ x)

-- To have that ∥ X ∥ is a proposition we need function extensionality.
-- In fact, assuming that ∥ X ∥ is a proposition gives function extensionality
-- (proof omitted here).

open import funext

∥∥-isProp : {X : U} → isProp ∥ X ∥
∥∥-isProp s t = lemma
 where
  lemma : s ≡ t
  lemma = funext (λ p → funext (λ f → holdsIsProp p (s p f) (t p f)))

-- Induction on ∥ X ∥ follows from recursion:

∥∥-ind : {X : U} {P : ∥ X ∥ → U} → ((s : ∥ X ∥) → isProp(P s))
       → ((x : X) → P ∣ x ∣) →  (s : ∥ X ∥) → P s
∥∥-ind {X} {P} isp φ s = ∥∥-rec (isp s) ψ s
 where
  ψ : X → P s
  ψ x = transport P (∥∥-isProp ∣ x ∣ s) (φ x)

-- There should be a way of defining ∥∥-ind so that its computation
-- rule holds definitionally (using the ideas of the file hsetfunext
-- elsewhere). For the above definition, it only holds
-- propositionally:

∥∥-ind-comp : {X : U} {P : ∥ X ∥ → U} (isp : (s : ∥ X ∥) → isProp(P s)) (φ : (x : X) → P ∣ x ∣)
            → (x : X) → ∥∥-ind isp φ ∣ x ∣ ≡ φ x
∥∥-ind-comp isp φ x = isp ∣ x ∣ (∥∥-ind isp φ ∣ x ∣) (φ x)
