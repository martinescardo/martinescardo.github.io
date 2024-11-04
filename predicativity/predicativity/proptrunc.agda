-- Martin Escardo, 7th August 2015

{-# OPTIONS --without-K #-}

module proptrunc where

open import preliminaries
open import prop

large-∥_∥ : {i : L} → U i → U (lsuc i)
large-∥ X ∥ = (p : Prp _) → (X → p holds) → p holds

large-∣_∣ : {i : L} → {X : U i} → X → large-∥ X ∥
large-∣ x ∣ = λ _ f → f x

large-∥∥-rec : {i : L} {X : U i} {P : U i} → isProp P → (X → P) → large-∥ X ∥ → P
large-∥∥-rec {i} {X} {P} isp φ s = s ₍ P , isp ₎ φ

large-∥∥-rec-comp : {i : L} {X P : U i} {isp : isProp P} (φ : X → P) (x : X) 
                  →  large-∥∥-rec isp φ large-∣ x ∣ ≡ φ x
large-∥∥-rec-comp φ x = refl(φ x)

open import funext

large-∥∥-isProp : {i : L} {X : U i} → isProp large-∥ X ∥
large-∥∥-isProp s t = lemma
 where
  lemma : s ≡ t
  lemma = funext (λ p → funext (λ f → holdsIsProp p (s p f) (t p f)))

large-∥∥-ind : {i : L} {X : U i} {P : large-∥ X ∥ → U i} → ((s : large-∥ X ∥) → isProp(P s)) 
            → ((x : X) → P large-∣ x ∣) →  (s : large-∥ X ∥) → P s
large-∥∥-ind {i} {X} {P} isp φ s = large-∥∥-rec (isp s) ψ s
 where
  ψ : X → P s
  ψ x = transport P (large-∥∥-isProp large-∣ x ∣ s) (φ x)

large-∥∥-ind-comp : {i : L} {X : U i} {P : large-∥ X ∥ → U i} (isp : (s : large-∥ X ∥) 
                  → isProp(P s)) (φ : (x : X) → P large-∣ x ∣) 
                  → (x : X) → large-∥∥-ind isp φ large-∣ x ∣ ≡ φ x
large-∥∥-ind-comp isp φ x = isp large-∣ x ∣ (large-∥∥-ind isp φ large-∣ x ∣) (φ x)

-- A higher-inductive definition of ∥-∥ makes it small. Here we
-- instead use postulates to define it (we may change it to an actual
-- definition using Dan Licata's trick to simulate the HIT in the
-- future).

postulate 
  ∥_∥ : {i : L} → U i → U i
  ∥∥-isProp : {i : L} {X : U i} → isProp ∥ X ∥
  ∣_∣ : {i : L} → {X : U i} → X → ∥ X ∥
  ∥∥-ind : {i : L} {X : U i} {P : ∥ X ∥ → U i} → ((s : ∥ X ∥) → isProp(P s)) 
         → ((x : X) → P ∣ x ∣) →  (s : ∥ X ∥) → P s

∥∥-rec : {i : L} {X P : U i} → isProp P → (X → P) → ∥ X ∥ → P
∥∥-rec {i} {X} {P} isp φ s = ∥∥-ind (λ _ → isp) φ s

∥∥-ind-comp : {i : L} {X : U i} {P : ∥ X ∥ → U i}
              (isp : (s : ∥ X ∥) → isProp(P s)) (φ : (x : X) → P ∣ x ∣) 
            → (x : X) → ∥∥-ind isp φ ∣ x ∣ ≡ φ x
∥∥-ind-comp isp φ x = isp ∣ x ∣ (∥∥-ind isp φ ∣ x ∣) (φ x)

∥∥-rec-comp : {i : L} {X P : U i} {isp : isProp P} (φ : X → P) (x : X) →  ∥∥-rec isp φ ∣ x ∣ ≡ φ x
∥∥-rec-comp {i} {X} {P} {isp} = ∥∥-ind-comp (λ s → isp) 

-- An important fact is that the small and large versions of
-- propositional truncation are logically equivalent:

increase : {i : L} {X : U i}  → ∥ X ∥ → large-∥ X ∥
increase s p f = ∥∥-rec (holdsIsProp p) f s

decrease : {i : L} {X : U i}  → large-∥ X ∥ → ∥ X ∥
decrease = large-∥∥-rec ∥∥-isProp ∣_∣
