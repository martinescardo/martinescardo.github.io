-- Martin Escardo, 13 September 2017, based on earlier ideas and Agda files.

-- Propositional truncation, by resizing the large propositional
-- truncation, rather than using Voevodsky's resizing of all
-- propositions.

{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-} -- Needed because we import resize which relies on that.
                            -- Only this module in this development should use rewriting
                            -- (and the general purpose module resize.lagda used here).
module proptrunc where

open import preliminaries
open import prop
open import resize          -- Only this module in this development should use resize.

-- Large propositional truncation first:

∥_∥' : {i : 𝕃} → U i → U(lsuc i)
∥ X ∥' = (p : Prp) → (X → p holds) → p holds

∣_∣' : {i : 𝕃} {X : U i} → X → ∥ X ∥'
∣ x ∣' = λ _ f → f x

∥∥'-rec : {i : 𝕃} {X : U i} {P : U i} → isProp P → (X → P) → ∥ X ∥' → P
∥∥'-rec {i} {X} {P} isp φ s = s ( P , isp ) φ

∥∥'-rec-comp : {i : 𝕃} {X : U i} {P : U i}
            → {isp : isProp P} (φ : X → P) (x : X) →  ∥∥'-rec isp φ ∣ x ∣' ≡ φ x
∥∥'-rec-comp φ x = refl(φ x)

-- To have that ∥ X ∥' is a proposition we need function extensionality.
-- In fact, assuming that ∥ X ∥' is a proposition gives function extensionality
-- (proof omitted here).

∥∥'-isProp : {i : 𝕃} {X : U i} → isProp ∥ X ∥'
∥∥'-isProp {i} {X} s t = lemma₀
 where
  open import funext
  lemma₀ : s ≡ t
  lemma₀ = funext (λ p → funext (λ f → holdsIsProp p (s p f) (t p f)))

-- Then we resize it to make it small:

∥_∥ : {i : 𝕃} → U i → U i
∥ X ∥ = resize ∥ X ∥'

private increase' : {i : 𝕃} {X : U i} → ∥ X ∥ → ∥ X ∥'
increase' = resize-in

private decrease' : {i : 𝕃} {X : U i} → ∥ X ∥' → ∥ X ∥
decrease' = resize-out

decrease-increase' : {i : 𝕃} {X : U i} (s : ∥ X ∥)
                  → decrease'(increase' s) ≡ s
decrease-increase' = refl

increase-decrease' : {i : 𝕃} {X : U i} (s' : ∥ X ∥')
                  → increase'(decrease' s') ≡ s'
increase-decrease' = refl

∣_∣ : {i : 𝕃} {X : U i} → X → ∥ X ∥
∣ x ∣ = decrease' ∣ x ∣'

∥∥-rec : {i : 𝕃} {X : U i} {P : U i} → isProp P → (X → P) → ∥ X ∥ → P
∥∥-rec {i} {X} {P} isp φ s = ∥∥'-rec {i} {X} {P} isp φ (increase' s)

-- The computation rule is definitional:

∥∥-rec-comp : {i : 𝕃} {X : U i} {P : U i} {isp : isProp P} (φ : X → P) (x : X)
            →  ∥∥-rec isp φ ∣ x ∣ ≡ φ x
∥∥-rec-comp {i} {X} {P} {isp} φ x = refl (φ x)

∥∥-isProp : {i : 𝕃} {X : U i} → isProp ∥ X ∥
∥∥-isProp {i} {X} s t = ap decrease' lemma
 where
  open import funext
  lemma : increase' s ≡ increase' t
  lemma = ∥∥'-isProp (increase' s) (increase' t)

-- We don't need increase' and decrease' now that we have ∥∥-rec and
-- ∥∥-isProp defined from them:

increase : {i : 𝕃} {X : U i}  → ∥ X ∥ → ∥ X ∥'
increase s p f = ∥∥-rec (holdsIsProp p) f s

decrease : {i : 𝕃} {X : U i}  → ∥ X ∥' → ∥ X ∥
decrease = ∥∥'-rec ∥∥-isProp ∣_∣

-- But then of course we don't get the following as definitional
-- equalities, as we do with increase' and decrease':

decrease-increase : {i : 𝕃} {X : U i} (s : ∥ X ∥)
                  → decrease(increase s) ≡ s
decrease-increase s = ∥∥-isProp (decrease (increase s)) s

increase-decrease : {i : 𝕃} {X : U i} (s' : ∥ X ∥')
                  → increase(decrease s') ≡ s'
increase-decrease s' = ∥∥'-isProp (increase (decrease s')) s'

-- Induction on ∥ X ∥ follows from recursion, as usual:

∥∥-ind : {i : 𝕃} {X : U i} {P : ∥ X ∥ → U i} → ((s : ∥ X ∥) → isProp(P s))
       → ((x : X) → P ∣ x ∣) →  (s : ∥ X ∥) → P s
∥∥-ind {i} {X} {P} isp φ s = ∥∥-rec (isp s) ψ s
 where
  ψ : X → P s
  ψ x = transport P (∥∥-isProp ∣ x ∣ s) (φ x)

-- There should be a way of defining ∥∥-ind so that its computation
-- rule holds definitionally (using the ideas of the file hsetfunext
-- elsewhere). For the above definition, it only holds
-- propositionally:

∥∥-ind-comp : {i : 𝕃} {X : U i} {P : ∥ X ∥ → U i}
              (isp : (s : ∥ X ∥) → isProp(P s)) (φ : (x : X) → P ∣ x ∣)
            → (x : X) → ∥∥-ind isp φ ∣ x ∣ ≡ φ x
∥∥-ind-comp isp φ x = isp ∣ x ∣ (∥∥-ind isp φ ∣ x ∣) (φ x)
