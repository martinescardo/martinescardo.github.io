-- File by Andrea Vezzosi (https://github.com/Saizan/cubical-demo)

{-# OPTIONS --cubical #-}
module Sub where

open import PathPrelude

-- "Sub A φ t" is our notation for "A[φ ↦ t]" as a type.
module _ {ℓ} {A : Set ℓ} where
  ouc-φ : {t : Partial A i1} → (s : Sub A i1 t) → (ouc s) ≡ t itIsOne
  ouc-φ s i = ouc s

  ouc-β : {φ : I} → (a : A) → ouc {φ = φ} {u = λ { (φ = i1) → a }} (inc {φ = φ} a) ≡ a
  ouc-β a i = a

safeComp : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub (A i0) φ (u i0)
                                  → Sub (A i1) φ (u i1)
safeComp A φ u azero = inc {φ = φ} (primComp A φ u (ouc azero))


safeFill : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub (A i0) φ (u i0) → (i : I) → A i
safeFill A φ u azero i = ouc (safeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
       (λ j → ([ φ ↦ (u (i ∧ j)) , ~ i ↦ (λ { (i = i0) → ouc azero })])) (inc (ouc azero)))



Comp : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub (A i0) φ (u i0)
                                  → A i1
Comp A φ u azero = primComp A φ u (ouc azero)


Fill : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  (u : (i : I) → Partial (A i) φ) → Sub (A i0) φ (u i0) → (i : I) → A i
Fill A φ u azero i = Comp (\ j → A (i ∧ j)) _ (\ { j (φ = i1) → u (i ∧ j) itIsOne
                                              ; j (i = i0) → ouc azero
                                              })
                                           (inc (ouc azero))
