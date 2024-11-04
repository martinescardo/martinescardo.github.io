30 Mar 2013. MHE.

If every type has a constant endomap (the principle of global choice
holds), then every type has decidable equality.

We don't use any feature of Agda that goes beyond intensional
MLTT. Although we use HoTT notions, we don't use any HoTT axiom. In
particular, hpropositional reflection is defined from the assumption
of global choice.

\begin{code} 

{-# OPTIONS --without-K #-}

module GlobalChoice where

open import mini-library
open import KrausLemma
open import decidable-and-discrete

postulate Global-Choice : (X : Type) → Σ \(κ : X → X) → constant κ

κ : (X : Type) → X → X
κ X = π₀(Global-Choice X)
κ-constant : (X : Type) → constant(κ X)
κ-constant X = π₁(Global-Choice X)

hinhabited : Type → Type
hinhabited X = fix(κ X)

hprop-hinhabited : {X : Type} → hprop(hinhabited X)
hprop-hinhabited {X} = Kraus-Lemma (κ X) (κ-constant X)

η : {X : Type} → X → hinhabited X
η {X} x = κ X x , κ-constant X x (κ X x)

hinhabited-elim : {X P : Type} → hprop P → (X → P) → (hinhabited X → P)
hinhabited-elim _ f = f ∘ π₀

global-choice : {X : Type} → hinhabited X → X
global-choice = π₀

\end{code}

We apply global choice to

    (a₀ ≡ x) + (a₁ ≡ x)

to conclude that a₀ ≡ a₁ is decidable. We represent the displayed type
as Σ \(i : ₂) → a i ≡ x for convenience.

\begin{code} 

taboo : (X : Type) →  (a : ₂ → X) → decidable(a ₀ ≡ a ₁)
taboo X a  = equal-or-different
 where
  E : Type
  E = Σ \(x : X) → hinhabited(Σ \(i : ₂) → a i ≡ x)

  r : ₂ → E
  r i = a i , η(i , refl)

  r-splits : (e : E) → Σ \(i : ₂) → r i ≡ e
  r-splits (x , p) = π₀ p' ,  Σ-≡ (a(π₀ p')) x (η((π₀ p') , refl)) p (π₁ p') (hprop-hinhabited _ p)
   where
    p' : Σ \(i : ₂) → a i ≡ x
    p' = global-choice p

  s : E → ₂
  s e = π₀(r-splits e)

  r-retract : (e : E) → r(s e) ≡ e
  r-retract e = π₁(r-splits e)

  s-injective : (e e' : E) → s e ≡ s e' → e ≡ e'
  s-injective e e' p = (r-retract e)⁻¹ • ap r p • r-retract e'

  a-r : (i j : ₂) → a i ≡ a j → r i ≡ r j
  a-r i j p = Σ-≡ (a i) (a j) (η(i , refl)) (η(j , refl)) p (hprop-hinhabited _ (η(j , refl)))

  r-a : (i j : ₂) → r i ≡ r j → a i ≡ a j
  r-a i j q = ap π₀ q

  a-s : (i j : ₂) → a i ≡ a j → s(r i) ≡ s(r j)
  a-s i j p = ap s (a-r i j p)

  s-a : (i j : ₂) → s(r i) ≡ s(r j) → a i ≡ a j
  s-a i j p = r-a i j (s-injective (r i) (r j) p)

  equal-or-different : (a ₀ ≡ a ₁) + (a ₀ ≡ a ₁ → ∅) 
  equal-or-different = claim(₂-discrete {s(r ₀)} {s(r ₁)})
   where 
    claim : (s(r ₀) ≡ s(r ₁)) + (s(r ₀) ≡ s(r ₁) → ∅) → (a ₀ ≡ a ₁) + (a ₀ ≡ a ₁ → ∅) 
    claim (in₀ p) = in₀ (s-a ₀ ₁ p)
    claim (in₁ u) = in₁ (λ p → u (a-s ₀ ₁ p)) 

\end{code}
