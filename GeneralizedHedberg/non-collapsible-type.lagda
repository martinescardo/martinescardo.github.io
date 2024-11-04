30 Mar 2013. MHE.

A type is called collapsible if it has a constant endomap, where a map
is called constant if any two of its values are equal. Hence any empty
or inhabited type is collapsible, and all types are collapsible under
excluded middle.

We give an explicit counter-example to collapsibility. From any two
given elements of any type, we construct a family of types such that
if each of them has a constant endomap, then the equality of the two
elements is decidable. Because there are types that don't provably
have decidable equality, this gives an example of a family of types
that can't be provably collapsible in general. This is developed in
pure intensional MLTT.

This module should probably be called non-collapsible-family-of-types
instead. It is an open problem to produce a single type (in a context)
that cannot be proved to be collapsible.

\begin{code} 

{-# OPTIONS --without-K #-}

module non-collapsible-type where

open import mini-library
open import KrausLemma
open import decidable-and-discrete

\end{code}

The type

    (a₀ ≡ x) + (a₁ ≡ x)

cannot be collapsible for all x unless a₀ ≡ a₁ is decidable. We
represent the displayed type as Σ \(i : ₂) → a i ≡ x for convenience.

A positive way of formulating this is as follows, as a technique for
proving the decidable equality of two given elements. But at present
it is difficult to imagine a situation where this technique would be
profitably applicable.


\begin{code} 

bold-proof-technique : (X : Type) → (a : ₂ → X) → ((x : X) → collapsible(Σ \(i : ₂) → a i ≡ x)) → decidable(a ₀ ≡ a ₁)
bold-proof-technique X a c = equal-or-different
 where
  κ : (x : X) → (Σ \(i : ₂) → a i ≡ x) → Σ \(i : ₂) → a i ≡ x
  κ x = π₀(c x)
  κ-constant : (x : X) → constant(κ x)
  κ-constant x = π₁(c x)

  hprop-fix : (x : X) → hprop(fix(κ x))
  hprop-fix x = Kraus-Lemma (κ x) (κ-constant x)

  choice : (x : X) → fix(κ x) → Σ \(i : ₂) → a i ≡ x
  choice x = π₀

  η : (x : X) → (Σ \(i : ₂) → a i ≡ x) → fix(κ x)
  η x σ = κ x σ , κ-constant x σ (κ x σ)

  E : Type
  E = Σ \(x : X) → fix(κ x)

  r : ₂ → E
  r i = a i , η (a i) (i , refl)

  r-splits : (e : E) → Σ \(i : ₂) → r i ≡ e
  r-splits (x , p) = π₀ p' , Σ-≡ (a(π₀ p')) x (η (a (π₀ p')) ((π₀ p') , refl)) p (π₁ p') (hprop-fix x _ p)
   where
    p' : Σ \(i : ₂) → a i ≡ x
    p' = choice x p

  s : E → ₂
  s e = π₀(r-splits e)

  r-retract : (e : E) → r(s e) ≡ e
  r-retract e = π₁(r-splits e)

  s-injective : (e e' : E) → s e ≡ s e' → e ≡ e'
  s-injective e e' p = (r-retract e)⁻¹ • ap r p • r-retract e'

  a-r : (i j : ₂) → a i ≡ a j → r i ≡ r j
  a-r i j p = Σ-≡ (a i) (a j) (η (a i) (i , refl)) (η (a j) (j , refl)) p (hprop-fix (a j) _ (η (a j) (j , refl)))

  r-a : (i j : ₂) → r i ≡ r j → a i ≡ a j
  r-a i j = ap π₀

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
