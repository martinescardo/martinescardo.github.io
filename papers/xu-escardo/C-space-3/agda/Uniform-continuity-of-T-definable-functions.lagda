Chuangjie Xu, 2012

\begin{code}

module Uniform-continuity-of-T-definable-functions where

open import Mini-library
open import ConsHeadTail
open import Uniform-continuity
open import Setoid
open import Space
open import Space-exponential
open import Space-product
open import Space-coproduct
open import Space-discrete
open import Space-cantor
open import Continuous-combinator
open import System-T
open import Set-interpretation-of-T
open import CSpace-interpretation-of-T


-- Logical relation over these two models

R : {A : Ty} → set A → Ũ(U(space A)) → Set
R {①} ⋆ ⋆ = ⋆ ≡ ⋆
R {②} b b' = b ≡ b'
R {Ⓝ} n n' = n ≡ n'
R {A ⊠ B} (a , b) (a' , b') = R a a' ∧ R b b'
R {A ⊞ B} (in₀ a) (in₀ a') = R a a'
R {A ⊞ B} (in₀ a) (in₁ b') = ∅
R {A ⊞ B} (in₁ b) (in₀ a') = ∅
R {A ⊞ B} (in₁ b) (in₁ b') = R b b'
R {A ↣ B} f ((f' , e) , cts) =
  ∀(x : set A)(x' : Ũ(U(space A))) → R x x' → R (f x) (f' x')



-- The set and C-space interpretations of any term are related.

Lemma : ∀{A : Ty} → ∀(t : Tm A) → R ⟦ t ⟧ C⟦ t ⟧
Lemma ✸                = refl
Lemma Unit             = λ _ _ _ → refl
Lemma ⊤                = refl
Lemma ⊥                = refl
Lemma (If {A})         = claim
 where
  claim : R ⟦ If {A} ⟧ C⟦ If {A} ⟧
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₀ ₀ refl = r₀
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₀ ₁ ()
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₁ ₀ ()
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₁ ₁ refl = r₁
Lemma Zero             = refl
Lemma Succ             = λ _ _ r → cong succ r
Lemma (Rec {A})        = claim
 where
  claim : R ⟦ Rec {A} ⟧ C⟦ Rec {A} ⟧
  claim f f' r a a' s 0        0         refl = s
  claim f f' r a a' s 0        (succ n') ()
  claim f f' r a a' s (succ n) 0         ()
  claim f f' r a a' s (succ n) (succ n') eq   =
        r (⟦ Rec ⟧ f a n)
          (π₀ (π₀ (π₀ (π₀ (π₀ (π₀ C⟦ Rec {A} ⟧) f')) a')) n')
          (claim f f' r a a' s n n' (succ-injective eq))
Lemma (K {A})          = λ _ _ r _ _ _ → r
Lemma (S {A}{B}{C})    = claim
 where
  claim : R ⟦ S {A}{B}{C} ⟧ C⟦ S {A}{B}{C} ⟧
  claim x x' r y y' s z z' t = r z z' t (y z) (π₀ (π₀ y') z') (s z z' t)
Lemma (t · u)          = Lemma t ⟦ u ⟧ C⟦ u ⟧ (Lemma u)
Lemma (t ˣ u)          = ∧-intro (Lemma t) (Lemma u)
Lemma Prj₀             = λ _ _ r → ∧-elim₀ r
Lemma Prj₁             = λ _ _ r → ∧-elim₁ r
Lemma Inj₀             = λ _ _ r → r
Lemma Inj₁             = λ _ _ r → r
Lemma (Case {A}{B}{C}) = claim
 where
  claim : R ⟦ Case {A}{B}{C} ⟧ C⟦ Case {A}{B}{C} ⟧
  claim f₀ f₀' r f₁ f₁' s (in₀ x) (in₀ x') t = r x x' t
  claim f₀ f₀' r f₁ f₁' s (in₀ x) (in₁ y') ()
  claim f₀ f₀' r f₁ f₁' s (in₁ y) (in₀ x') ()
  claim f₀ f₀' r f₁ f₁' s (in₁ y) (in₁ y') t = s y y' t



Theorem : ∀(f : ₂ℕ → ℕ) → T-definable f → uniformly-continuous f
Theorem f (t , r) = ∃-intro n prf
 where
  g : E-map-₂ℕ Eℕ
  g = ∃-witness (Lemma[Yoneda] {ℕSpace} C⟦ t ⟧)
  ucg : uniformly-continuous-ℕ g
  ucg = ∃-elim (Lemma[Yoneda] {ℕSpace} C⟦ t ⟧)
  claim₀ : R f C⟦ t ⟧
  claim₀ = subst {₂ℕ → ℕ} {λ h → R h C⟦ t ⟧} r (Lemma t)
  claim₁ : ∀(α : ₂ℕ) → f α ≡ π₀ g α
  claim₁ α = claim₀ α ᾱ rαᾱ
   where
    ᾱ : Map ℕSpace ₂Space
    ᾱ = Lemma[₂ℕ-to-Map-ℕ-₂] α
    rαᾱ : R α ᾱ
    rαᾱ n .n refl = refl
  n : ℕ
  n = ∃-witness ucg
  prf : ∀(α β : ₂ℕ) → α ≣ n ≣ β → f α ≡ f β
  prf α β e = trans (trans (claim₁ α) (∃-elim ucg α β e)) (sym (claim₁ β))

\end{code}

Translation rules ⦃_⦄:

0. ⦃ c ⦄              =  c               (c is a constant)

1. ⦃ λ x . x ⦄        =  I = S · K · K

2. ⦃ λ x . M ⦄        =  K · ⦃ M ⦄       (x is not free in M)

3. ⦃ λ x . λ y . M ⦄  =  ⦃ λ x . ⦃ λ y . M ⦄ ⦄

4. ⦃ λ x . (M N) ⦄    =  S · ⦃ λ x . M ⦄ · ⦃ λ x . N ⦄


To make the translation easier, we define the following auxilaries.

\begin{code}

I : {A : Ty} → Tm(A ↣ A)
I {A} = S · K · (K {A} {A})
 
encode : ℕ → Tm Ⓝ
encode 0 = Zero
encode (succ n) = Succ · (encode n)

-- This is a constant function.

f₀ : ₂ℕ → ℕ
f₀ = λ α → 0

definability-of-f₀ : T-definable f₀
definability-of-f₀ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = K · Zero

m₀ : ℕ
m₀ = ∃-witness (Theorem f₀ definability-of-f₀)


-- The output of this function depends on the first bit of input

f₁ : ₂ℕ → ℕ
f₁ = λ α → if 0 1 (α 10)

definability-of-f₁ : T-definable f₁
definability-of-f₁ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = S · (K · (If · (encode 0) · (encode 1))) · (S · (S · K · (K {Ⓝ ↣ ②} {②})) · (K · (encode 10)))

m₁ : ℕ
m₁ = ∃-witness (Theorem f₁ definability-of-f₁)


f₂ : ₂ℕ → ℕ
f₂ = λ α → if 3 (if 1 0 (α 4)) (α 2)

definability-of-f₂ : T-definable f₂
definability-of-f₂ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = S · (S · (K · (If · (encode 3))) · (S · (K · (If · (encode 1) · (encode 0))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 4))))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 2)))

m₂ : ℕ
m₂ = ∃-witness (Theorem f₂ definability-of-f₂)


f₃ : ₂ℕ → ℕ
f₃ = λ α → if (if 1 0 (α 4)) 3 (α 2)

definability-of-f₃ : T-definable f₃
definability-of-f₃ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = S · (S · (S · (K · If) · (S · (K · (If · (encode 1) · (encode 0))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 4))))) · (K · (encode 3))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 2)))

m₃ : ℕ
m₃ = ∃-witness (Theorem f₃ definability-of-f₃)


f₄ : ₂ℕ → ℕ
f₄ = λ α → if (if 1 (if 0 6 (α 5)) (α 4)) 3 (α 2)

definability-of-f₄ : T-definable f₄
definability-of-f₄ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = S · (S · (S · (K · If) · (S · (S · (K · (If · (encode 1))) · (S · (K · (If · (encode 0) · (encode 6))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 5))))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 4))))) · (K · (encode 3))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 2)))

m₄ : ℕ
m₄ = ∃-witness (Theorem f₄ definability-of-f₄)



f₅ : ₂ℕ → ℕ
f₅ = λ α → rec id 0 (if 0 1 (α 3))

definability-of-f₅ : T-definable f₅
definability-of-f₅ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = S · (K · (Rec · (I {Ⓝ}) · (encode 0))) · (S · (K · (If · (encode 0) · (encode 1))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 3))))

m₅ : ℕ
m₅ = ∃-witness (Theorem f₅ definability-of-f₅)


f₆ : ₂ℕ → ℕ
f₆ = λ α → rec succ (if 5 4 (α 3)) (if 0 1 (α 2))

definability-of-f₆ : T-definable f₆
definability-of-f₆ = (t , refl)
 where
  t : Tm ((Ⓝ ↣ ②) ↣ Ⓝ)
  t = S · (S · (K · (Rec · Succ)) · (S · (K · (If · (encode 5) · (encode 4))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 3))))) · (S · (K · (If · (encode 0) · (encode 1))) · (S · (I {Ⓝ ↣ ②}) · (K · (encode 2))))

m₆ : ℕ
m₆ = ∃-witness (Theorem f₆ definability-of-f₆)


\end{code}
