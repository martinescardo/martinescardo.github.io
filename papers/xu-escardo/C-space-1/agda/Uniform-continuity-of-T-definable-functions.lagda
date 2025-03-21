Chuangjie Xu, 2012

\begin{code}

module Uniform-continuity-of-T-definable-functions where

open import Mini-library
open import Space
open import Space-discrete
open import Space-product
open import Space-exponential
open import Space-cantor
open import Continuous-combinator
open import System-T
open import Set-interpretation-of-T
open import CSpace-interpretation-of-T


-- Logical relation over the two models

R : {A : Ty} → set A → U(space A) → Set
R {②} b b' = b ≡ b'
R {Ⓝ} n n' = n ≡ n'
R {A ↣ B} f f' = ∀(x : set A)(x' : U(space A)) →
                  R {A} x x' → R {B} (f x) (π₀ f' x')


Lemma : ∀{A : Ty} → ∀(t : Tm A) → R ⟦ t ⟧ C⟦ t ⟧
Lemma ⊤               = refl
Lemma ⊥               = refl
Lemma (If {A})        = claim
 where
  claim : (a₀ : set A)(a₀' : U(space A)) → R a₀ a₀' →
          (a₁ : set A)(a₁' : U(space A)) → R a₁ a₁' →
          (b b' : ₂) → b ≡ b' →
          R (⟦ If ⟧ a₀ a₁ b) (π₀ (π₀ (π₀ C⟦ If {A} ⟧ a₀') a₁') b')
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₀ ₀ refl = r₀
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₀ ₁ ()
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₁ ₀ ()
  claim a₀ a₀' r₀ a₁ a₁' r₁ ₁ ₁ refl = r₁
Lemma Zero            = refl
Lemma Succ            = λ x x' r → cong succ r
Lemma (Rec {A})       = claim
 where
  claim : (f : set(A ↣ A))(f' : U(space(A ↣ A))) → R f f' →
          (a : set A)(a' : U(space A)) → R a a' →
          (n n' : ℕ) → n ≡ n' →
          R (⟦ Rec ⟧ f a n) (π₀ (π₀ (π₀ C⟦ Rec {A} ⟧ f') a') n')
  claim f f' r a a' s 0        0         refl = s
  claim f f' r a a' s 0        (succ n') ()
  claim f f' r a a' s (succ n) 0         ()
  claim f f' r a a' s (succ n) (succ n') eq   =
        r (⟦ Rec ⟧ f a n) (π₀ (π₀ (π₀ C⟦ Rec {A} ⟧ f') a') n')
          (claim f f' r a a' s n n' (succ-injective eq))
Lemma (K {A})         = λ x x' r y y' s → r
Lemma (S {A} {B} {C}) = claim
 where
  claim : (x : set(A ↣ B ↣ C))(x' : U(space(A ↣ B ↣ C))) → R x x' →
          (y : set(A ↣ B))(y' : U(space(A ↣ B))) → R y y' →
          (z : set A)(z' : U(space A)) → R z z' →
          R (⟦ S ⟧ x y z) (π₀ (π₀ (π₀ C⟦ S {A} {B} {C} ⟧ x') y') z')
  claim x x' r y y' s z z' t = r z z' t (y z) (π₀ y' z') (s z z' t)
Lemma (t · u)         = Lemma t ⟦ u ⟧ C⟦ u ⟧ (Lemma u)


uniformly-continuous = uniformly-continuous-ℕ

Theorem : ∀(f : ₂ℕ → ℕ) → T-definable f → uniformly-continuous f
Theorem f (t , r) = ∃-intro n prf
 where
  fact : R f C⟦ t ⟧
  fact = subst {₂ℕ → ℕ} {λ h → R h C⟦ t ⟧} r (Lemma t)
  g : ₂ℕ → ℕ
  g α = π₀ C⟦ t ⟧ (α , Lemma[discreteness] {ℕ} {₂Space} α)
  id' : ₂ℕ → U (ℕSpace ⇒ ₂Space)
  id' = ∃-witness (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] id Lemma[id-UC])
  id'-is-a-probe : id' ∈ Probe (ℕSpace ⇒ ₂Space)
  id'-is-a-probe = ∃-elim (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] id Lemma[id-UC])
  uc-g : uniformly-continuous-ℕ g
  uc-g = π₁ C⟦ t ⟧ id' id'-is-a-probe
  eq : ∀(α : ₂ℕ) → f α ≡ g α
  eq α = fact α (α , Lemma[discreteness] {ℕ} {₂Space} α) (λ n n' eq → cong α eq)
  n : ℕ
  n = ∃-witness uc-g
  prf : ∀(α β : ₂ℕ) → α ≣ n ≣ β → f α ≡ f β
  prf α β aw = trans (trans (eq α) (∃-elim uc-g α β aw)) (sym (eq β))

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

\end{code}

The second example does not work: m₁ cannot be normalized to
a natural number, as it computation uses extensionality, which
stops the normalization.