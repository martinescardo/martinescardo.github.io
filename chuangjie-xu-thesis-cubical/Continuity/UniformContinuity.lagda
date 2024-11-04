Chuangjie Xu 2013 (Changes not needed for the cubical version of 9th Nov 2017)

\begin{code}

{-# OPTIONS --without-K #-}

module Continuity.UniformContinuity where

open import Preliminaries.SetsAndFunctions
open import Preliminaries.NaturalNumber hiding (_+_)
open import Preliminaries.Boolean
open import Preliminaries.Sequence

\end{code}

In the definitions of local constancy and uniform continuity, we require the
moduli to be the minimal.

\begin{code}

locally-constant : {X : Set} → (₂ℕ → X) → Set
locally-constant p = Σ-min \(n : ℕ) → ∀(α β : ₂ℕ) → α ≡[ n ] β → p α ≡ p β

Axiom[UC-ℕ] : Set
Axiom[UC-ℕ] = ∀(f : ₂ℕ → ℕ) → locally-constant f

uniformly-continuous-₂ℕ : (₂ℕ → ₂ℕ) → Set
uniformly-continuous-₂ℕ t = ∀(m : ℕ) → Σ-min \(n : ℕ) → ∀(α β : ₂ℕ) → α ≡[ n ] β → t α ≡[ m ] t β

\end{code}

Here we provide an algorithm to compute least moduli of uniform continuity.

\begin{code}

Lemma[decidable-zerō-1̄] : {X : Set} → (_~_ : X → X → Set) →
         (∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
         (p : ₂ℕ → X) → (n : ℕ) →
         decidable (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄))
Lemma[decidable-zerō-1̄] _~_ dec p n = Lemma[₂Fin-decidability] n P claim
 where
  P : ₂Fin n → Set
  P s = p (cons s zerō) ~ p (cons s 1̄)
  claim : ∀(s : ₂Fin n) → decidable (P s)
  claim s = dec (p (cons s zerō)) (p (cons s 1̄))


LM : {X : Set} → (_~_ : X → X → Set) → (∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
     (₂ℕ → X) → ℕ → ℕ
LM _~_ dec p zero        = zero
LM _~_ dec p (succ n) = case f₀ f₁ (Lemma[decidable-zerō-1̄] _~_ dec p n)
 where
  f₀ : (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) → ℕ
  f₀ _ = LM _~_ dec p n
  f₁ : ¬ (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) → ℕ
  f₁ _ = succ n


LM-₂ℕ : {m : ℕ} → (₂ℕ → ₂ℕ) → ℕ → ℕ
LM-₂ℕ {m} = LM {₂ℕ} (λ α β → α ≡[ m ] β) Lemma[≡[]-decidable] 

LM-ℕ : (₂ℕ → ℕ) → ℕ → ℕ
LM-ℕ = LM {ℕ} _≡_ ℕ-discrete

LM-₂ : (₂ℕ → ₂) → ℕ → ℕ
LM-₂ = LM {₂} _≡_ ₂-discrete


Lemma[LM]₀ : {X : Set} → (_~_ : X → X → Set) → (dec : ∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
             (p : ₂ℕ → X) → (n : ℕ) →
             (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) →
             LM _~_ dec p (succ n) ≡ LM _~_ dec p n
Lemma[LM]₀ _~_ dec p n h = equality-cases (Lemma[decidable-zerō-1̄] _~_ dec p n) claim₀ claim₁
 where
  claim₀ : ∀ h → Lemma[decidable-zerō-1̄] _~_ dec p n ≡ inl h → LM _~_ dec p (succ n) ≡ LM _~_ dec p n
  claim₀ _ r = ap (case _ _) r
  claim₁ : ∀ f → Lemma[decidable-zerō-1̄] _~_ dec p n ≡ inr f → LM _~_ dec p (succ n) ≡ LM _~_ dec p n
  claim₁ f = ∅-elim(f h)

Lemma[LM]₁ : {X : Set} → (_~_ : X → X → Set) → (dec : ∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
             (p : ₂ℕ → X) → (n : ℕ) →
             ¬ (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) →
             LM _~_ dec p (succ n) ≡ succ n
Lemma[LM]₁ _~_ dec p n f = equality-cases (Lemma[decidable-zerō-1̄] _~_ dec p n) claim₀ claim₁
 where
  claim₀ : ∀ h → Lemma[decidable-zerō-1̄] _~_ dec p n ≡ inl h → LM _~_ dec p (succ n) ≡ succ n
  claim₀ h = ∅-elim (f h)
  claim₁ : ∀ f → Lemma[decidable-zerō-1̄] _~_ dec p n ≡ inr f → LM _~_ dec p (succ n) ≡ succ n
  claim₁ _ r = ap (case _ _) r


Lemma[succ-zerō-1̄] : {X : Set} → (_~_ : X → X → Set) →
        (∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
        ({x₀ x₁ : X} → x₀ ~ x₁ → x₁ ~ x₀) →
        ({x₀ x₁ x₂ : X} → x₀ ~ x₁ → x₁ ~ x₂ → x₀ ~ x₂) →
        (p : ₂ℕ → X) → (n : ℕ) →
        (∀(α β : ₂ℕ) → α ≡[ succ n ] β → p α ~ p β) →
        (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) →
         ∀(α β : ₂ℕ) → α ≡[ n ] β → p α ~ p β
Lemma[succ-zerō-1̄] {X} _~_ dec sy tr p n pr g α β en = tr eqα (sy eqβ)
 where
  s : ₂Fin n
  s = take n α
  eq : p (cons s zerō) ~ p (cons s 1̄)
  eq = g s
  eqzerō : ∀{k : ℕ} → ∀(t : ₂Fin k) → cons t zerō k ≡ ₀
  eqzerō ⟨⟩ = refl
  eqzerō (b ∷ s) = eqzerō s
  eq1̄ : ∀{k : ℕ} → ∀(t : ₂Fin k) → cons t 1̄ k ≡ ₁
  eq1̄ ⟨⟩ = refl
  eq1̄ (b ∷ s) = eq1̄ s
  subclaim₀ : α ≡[ succ n ] cons s zerō → p α ~ p (cons s zerō)
  subclaim₀ = pr α (cons s zerō)
  subclaim₁ : α ≡[ succ n ] cons s 1̄ → p α ~ p (cons s zerō)
  subclaim₁ en' = tr (pr α (cons s 1̄) en') (sy eq)
  subclaim₂ : (α ≡[ succ n ] cons s zerō) + (α ≡[ succ n ] cons s 1̄)
  subclaim₂ = cases sclaim₀ sclaim₁ Lemma[b≡₀∨b≡₁]
   where
    sclaim₀ : α n ≡ ₀ → α ≡[ succ n ] cons s zerō
    sclaim₀ αn₀ = ≡[succ] (Lemma[cons-take-≡[]] n α zerō) (αn₀ · (eqzerō s)⁻¹)
    sclaim₁ : α n ≡ ₁ → α ≡[ succ n ] cons s 1̄
    sclaim₁ αn₁ = ≡[succ] (Lemma[cons-take-≡[]] n α 1̄) (αn₁ · (eq1̄ s)⁻¹)
  eqα : p α ~ p (cons s zerō)
  eqα = case subclaim₀ subclaim₁ subclaim₂
  subclaim₃ : β ≡[ succ n ] cons s zerō → p β ~ p (cons s zerō)
  subclaim₃ = pr β (cons s zerō)
  subclaim₄ : β ≡[ succ n ] cons s 1̄ → p β ~ p (cons s zerō)
  subclaim₄ aw' = tr (pr β (cons s 1̄) aw') (sy eq)
  subclaim₅ : (β ≡[ succ n ] cons s zerō) + (β ≡[ succ n ] cons s 1̄)
  subclaim₅ = transport (λ s → (β ≡[ succ n ] cons s zerō) + (β ≡[ succ n ] cons s 1̄))
                        ((Lemma[≡[]-take] en)⁻¹) sclaim₂
   where
    s' : ₂Fin n
    s' = take n β
    sclaim₀ : β n ≡ ₀ → β ≡[ succ n ] cons s' zerō
    sclaim₀ βn₀ = ≡[succ] (Lemma[cons-take-≡[]] n β zerō) (βn₀ · (eqzerō s')⁻¹)
    sclaim₁ : β n ≡ ₁ → β ≡[ succ n ] cons s' 1̄
    sclaim₁ βn₁ = ≡[succ] (Lemma[cons-take-≡[]] n β 1̄) (βn₁ · (eq1̄ s')⁻¹)
    sclaim₂ : (β ≡[ succ n ] cons s' zerō) + (β ≡[ succ n ] cons s' 1̄)
    sclaim₂ = cases sclaim₀ sclaim₁ Lemma[b≡₀∨b≡₁]
  eqβ : p β ~ p (cons s zerō)
  eqβ = case subclaim₃ subclaim₄ subclaim₅


Lemma[LM-modulus] : {X : Set} → (_~_ : X → X → Set) →
        (dec : ∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
        ({x₀ x₁ : X} → x₀ ~ x₁ → x₁ ~ x₀) →
        ({x₀ x₁ x₂ : X} → x₀ ~ x₁ → x₁ ~ x₂ → x₀ ~ x₂) →
        (p : ₂ℕ → X) → (n : ℕ) →
        (∀(α β : ₂ℕ) → α ≡[ n ] β → p α ~ p β) →
         ∀(α β : ₂ℕ) → α ≡[ LM _~_ dec p n ] β → p α ~ p β
Lemma[LM-modulus] _~_ dec sy tr p zero        pr α β e = pr α β e
Lemma[LM-modulus] _~_ dec sy tr p (succ n) pr α β e =
      case claim₀ claim₁ (Lemma[decidable-zerō-1̄] _~_ dec p n)
 where
  claim₀ : (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) → p α ~ p β
  claim₀ h = Lemma[LM-modulus] _~_ dec sy tr p n pr' α β e'
   where
    fact : LM _~_ dec p (succ n) ≡ LM _~_ dec p n
    fact = Lemma[LM]₀ _~_ dec p n h
    e' : α ≡[ LM _~_ dec p n ] β
    e' = transport (λ k → α ≡[ k ] β) fact e
    pr' : ∀(α β : ₂ℕ) → α ≡[ n ] β → p α ~ p β
    pr' = Lemma[succ-zerō-1̄] _~_ dec sy tr p n pr h
  claim₁ : ¬ (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) → p α ~ p β
  claim₁ f = pr α β e'
   where
    fact : LM _~_ dec p (succ n) ≡ succ n
    fact = Lemma[LM]₁ _~_ dec p n f
    e' : α ≡[ succ n ] β
    e' = transport (λ k → α ≡[ k ] β) fact e


Lemma[LM-least] : {X : Set} → (_~_ : X → X → Set) →
        (dec : ∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
        ({x₀ x₁ : X} → x₀ ~ x₁ → x₁ ~ x₀) →
        ({x₀ x₁ x₂ : X} → x₀ ~ x₁ → x₁ ~ x₂ → x₀ ~ x₂) →
        (p : ₂ℕ → X) →
        (n : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n ] β → p α ~ p β) →
        (k : ℕ) → (∀(α β : ₂ℕ) → α ≡[ k ] β → p α ~ p β) →
         LM _~_ dec p n ≤ k
Lemma[LM-least] _~_ dec sy tr p zero        prn k prk = ≤-zero
Lemma[LM-least] _~_ dec sy tr p (succ n) prn k prk = case claim₀ claim₁ claim₂
 where
  claim₀ : (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) →
            LM _~_ dec p (succ n) ≤ k
  claim₀ h = transport (λ l → l ≤ k) (fact ⁻¹) IH
   where
    fact : LM _~_ dec p (succ n) ≡ LM _~_ dec p n
    fact = Lemma[LM]₀ _~_ dec p n h
    prn' : ∀(α β : ₂ℕ) → α ≡[ n ] β → p α ~ p β
    prn' = Lemma[succ-zerō-1̄] _~_ dec sy tr p n prn h
    IH : LM _~_ dec p n ≤ k
    IH = Lemma[LM-least] _~_ dec sy tr p n prn' k prk
  claim₁ : ¬ (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)) →
            LM _~_ dec p (succ n)  ≤ k
  claim₁ f = Lemma[m≮n→n≤m] goal
   where
    fact : LM _~_ dec p (succ n) ≡ succ n
    fact = Lemma[LM]₁ _~_ dec p n f
    goal : k ≮ LM _~_ dec p (succ n)
    goal r = f c₃
     where
      c₀ : k < succ n
      c₀ = transport (λ l → k < l) fact r
      c₁ : k ≤ n
      c₁ = Lemma[m+1≤n+1→m≤n] c₀
      c₂ : ∀(s : ₂Fin n) → (cons s zerō) ≡[ k ] (cons s 1̄)
      c₂ s = Lemma[≡[]-≤] (Lemma[cons-≡[]] s zerō 1̄) c₁
      c₃ : ∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄)
      c₃ s = prk (cons s zerō) (cons s 1̄) (c₂ s)
  claim₂ : decidable (∀(s : ₂Fin n) → p (cons s zerō) ~ p (cons s 1̄))
  claim₂ = Lemma[decidable-zerō-1̄] _~_ dec p n


Lemma[LM-least-modulus] : {X : Set} → (_~_ : X → X → Set) →
        (dec : ∀(x₀ x₁ : X) → decidable (x₀ ~ x₁)) →
        ({x₀ x₁ : X} → x₀ ~ x₁ → x₁ ~ x₀) →
        ({x₀ x₁ x₂ : X} → x₀ ~ x₁ → x₁ ~ x₂ → x₀ ~ x₂) →
        (p : ₂ℕ → X) →
        (n : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n ] β → p α ~ p β) →
        Σ-min \(k : ℕ) → (∀(α β : ₂ℕ) → α ≡[ k ] β → p α ~ p β)
Lemma[LM-least-modulus] _~_ dec sy tr p n pr =
     (LM _~_ dec p n) , (Lemma[LM-modulus] _~_ dec sy tr p n pr) , (Lemma[LM-least] _~_ dec sy tr p n pr)


Lemma[LM-₂ℕ-least-modulus] : {m : ℕ} → ∀(t : ₂ℕ → ₂ℕ) →
     (n : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n ] β → t α ≡[ m ] t β) →
     Σ-min \(k : ℕ) → ∀(α β : ₂ℕ) → α ≡[ k ] β → t α ≡[ m ] t β
Lemma[LM-₂ℕ-least-modulus] {m} = Lemma[LM-least-modulus] (λ α β → α ≡[ m ] β) Lemma[≡[]-decidable] ≡[]-sym ≡[]-trans

Lemma[LM-ℕ-least-modulus] : ∀(p : ₂ℕ → ℕ) →
     (n : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n ] β → p α ≡ p β) →
     Σ-min \(k : ℕ) → ∀(α β : ₂ℕ) → α ≡[ k ] β → p α ≡ p β
Lemma[LM-ℕ-least-modulus] = Lemma[LM-least-modulus] _≡_ ℕ-discrete _⁻¹ _·_

Lemma[LM-₂-least-modulus] : ∀(p : ₂ℕ → ₂) →
     (n : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n ] β → p α ≡ p β) →
     Σ-min \(k : ℕ) → ∀(α β : ₂ℕ) → α ≡[ k ] β → p α ≡ p β
Lemma[LM-₂-least-modulus] = Lemma[LM-least-modulus] _≡_ ₂-discrete _⁻¹ _·_

\end{code}

Identity map is uniformly continuous.

Function composition preserves uniform continuity.

Concatenation maps are uniformly continuous.

\begin{code}

Lemma[id-UC] : uniformly-continuous-₂ℕ id
Lemma[id-UC] m = m , prp , min
 where
  prp : ∀(α β : ₂ℕ) → α ≡[ m ] β → id α ≡[ m ] id β
  prp α β em = em
  min : ∀(n : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n ] β → id α ≡[ m ] id β) → m ≤ n
  min n prn = Lemma[m≮n→n≤m] claim
   where
    claim : n ≮ m
    claim r = c₃ c₂
     where
      α : ₂ℕ
      α = zerō
      β : ₂ℕ
      β = overwrite zerō n ₁
      c₀ : α ≡[ n ] β
      c₀ = Lemma[overwrite-≡[]] zerō n ₁
      c₁ : α ≡[ succ n ] β
      c₁ = Lemma[≡[]-≤] (prn α β c₀) r
      c₂ : α n ≡ β n
      c₂ = Lemma[≡[succ]]₁ c₁
      c₃ : α n ≠ β n
      c₃ = transport (λ b → ₀ ≠ b) ((Lemma[overwrite] zerō n ₁)⁻¹) Lemma[₀≠₁]


Lemma[∘-UC] : ∀(t₀ : ₂ℕ → ₂ℕ) → uniformly-continuous-₂ℕ t₀ →
              ∀(t₁ : ₂ℕ → ₂ℕ) → uniformly-continuous-₂ℕ t₁ →
              uniformly-continuous-₂ℕ (t₀ ∘ t₁)
Lemma[∘-UC] t₀ uc₀ t₁ uc₁ m = Lemma[LM-₂ℕ-least-modulus] (t₀ ∘ t₁) n₁ pr
 where
  n₀ : ℕ
  n₀ = pr₁ (uc₀ m)
  prf₀ : ∀(α β : ₂ℕ) → α ≡[ n₀ ] β → t₀ α ≡[ m ] t₀ β
  prf₀ = pr₁ (pr₂ (uc₀ m))
  n₁ : ℕ
  n₁ = pr₁ (uc₁ n₀)
  prf₁ : ∀(α β : ₂ℕ) → α ≡[ n₁ ] β → t₁ α ≡[ n₀ ] t₁ β
  prf₁ = pr₁ (pr₂ (uc₁ n₀))
  pr : ∀(α β : ₂ℕ) → α ≡[ n₁ ] β → t₀ (t₁ α) ≡[ m ] t₀ (t₁ β)
  pr α β e = (prf₀ (t₁ α) (t₁ β)) (prf₁ α β e)


Lemma[cons-UC] : ∀{n : ℕ} → ∀(s : ₂Fin n) → uniformly-continuous-₂ℕ (cons s)
Lemma[cons-UC] ⟨⟩      m        = Lemma[id-UC] m
Lemma[cons-UC] (b ∷ s) zero        = zero , (λ _ _ _ → ≡[zero]) , (λ _ _ → ≤-zero)
Lemma[cons-UC] (b ∷ s) (succ m) = n , prs , mins
 where
  IH : Σ-min \(n : ℕ) → ∀(α β : ₂ℕ) → α ≡[ n ] β → cons s α ≡[ m ] cons s β
  IH = Lemma[cons-UC] s m
  n : ℕ
  n = pr₁ IH
  prn : ∀(α β : ₂ℕ) → α ≡[ n ] β → cons s α ≡[ m ] cons s β
  prn = pr₁ (pr₂ IH)
  claim₀ : ∀(α β : ₂ℕ) → α ≡[ n ] β → cons s α ≡[ m ] cons s β → 
            ∀(i : ℕ) → i < succ m → cons (b ∷ s) α i ≡ cons (b ∷ s) β i
  claim₀ α β en em zero        r          = refl
  claim₀ α β en em (succ i) (≤-succ r) = Lemma[≡[]-<] em i r
  claim₁ : ∀(α β : ₂ℕ) → α ≡[ n ] β → cons s α ≡[ m ] cons s β → 
            cons (b ∷ s) α ≡[ succ m ] cons (b ∷ s) β
  claim₁ α β en em = Lemma[<-≡[]] (claim₀ α β en em)
  prs : ∀(α β : ₂ℕ) → α ≡[ n ] β → cons (b ∷ s) α ≡[ succ m ] cons (b ∷ s) β
  prs α β en = claim₁ α β en (prn α β en)
  min : ∀(n' : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n' ] β → cons s α ≡[ m ] cons s β) → n ≤ n'
  min = pr₂ (pr₂ IH)
  lemma : ∀{n m : ℕ}{b : ₂}{s : ₂Fin n}{α β : ₂ℕ} →
          cons (b ∷ s) α ≡[ succ m ] cons (b ∷ s) β → cons s α ≡[ m ] cons s β
  lemma {n} {m} {b} {s} {α} {β} esm = Lemma[<-≡[]] em'
   where
    esm' : ∀(i : ℕ) → i < succ m → cons (b ∷ s) α i ≡ cons (b ∷ s) β i
    esm' = Lemma[≡[]-<] esm
    em' : ∀(i : ℕ) → i < m → cons s α i ≡ cons s β i
    em' i r = esm' (succ i) (≤-succ r)
  mins : ∀(n' : ℕ) → (∀(α β : ₂ℕ) → α ≡[ n' ] β → cons (b ∷ s) α ≡[ succ m ] cons (b ∷ s) β) → n ≤ n'
  mins n' pr' = min n' (λ α β en → lemma (pr' α β en))

\end{code}
