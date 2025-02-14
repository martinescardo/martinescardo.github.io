Martin Escardo & Chuangjie Xu, 2015

One of Brouwer's continuity principles is the following

    All functions ₂ℕ → ℕ are uniformly continuous

whose logical formulation is

    ∀(f : ₂ℕ → ℕ). ∃(m : ℕ). ∀(α,β : ₂ℕ). α =[m] β → f α = f β

where α =[m] β expresses that the sequences α and β agree up to the
first m positions.

\begin{code}

{-# OPTIONS --without-K #-}

module UniformContinuity where

open import Preliminaries
open import MainLemma
open import HSet

\end{code}

If function extensionality is available, then for any f : ₂ℕ → ℕ,
the type

  UC(f) = Σ \(n : ℕ) → ∀(α β : ₂ℕ) → α ≡[ n ] β → f α ≡ f β

has a propositional truncation, using the main lemma, because the
type family A(f) : ℕ → Set, defined by

  
  A(f,n) = (α β : ₂ℕ) → α ≡[ n ] β → f α ≡ f β,

satisfies

(1) A(f,n) is a proposition for all n (using funext), and

(2) if A(f,n) holds then A(f,m) is decidable for all m < n.

\begin{code}

A : (₂ℕ → ℕ) → ℕ → Set
A f n = (α β : ₂ℕ) → α ≡[ n ] β → f α ≡ f β

A-hprop : Funext → (f : ₂ℕ → ℕ) → ∀ n → hprop (A f n)
A-hprop funext f n p q = funext (λ α → funext (λ β → funext (λ e → ℕ-hset (p α β e) (q α β e))))

A-≤-decidable : ∀(f : ₂ℕ → ℕ) → ∀ n → A f n → ∀ m → m ≤ n → decidable (A f m)
A-≤-decidable f  0       a _ _ = inl (λ α β _ → a α β ≡[zero])
A-≤-decidable f (succ n) a m r = case c₀ c₁ (Lemma[n≤m+1→n≤m∨n≡m+1] r)
 where
  c₀ : m ≤ n → decidable (A f m)
  c₀ r' = case sc₀' sc₁' claim
   where
    claim : decidable ((s : ₂Fin n) → f (cons s 0̄) ≡ f (cons s 1̄))
    claim = Lemma[₂Fin-decidability] n (λ s → f (cons s 0̄) ≡ f (cons s 1̄))
                                       (λ s → ℕ-discrete (f (cons s 0̄)) (f (cons s 1̄)))
    sc₀ : ((s : ₂Fin n) → f (cons s 0̄) ≡ f (cons s 1̄)) →
          (α β : ₂ℕ) → α ≡[ n ] β → f α ≡ f β
    sc₀ efs α β en = case ssc₀ ssc₁ (₂-discrete (α n) (β n))
     where
      ssc₀ : α n ≡ β n → f α ≡ f β
      ssc₀ e = a α β (≡[succ] en e)
      ssc₁ : ¬ (α n ≡ β n) → f α ≡ f β
      ssc₁ ne = case sssc₀ sssc₁ Lemma[b≡₀∨b≡₁]
       where
        s : ₂Fin n
        s = take n α
        sssc₀ : α n ≡ ₀ → f α ≡ f β
        sssc₀ eα₀ = claim₁ · (efs s) · claim₃ ⁻¹
         where
          eβ₁ : β n ≡ ₁
          eβ₁ = Lemma[b≠₀→b≡₁] (λ eβ₀ → ne (eα₀ · eβ₀ ⁻¹))
          claim₀ : α ≡[ succ n ] cons s 0̄
          claim₀ = ≡[succ] (Lemma[≡[]-cons-take] n) (eα₀ · (Lemma[cons-take-0] n))
          claim₁ : f α ≡ f (cons s 0̄)
          claim₁ = a α (cons s 0̄) claim₀
          claim₂ : β ≡[ succ n ] cons s 1̄
          claim₂ = ≡[succ] (Lemma[≡[]-≡[]-take] n en) (eβ₁ · (Lemma[cons-take-0] n))
          claim₃ : f β ≡ f (cons s 1̄)
          claim₃ = a β (cons s 1̄) claim₂
        sssc₁ : α n ≡ ₁ → f α ≡ f β
        sssc₁ eα₁ = claim₁ · (efs s)⁻¹ · claim₃ ⁻¹
         where
          eβ₀ : β n ≡ ₀
          eβ₀ = Lemma[b≠₁→b≡₀] (λ eβ₁ → ne (eα₁ · eβ₁ ⁻¹))
          claim₀ : α ≡[ succ n ] cons s 1̄
          claim₀ = ≡[succ] (Lemma[≡[]-cons-take] n) (eα₁ · (Lemma[cons-take-0] n))
          claim₁ : f α ≡ f (cons s 1̄)
          claim₁ = a α (cons s 1̄) claim₀
          claim₂ : β ≡[ succ n ] cons s 0̄
          claim₂ = ≡[succ] (Lemma[≡[]-≡[]-take] n en) (eβ₀ · (Lemma[cons-take-0] n))
          claim₃ : f β ≡ f (cons s 0̄)
          claim₃ = a β (cons s 0̄) claim₂
    sc₀' : (∀(s : ₂Fin n) → f (cons s 0̄) ≡ f (cons s 1̄))
         → decidable (∀(α β : ₂ℕ) → α ≡[ m ] β → f α ≡ f β)
    sc₀' ps = A-≤-decidable f n (sc₀ ps) m r'
    sc₁ : ¬ (∀(s : ₂Fin n) → f (cons s 0̄) ≡ f (cons s 1̄)) →
          ¬ (∀(α β : ₂ℕ) → α ≡[ m ] β → f α ≡ f β)
    sc₁ fs pn = fs (λ s → pn (cons s 0̄) (cons s 1̄) (Lemma[cons-≡[]-≤] s r'))
    sc₁' : ¬ (∀(s : ₂Fin n) → f (cons s 0̄) ≡ f (cons s 1̄)) →
           decidable (∀(α β : ₂ℕ) → α ≡[ m ] β → f α ≡ f β)
    sc₁' fs = inr (sc₁ fs)
  c₁ : m ≡ succ n → decidable (A f m)
  c₁ e = inl (transport (A f) (e ⁻¹) a)

\end{code}

Therefore, the truncation of UC(f) exists and hence we have two
formulations of the uniform continuity principle:

\begin{code}

UC : Set
UC = (f : ₂ℕ → ℕ) → ∥Σ (\(n : ℕ) → ∀(α β : ₂ℕ) → α ≡[ n ] β → f α ≡ f β) ∥

CH-UC : Set
CH-UC = (f : ₂ℕ → ℕ) → Σ \(n : ℕ) → ∀(α β : ₂ℕ) → α ≡[ n ] β → f α ≡ f β

\end{code}

Moreover, the above types are logically equivalent.

\begin{code}

Theorem[CH-UC→UC] : CH-UC → UC
Theorem[CH-UC→UC] chuc = λ f → ΣA→∥ΣA∥ (A-≤-decidable f) (chuc f) 

Theorem[UC→CH-UC] : UC → CH-UC
Theorem[UC→CH-UC] uc f = ∥ΣA∥→ΣA (uc f)

\end{code}
