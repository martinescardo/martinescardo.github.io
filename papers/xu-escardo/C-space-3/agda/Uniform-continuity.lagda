Chuangjie Xu, 2012

\begin{code}

module Uniform-continuity where

open import Mini-library
open import Setoid


constant : {A B : Setoid} → E-map A B → Set
constant {A , _} {B , _≈_ , _} (f , _) = ∀(a a' : A) → f a ≈ f a'

Lemma[unit-constant] : {A : Setoid} → ∀(u : E-map A E⒈) → constant {A} {E⒈} u
Lemma[unit-constant] {A} (u , _) x x' = singleton (u x) (u x')


_≣_≣_ : ₂ℕ → ℕ → ₂ℕ → Set
α ≣ n ≣ β = ∀(i : ℕ) → i < n → α i ≡ β i

Lemma[≣_≣-≤] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β →
                       ∀(m : ℕ) → m ≤ n → α ≣ m ≣ β
Lemma[≣_≣-≤] n α β awn m r i l = awn i (Lemma[a<b≤c→a<c] l r)

Lemma[≣_≣-take] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β → take n α ≡ take n β
Lemma[≣_≣-take] 0        α β e = refl
Lemma[≣_≣-take] (succ n) α β e = Lemma[Vec-≡] claim₀ claim₁
 where
  claim₀ : α 0 ≡ β 0
  claim₀ = e 0 (≤-succ ≤-zero)
  e' : (α ∘ succ) ≣ n ≣ (β ∘ succ)
  e' i r = e (succ i) (≤-succ r)
  claim₁ : take n (α ∘ succ) ≡ take n (β ∘ succ)
  claim₁ = Lemma[≣_≣-take] n (α ∘ succ) (β ∘ succ) e'


Lemma[≣_≣-drop] : ∀(n m : ℕ) → ∀(α β : ₂ℕ) → α ≣ n + m ≣ β →
                   drop n α ≣ m ≣ drop n β
Lemma[≣_≣-drop] n m α β e i i<m = trans (trans (lemma n i α) claim)
                                        (sym (lemma n i β))
 where
  i+n<n+m : i + n < n + m
  i+n<n+m = subst {ℕ} {λ x → i + n < x}
                  (Lemma[n+m=m+n] m n) (Lemma[a<b→a+c<b+c] i m n i<m)
  claim : α (i + n) ≡ β (i + n)
  claim = e (i + n) i+n<n+m
  lemma : ∀(n i : ℕ) → ∀(α : ₂ℕ) → drop n α i ≡ α (i + n)
  lemma 0        i α = refl
  lemma (succ n) i α = lemma n i (α ∘ succ)

Lemma[drop-≣] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ β → drop n α ≣ drop n β
Lemma[drop-≣] 0        α β e = e
Lemma[drop-≣] (succ n) α β e = Lemma[drop-≣] n (α ∘ succ) (β ∘ succ)
                                               (λ i → e (succ i))
Lemma[≣_≣-cons] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β → α n ≡ β n → α ≣ succ n ≣ β
Lemma[≣_≣-cons] 0        α β awn eq 0        r           = eq
Lemma[≣_≣-cons] 0        α β awn eq (succ i) (≤-succ ())
Lemma[≣_≣-cons] (succ n) α β awn eq 0 r                  = awn 0 (≤-succ ≤-zero)
Lemma[≣_≣-cons] (succ n) α β awn eq (succ i) (≤-succ r)  =
  Lemma[≣ n ≣-cons] (α ∘ succ) (β ∘ succ) (λ j z → awn (succ j) (≤-succ z)) eq i r


locally-constant : {A : Setoid} → E-map E₂ℕ A → Set
locally-constant {A , _~_ , _} (f , _) = ∃ \(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β → f α ~ f β


uniformly-continuous-₂ : E-map E₂ℕ E₂ → Set
uniformly-continuous-₂ = locally-constant {E₂}


uniformly-continuous-ℕ : E-map E₂ℕ Eℕ → Set
uniformly-continuous-ℕ = locally-constant {Eℕ}


uniformly-continuous-₂ℕ : E-map E₂ℕ E₂ℕ → Set
uniformly-continuous-₂ℕ (f , _) = ∀(m : ℕ) → ∃ \(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β → f α ≣ m ≣ f β


Lemma[id-UC] : uniformly-continuous-₂ℕ (E-id {E₂ℕ})
Lemma[id-UC] m = m , (λ α β z → z)


Lemma[◎-UC] : ∀(t : E-map E₂ℕ E₂ℕ) → uniformly-continuous-₂ℕ t →
               ∀(t' : E-map E₂ℕ E₂ℕ) → uniformly-continuous-₂ℕ t' →
                uniformly-continuous-₂ℕ (t ◎ t')
Lemma[◎-UC] (t , _) uc (t' , _) uc' m = n , prf
 where
  k : ℕ
  k = ∃-witness (uc m)
  n : ℕ
  n = ∃-witness (uc' k)
  e : ∀(α β : ₂ℕ) → α ≣ k ≣ β → t α ≣ m ≣ t β
  e = ∃-elim (uc m)
  e' : ∀(α β : ₂ℕ) → α ≣ n ≣ β → t' α ≣ k ≣ t' β
  e' = ∃-elim (uc' k)
  prf : ∀(α β : ₂ℕ) → α ≣ n ≣ β → t (t' α) ≣ m ≣ t (t' β)
  prf α β awn = e (t' α) (t' β) (e' α β awn)


uniformly-continuous : (₂ℕ → ℕ) → Set
uniformly-continuous f = ∃ \(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β → f α ≡ f β

\end{code}