Martin Escardo, Chuangjie Xu, December 2013

Here we prove the main lemma that

    If function extensionality is available, then for any
    type family A : ℕ → U such that
    (1) A(n) is a proposition for all n,
    (2) if A(n) then A(m) is decidable for all i < n,
    the truncation ∥ Σ(n:ℕ).A(n) ∥ exists, and

          ∥ Σ(n:ℕ).A(n) ∥ → Σ(n:ℕ).A(n).

One example of such a predicate A is

    Π(α β : ₂ℕ). α ≡[n] β → f α = f β

for any f : ₂ℕ → ℕ and n : ℕ.

\begin{code}

{-# OPTIONS --without-K #-}

module MainLemma where

open import Preliminaries

\end{code}

For any P : ℕ → U and n : ℕ, if P(m) is decidable for all m ≤ n, then

    (Π(m ≤ n). ¬P(m))  +  (Σ(m ≤ n). P(m)).

\begin{code}

Lemma[≤-dec-∨] : {P : ℕ → Set} →
        ∀(n : ℕ) → (∀(m : ℕ) → m ≤ n → decidable (P m)) →
        (∀ m → m ≤ n → ¬(P m)) + (Σ \m → m ≤ n × P m)
Lemma[≤-dec-∨] {P} 0 dp = case c₀ c₁ (dp 0 ≤-zero)
 where
  c₀ : P 0 → (∀ m → m ≤ 0 → ¬(P m)) + (Σ \m → m ≤ 0 × P m)
  c₀ p0 = inr (0 , ≤-zero , p0)
  c₁ : ¬(P 0) → (∀ m → m ≤ 0 → ¬(P m)) + (Σ \(m : ℕ) → m ≤ 0 × P m)
  c₁ f0 = inl claim
   where
    claim : ∀ m → m ≤ 0 → ¬(P m)
    claim 0 ≤-zero = f0
    claim (succ m) ()
Lemma[≤-dec-∨] {P} (succ n) dp = case c₀ c₁ (dp (succ n) ≤-refl)
 where
  dp' : ∀(m : ℕ) → m ≤ n → decidable (P m)
  dp' m r = dp m (≤-r-succ r)
  c₀ : P(succ n) → (∀ m → m ≤ succ n → ¬(P m)) + (Σ \m → m ≤ succ n × P m)
  c₀ psn = inr (succ n , ≤-refl , psn)
  c₁ : ¬(P(succ n)) → (∀ m → m ≤ succ n → ¬(P m)) + (Σ \m → m ≤ succ n × P m)
  c₁ fsn = cases sc₀ sc₁ (Lemma[≤-dec-∨] n dp')
   where
    sc₀ : (∀ m → m ≤ n → ¬(P m)) → ∀ m → m ≤ succ n → ¬(P m)
    sc₀ fms m r = case (fms m) (λ e → transport (¬ ∘ P) (e ⁻¹) fsn)
                       (Lemma[n≤m+1→n≤m∨n≡m+1] r)
    sc₁ : (Σ \m → m ≤ n × P m) → Σ \m → m ≤ succ n × P m
    sc₁ (m , r , pm) = (m , ≤-r-succ r , pm)

\end{code}

If P(n) implies that P(i) is decidable for all i < n,
then we can find the least m such that P(m).

\begin{code}

Σ-min : (ℕ → Set) → Set
Σ-min P = Σ \(n : ℕ) → (P n) × (∀(n' : ℕ) → P n' → n ≤ n')

μ : {P : ℕ → Set} →
    (n : ℕ) → P n → (∀ i → i ≤ n → decidable (P i)) →
    Σ-min \(m : ℕ) → P m
μ {P} = CoV-induction step
 where

  Q : ℕ → Set
  Q n = P n → (∀ i → i ≤ n → decidable (P i)) → Σ-min \(m : ℕ) → P m

  g : {A : Set} → A + ¬ A → A → A
  g (inl a) _ = a
  g (inr f) a = ∅-elim (f a)

  step : ∀ n → (∀ m → m < n → Q m) → Q n
  step 0        f p0  dp = 0 , g (dp 0 ≤-zero) p0 , (λ _ _ → ≤-zero)
  step (succ n) f psn dp = case c₀ c₁ claim
   where
    dp' : ∀(m : ℕ) → m ≤ n → decidable (P m)
    dp' m r = dp m (≤-r-succ r)
    claim : (∀ m → m ≤ n → ¬(P m)) + (Σ \m → m ≤ n × P m)
    claim = Lemma[≤-dec-∨] n dp'
    c₀ : (∀ m → m ≤ n → ¬(P m)) → Σ-min \(m : ℕ) → P m
    c₀ fm = succ n , g (dp (succ n) ≤-refl) psn , min
     where
      min : ∀ m → P m → succ n ≤ m
      min m pm = Lemma[n≰m→m<n] (λ r → fm m r pm)
    c₁ : (Σ \m → m ≤ n × P m) → Σ-min \(m : ℕ) → P m
    c₁ (m , r , pm) = f m (≤-succ r) pm dpm
     where
      dpm : ∀ k → k ≤ m → decidable (P k)
      dpm k r' = dp k (≤-trans r' (≤-r-succ r))

≤-hprop : {n m : ℕ} → hprop (n ≤ m)
≤-hprop  ≤-zero     ≤-zero    = refl
≤-hprop (≤-succ r) (≤-succ s) = ap ≤-succ (≤-hprop r s)

pairˣ⁼ : {A₀ A₁ : Set}{a₀ a₀' : A₀}{a₁ a₁' : A₁}
       → a₀ ≡ a₀' → a₁ ≡ a₁' → (a₀ , a₁) ≡ (a₀' , a₁')
pairˣ⁼ refl refl = refl

\end{code}

If A : ℕ → U is a hprop-valued predicate such that A(n) implies that
    A(i) is decidable for all i < n, then the truncation ∥ Σ(n:ℕ).A(n)
    ∥ exists, and

          ∥ Σ(n:ℕ).A(n) ∥ → Σ(n:ℕ).A(n).

\begin{code}

∥Σ_∥ : (ℕ → Set) → Set
∥Σ A ∥ = Σ-min A

∥Σ-∥-hprop : Funext →
             (A : ℕ → Set) →
             (∀ n → hprop (A n))
           → hprop ∥Σ A ∥
∥Σ-∥-hprop funext A hA (n , a , r) (n' , a' , r') = goal
 where
  claim₀ : n ≡ n'
  claim₀ = Lemma[m≤n∧n≤m→m=n] (r n' a') (r' n a)
  w : (A n') × (∀ m → A m → n' ≤ m)
  w = transport _ claim₀ (a , r)
  claim₁ : pr₁ w ≡ a'
  claim₁ = hA n' (pr₁ w) a'
  claim₂ : ∀(m : ℕ)(am : A m) → pr₂ w m am ≡ r' m am
  claim₂ m am = ≤-hprop (pr₂ w m am) (r' m am)
  claim₃ : pr₂ w ≡ r'
  claim₃ = funext (λ m → funext (claim₂ m))
          --------      --------
  claim₄ : w ≡ (a' , r')
  claim₄ = pairˣ⁼ claim₁ claim₃
  goal : (n , a , r) ≡ (n' , a' , r')
  goal = pair⁼ claim₀ claim₄

ΣA→∥ΣA∥ : {A : ℕ → Set} →
          (∀ n → A n → ∀ m → m ≤ n → decidable (A m))
        → Σ A → ∥Σ A ∥
ΣA→∥ΣA∥ dA (n , a) = μ n a (dA n a)

∥ΣA∥→ΣA : {A : ℕ → Set}
        → ∥Σ A ∥ → Σ A
∥ΣA∥→ΣA (n , a , _) = (n , a)

∥Σ-∥-elim : {A : ℕ → Set} {P : Set}
          → hprop P → (Σ A → P) → ∥Σ A ∥ → P
∥Σ-∥-elim _ f (n , a , _) = f (n , a)

\end{code}
