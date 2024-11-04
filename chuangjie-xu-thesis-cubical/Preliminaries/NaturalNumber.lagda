Chuangjie Xu 2014

(Changed 9th Nov 2017 to add proof of 0 ‌‌‌≠ 1 without pattern matching
on equalities (and remove built-in NATURAL).)

\begin{code}

{-# OPTIONS --without-K #-}

module Preliminaries.NaturalNumber where

open import Preliminaries.SetsAndFunctions renaming (_+_ to _∨_)
open import Preliminaries.HSet

\end{code}

Natural numbers, basic operations and properties

\begin{code}

data ℕ : Set where 
  zero : ℕ
  succ : ℕ → ℕ

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

succ-injective : ∀{i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-injective = ap pred

rec : {X : Set} → X → (ℕ → X → X) → ℕ → X
rec x f zero        = x
rec x f (succ n) = f n (rec x f n)

succ-is-not-zero : {n : ℕ} → succ n ≠ zero
succ-is-not-zero {n} p = idtofun a ⋆
 where
   f : ℕ → Set
   f zero = ∅
   f (succ n) = ⒈
   a : ⒈ ≡ ∅
   a = ap f p

ℕ-discrete : discrete ℕ
ℕ-discrete  zero        zero       = inl refl
ℕ-discrete  zero       (succ m) = inr λ p → succ-is-not-zero (p ⁻¹)
ℕ-discrete (succ n)  zero       = inr succ-is-not-zero
ℕ-discrete (succ n) (succ m) = step (ℕ-discrete n m)
 where 
  step : decidable(n ≡ m) → decidable (succ n ≡ succ m) 
  step (inl r) = inl (ap succ r)
  step (inr f) = inr (λ s → f (succ-injective s))

ℕ-hset : hset ℕ
ℕ-hset = discrete-is-hset ℕ-discrete

\end{code}

Addition

\begin{code}

infixl 31 _+_

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + (succ m) = succ(n + m)

Lemma[zero+m=m] : ∀(m : ℕ) → zero + m ≡ m
Lemma[zero+m=m] zero = refl
Lemma[zero+m=m] (succ m) = ap succ (Lemma[zero+m=m] m)

Lemma[n+1+m=n+m+1] : ∀(n m : ℕ) → succ n + m ≡ n + succ m
Lemma[n+1+m=n+m+1] n zero = refl
Lemma[n+1+m=n+m+1] n (succ m) = ap succ (Lemma[n+1+m=n+m+1] n m)

Lemma[n+m=m+n] : ∀(n m : ℕ) → n + m ≡ m + n
Lemma[n+m=m+n] n zero        = (Lemma[zero+m=m] n)⁻¹
Lemma[n+m=m+n] n (succ m) = (ap succ (Lemma[n+m=m+n] n m)) · (Lemma[n+1+m=n+m+1] m n)⁻¹

Lemma[n≡zero∨n≡m+1] : ∀(n : ℕ) → (n ≡ zero) ∨ (Σ \(m : ℕ) → n ≡ succ m)
Lemma[n≡zero∨n≡m+1] zero        = inl refl
Lemma[n≡zero∨n≡m+1] (succ n) = inr (n , refl)

\end{code}

Inequality

\begin{code}

infix 30 _≤_
infix 30 _<_
infix 30 _≰_
infix 30 _≮_

data _≤_ : ℕ → ℕ → Set where
 ≤-zero : ∀{n : ℕ} → zero ≤ n
 ≤-succ : ∀{m n : ℕ} → m ≤ n → succ m ≤ succ n

_<_ : ℕ → ℕ → Set
m < n = succ m ≤ n

_≰_ : ℕ → ℕ → Set
m ≰ n = ¬ (m ≤ n)

_≮_ : ℕ → ℕ → Set
m ≮ n = ¬ (m < n)

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero}      = ≤-zero
≤-refl {succ n} = ≤-succ ≤-refl

≤-pred : {n m : ℕ} → succ n ≤ succ m → n ≤ m
≤-pred (≤-succ r) = r

≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-zero     v          = ≤-zero
≤-trans (≤-succ u) (≤-succ v) = ≤-succ (≤-trans u v)

≤-r-succ : {n m : ℕ} → n ≤ m → n ≤ succ m
≤-r-succ ≤-zero     = ≤-zero
≤-r-succ (≤-succ r) = ≤-succ (≤-r-succ r)

Lemma[≤-hprop] : ∀{m n : ℕ} → ∀(r r' : m ≤ n) → r ≡ r'
Lemma[≤-hprop] {zero}      {n}      ≤-zero ≤-zero = refl
Lemma[≤-hprop] {succ m} {zero}      ()     ()
Lemma[≤-hprop] {succ m} {succ n} (≤-succ r) (≤-succ r') = ap ≤-succ (Lemma[≤-hprop] r r')

Lemma[a≤b-decidable] : ∀{a b : ℕ} → decidable (a ≤ b)
Lemma[a≤b-decidable] {zero}      {zero}      = inl ≤-zero
Lemma[a≤b-decidable] {zero}      {succ b} = inl ≤-zero
Lemma[a≤b-decidable] {succ a} {zero}      = inr (λ ())
Lemma[a≤b-decidable] {succ a} {succ b} = cases c₀ c₁ IH
 where
  IH : decidable (a ≤ b)
  IH = Lemma[a≤b-decidable] {a} {b}
  c₀ : a ≤ b → succ a ≤ succ b
  c₀ r = ≤-succ r
  c₁ : ¬ (a ≤ b) → ¬ (succ a ≤ succ b)
  c₁ f sr = ∅-elim (f (≤-pred sr))

Lemma[n≤n+1] : ∀(n : ℕ) → n ≤ succ n
Lemma[n≤n+1] zero        = ≤-zero
Lemma[n≤n+1] (succ n) = ≤-succ (Lemma[n≤n+1] n)

Lemma[m+1≤n+1→m≤n] : ∀{m n : ℕ} → succ m ≤ succ n → m ≤ n
Lemma[m+1≤n+1→m≤n] (≤-succ r) = r

Lemma[m≮n→n≤m] : ∀{m n : ℕ} → m ≮ n → n ≤ m
Lemma[m≮n→n≤m] {m}      {zero}      f = ≤-zero
Lemma[m≮n→n≤m] {zero}      {succ n} f = ∅-elim (f (≤-succ ≤-zero))
Lemma[m≮n→n≤m] {succ m} {succ n} f = ≤-succ (Lemma[m≮n→n≤m] (f ∘ ≤-succ))

Lemma[m<n→m≠n] : ∀{m n : ℕ} → m < n → m ≠ n
Lemma[m<n→m≠n] {zero}      {zero}      ()
Lemma[m<n→m≠n] {zero}      {succ n} r          = λ p → succ-is-not-zero (p ⁻¹)
Lemma[m<n→m≠n] {succ m} {zero}      r          = succ-is-not-zero
Lemma[m<n→m≠n] {succ m} {succ n} (≤-succ r) = λ e → Lemma[m<n→m≠n] r (succ-injective e)

Lemma[a≤b→a+c≤b+c] : ∀(a b c : ℕ) → a ≤ b → a + c ≤ b + c
Lemma[a≤b→a+c≤b+c] a b zero        r = r
Lemma[a≤b→a+c≤b+c] a b (succ c) r = ≤-succ (Lemma[a≤b→a+c≤b+c] a b c r)

Lemma[a<b→a+c<b+c] : ∀(a b c : ℕ) → a < b → a + c < b + c
Lemma[a<b→a+c<b+c] a b c r = transport (λ n → n ≤ b + c) (lemma a c) (Lemma[a≤b→a+c≤b+c] (succ a) b c r)
 where
  lemma : ∀(n m : ℕ) → (succ n) + m ≡ succ (n + m)
  lemma n zero = refl
  lemma n (succ m) = ap succ (lemma n m)

Lemma[a≤a+b] : ∀(a b : ℕ) → a ≤ a + b
Lemma[a≤a+b] a zero = ≤-refl
Lemma[a≤a+b] a (succ b) = ≤-trans (Lemma[a≤a+b] a b) (Lemma[n≤n+1] (a + b))

Lemma[m≤n∧n≤m→m=n] : ∀{m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
Lemma[m≤n∧n≤m→m=n] {zero}      {zero}      ≤-zero     ≤-zero      = refl
Lemma[m≤n∧n≤m→m=n] {zero}      {succ n} ≤-zero     ()
Lemma[m≤n∧n≤m→m=n] {succ m} {zero}      ()         ≤-zero
Lemma[m≤n∧n≤m→m=n] {succ m} {succ n} (≤-succ r) (≤-succ r') = ap succ (Lemma[m≤n∧n≤m→m=n] r r')

Lemma[n≤m+1→n≤m∨n≡m+1] : {n m : ℕ} → n ≤ succ m → (n ≤ m) ∨ (n ≡ succ m)
Lemma[n≤m+1→n≤m∨n≡m+1] {zero}      {m}      r = inl ≤-zero
Lemma[n≤m+1→n≤m∨n≡m+1] {succ zero} {zero}      r = inr refl
Lemma[n≤m+1→n≤m∨n≡m+1] {succ (succ n)} {zero} (≤-succ ())
Lemma[n≤m+1→n≤m∨n≡m+1] {succ n} {succ m} (≤-succ r) = cases c₀ c₁ IH
 where
  c₀ : n ≤ m → succ n ≤ succ m
  c₀ = ≤-succ
  c₁ : n ≡ succ m → succ n ≡ succ (succ m)
  c₁ = ap succ
  IH : (n ≤ m) ∨ (n ≡ succ m)
  IH = Lemma[n≤m+1→n≤m∨n≡m+1] {n} {m} r

Lemma[n≰m→m<n] : {n m : ℕ} → ¬(n ≤ m) → m < n
Lemma[n≰m→m<n] {zero}      {m}      f = ∅-elim (f ≤-zero)
Lemma[n≰m→m<n] {succ n} {zero}      f = ≤-succ ≤-zero
Lemma[n≰m→m<n] {succ n} {succ m} f = ≤-succ (Lemma[n≰m→m<n] (f ∘ ≤-succ))

Lemma[≤-Σ] : ∀(a b : ℕ) → a ≤ b → Σ \(c : ℕ) → a + c ≡ b
Lemma[≤-Σ] zero b ≤-zero = b , Lemma[zero+m=m] b
Lemma[≤-Σ] (succ a) zero ()
Lemma[≤-Σ] (succ a) (succ b) (≤-succ r) = c , (Lemma[n+1+m=n+m+1] a c) · (ap succ eq)
 where
  c : ℕ
  c = pr₁ (Lemma[≤-Σ] a b r)
  eq : a + c ≡ b
  eq = pr₂ (Lemma[≤-Σ] a b r)

\end{code}

Maximum

\begin{code}

max : ℕ → ℕ → ℕ
max zero m = m
max n zero = n
max (succ n) (succ m) = succ (max n m)

max-spec₀ : (n m : ℕ) → n ≤ max n m
max-spec₀ zero        m        = ≤-zero
max-spec₀ (succ n) zero        = ≤-refl
max-spec₀ (succ n) (succ m) = ≤-succ (max-spec₀ n m)

max-spec₁ : (n m : ℕ) → m ≤ max n m
max-spec₁ zero        m        = ≤-refl
max-spec₁ (succ n) zero        = ≤-zero
max-spec₁ (succ n) (succ m) = ≤-succ (max-spec₁ n m)

\end{code}

The type of "there exists a least number n such that P n"

\begin{code}

Σ-min : (ℕ → Set) → Set
Σ-min P = Σ \(n : ℕ) → (P n) × (∀(n' : ℕ) → P n' → n ≤ n')

re-pair : {P : ℕ → Set} → Σ-min P → Σ P
re-pair (n , p , _) = (n , p)

Σ-min-≡ : {P : ℕ → Set}{w₀ w₁ : Σ-min P} → w₀ ≡ w₁ → re-pair w₀ ≡ re-pair w₁
Σ-min-≡ = ap re-pair

\end{code}

Primitive and course-of-value inductions

\begin{code}

primitive-induction : {P : ℕ → Set}
                    → P zero → (∀ n → P n → P(succ n)) → ∀ n → P n
primitive-induction base step zero        = base
primitive-induction base step (succ n) = step n (primitive-induction base step n)

CoV-induction : {P : ℕ → Set}
              → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
CoV-induction {P} step n = step n (claim n)
 where
  Q : ℕ → Set
  Q n = ∀ m → succ m ≤ n → P m
  qbase : Q zero
       -- ∀ m → succ m ≤ zero → P m
  qbase m ()
  qstep : ∀ n → Q n → Q(succ n)
       -- ∀ n → (∀ m → succ m ≤ n → P m) → ∀ m → succ m ≤ succ n → P m
  qstep n qn m (≤-succ r) = step m (λ k u → qn k (≤-trans u r))
  claim : ∀ n → Q n
       -- ∀ n → ∀ m → succ m ≤ n → P m
  claim = primitive-induction qbase qstep

\end{code}
