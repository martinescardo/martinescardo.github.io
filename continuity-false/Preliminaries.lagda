Chuangjie Xu, 2015

\begin{code}

{-# OPTIONS --without-K #-}

module Preliminaries where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)

\end{code}

Identity function and function composition

\begin{code}

id : {i : Level}{X : Set i} → X → X
id x = x

infixr 30 _∘_ 

_∘_ : {i j k : Level}{X : Set i}{Y : X → Set j}{Z : (x : X) → Y x → Set k} →
      ({x : X} → (y : Y x) → Z x y) → (f : (x : X) → Y x) →
      (x : X) → Z x (f x)
g ∘ f = λ x → g(f x)

\end{code}

Universe polymorphic sigma type

\begin{code}

infixr 3 _,_

record Σ {i j : Level} {A : Set i} (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
   pr₁ : A
   pr₂ : B pr₁

open Σ public

\end{code}

Cartesian products

\begin{code}

infixr 20 _×_

_×_ : {i j : Level} → Set i → Set j → Set(i ⊔ j)
X × Y = Σ \(x : X) → Y

\end{code}

Disjoint union

\begin{code}

infixr 20 _+_

data _+_ (X₀ X₁ : Set) : Set where
  inl : X₀ → X₀ + X₁
  inr : X₁ → X₀ + X₁

case : {X₀ X₁ Y : Set} → (X₀ → Y) → (X₁ → Y) → X₀ + X₁ → Y
case f₀ f₁ (inl x₀) = f₀ x₀
case f₀ f₁ (inr x₁) = f₁ x₁

cases : {X₀ X₁ Y₀ Y₁ : Set} → (X₀ → Y₀) → (X₁ → Y₁) → X₀ + X₁ → Y₀ + Y₁
cases f₀ f₁ (inl x₀) = inl (f₀ x₀)
cases f₀ f₁ (inr x₁) = inr (f₁ x₁)

\end{code}

Empty type:

\begin{code}

data ∅ : Set where

∅-elim : {i : Level}{A : Set i} → ∅ → A
∅-elim ()

¬ : {i : Level} → Set i → Set i
¬ X = X → ∅

\end{code}

Identity type and related lemmas:

\begin{code}

infix  30 _≡_
infixr 40 _·_
infixl 50 _⁻¹

data _≡_ {i : Level} {A : Set i} : A → A → Set i where
  refl : {a : A} → a ≡ a

J : {i j : Level} {A : Set i} (C : (a b : A) → a ≡ b → Set j)
  → ((a : A) → C a a refl)
  → (a b : A) → (p : a ≡ b) → C a b p
J C c a .a refl = c a

_⁻¹ : {i : Level}{A : Set i} → {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

_·_ : {i : Level}{A : Set i} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl · refl = refl

sym-is-inverse : {X : Set} {x y : X} (p : x ≡ y) → refl ≡ p ⁻¹ · p
sym-is-inverse refl = refl

transport : {i j : Level}{X : Set i}{x x' : X} → (Y : X → Set j) → x ≡ x' → Y x → Y x'
transport Y refl y = y

ap : {i j : Level}{X : Set i}{Y : Set j} → ∀(f : X → Y) → {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
ap f refl = refl

pair⁼ : {i j : Level}{X : Set i}{Y : X → Set j}{x x' : X}{y : Y x}{y' : Y x'}
      → (p : x ≡ x') → transport Y p y ≡ y' → (x , y) ≡ (x' , y')
pair⁼ refl refl = refl

\end{code}

Propositions and sets

\begin{code}

hprop : Set → Set
hprop X = (x y : X) → x ≡ y

hset : Set → Set
hset X = {x y : X} → hprop (x ≡ y)

\end{code}

Decidability and discreteness

\begin{code}

decidable : Set → Set
decidable A = A + ¬ A

discrete : Set → Set
discrete A = ∀(a a' : A) → decidable (a ≡ a')

\end{code}

Constancy

\begin{code}

constant : {i j : Level} {X : Set i} {Y : Set j} → (X → Y) → Set(i ⊔ j)
constant f = ∀ x x' → f x ≡ f x'

\end{code}

Natural numbers and booleans

\begin{code}

data ℕ : Set where 
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-injective : ∀{i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-injective = ap pred

ℕ-discrete : discrete ℕ
ℕ-discrete  0        0       = inl refl
ℕ-discrete  0       (succ m) = inr (λ ())
ℕ-discrete (succ n)  0       = inr (λ ())
ℕ-discrete (succ n) (succ m) = step (ℕ-discrete n m)
 where 
  step : decidable(n ≡ m) → decidable (succ n ≡ succ m) 
  step (inl r) = inl (ap succ r)
  step (inr f) = inr (λ s → f (succ-injective s))

data ₂ : Set where
 ₀ : ₂
 ₁ : ₂
{-# BUILTIN BOOL ₂ #-}

₂-discrete : discrete ₂
₂-discrete ₀ ₀ = inl refl 
₂-discrete ₀ ₁ = inr (λ ())
₂-discrete ₁ ₀ = inr (λ ())
₂-discrete ₁ ₁ = inl refl

Lemma[b≡₀∨b≡₁] : ∀{b : ₂} → (b ≡ ₀) + (b ≡ ₁)
Lemma[b≡₀∨b≡₁] {₀} = inl refl
Lemma[b≡₀∨b≡₁] {₁} = inr refl

Lemma[b≠₀→b≡₁] : {b : ₂} → ¬ (b ≡ ₀) → b ≡ ₁
Lemma[b≠₀→b≡₁] {₀} f = ∅-elim (f refl)
Lemma[b≠₀→b≡₁] {₁} f = refl

Lemma[b≠₁→b≡₀] : {b : ₂} → ¬ (b ≡ ₁) → b ≡ ₀
Lemma[b≠₁→b≡₀] {₀} f = refl
Lemma[b≠₁→b≡₀] {₁} f = ∅-elim (f refl)

\end{code}

Less-than relation

\begin{code}

infix 30 _≤_
infix 30 _<_

data _≤_ : ℕ → ℕ → Set where
 ≤-zero : ∀{n : ℕ} → 0 ≤ n
 ≤-succ : ∀{m n : ℕ} → m ≤ n → succ m ≤ succ n

_<_ : ℕ → ℕ → Set
m < n = succ m ≤ n

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}      = ≤-zero
≤-refl {succ n} = ≤-succ ≤-refl

≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-zero     v          = ≤-zero
≤-trans (≤-succ u) (≤-succ v) = ≤-succ (≤-trans u v)

≤-r-succ : {n m : ℕ} → n ≤ m → n ≤ succ m
≤-r-succ ≤-zero     = ≤-zero
≤-r-succ (≤-succ r) = ≤-succ (≤-r-succ r)

Lemma[n≤m+1→n≤m∨n≡m+1] : {n m : ℕ} → n ≤ succ m → (n ≤ m) + (n ≡ succ m)
Lemma[n≤m+1→n≤m∨n≡m+1] {0}      {m}      r = inl ≤-zero
Lemma[n≤m+1→n≤m∨n≡m+1] {succ 0} {0}      r = inr refl
Lemma[n≤m+1→n≤m∨n≡m+1] {succ (succ n)} {0} (≤-succ ())
Lemma[n≤m+1→n≤m∨n≡m+1] {succ n} {succ m} (≤-succ r) = cases c₀ c₁ IH
 where
  c₀ : n ≤ m → succ n ≤ succ m
  c₀ = ≤-succ
  c₁ : n ≡ succ m → succ n ≡ succ (succ m)
  c₁ = ap succ
  IH : (n ≤ m) + (n ≡ succ m)
  IH = Lemma[n≤m+1→n≤m∨n≡m+1] {n} {m} r

Lemma[n≰m→m<n] : {n m : ℕ} → ¬(n ≤ m) → m < n
Lemma[n≰m→m<n] {0}      {m}      f = ∅-elim (f ≤-zero)
Lemma[n≰m→m<n] {succ n} {0}      f = ≤-succ ≤-zero
Lemma[n≰m→m<n] {succ n} {succ m} f = ≤-succ (Lemma[n≰m→m<n] (f ∘ ≤-succ))

Lemma[m≤n∧n≤m→m=n] : ∀{m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
Lemma[m≤n∧n≤m→m=n] {0}      {0}      ≤-zero     ≤-zero      = refl
Lemma[m≤n∧n≤m→m=n] {0}      {succ n} ≤-zero     ()
Lemma[m≤n∧n≤m→m=n] {succ m} {0}      ()         ≤-zero
Lemma[m≤n∧n≤m→m=n] {succ m} {succ n} (≤-succ r) (≤-succ r') = ap succ (Lemma[m≤n∧n≤m→m=n] r r')

\end{code}

Primitive and course-of-value inductions

\begin{code}

primitive-induction : {P : ℕ → Set}
                    → P 0 → (∀ n → P n → P(succ n)) → ∀ n → P n
primitive-induction base step 0        = base
primitive-induction base step (succ n) = step n (primitive-induction base step n)

CoV-induction : {P : ℕ → Set}
              → (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
CoV-induction {P} step n = step n (claim n)
 where
  Q : ℕ → Set
  Q n = ∀ m → succ m ≤ n → P m
  qbase : Q 0
       -- ∀ m → succ m ≤ 0 → P m
  qbase m ()
  qstep : ∀ n → Q n → Q(succ n)
       -- ∀ n → (∀ m → succ m ≤ n → P m) → ∀ m → succ m ≤ succ n → P m
  qstep n qn m (≤-succ r) = step m (λ k u → qn k (≤-trans u r))
  claim : ∀ n → Q n
       -- ∀ n → ∀ m → succ m ≤ n → P m
  claim = primitive-induction qbase qstep

\end{code}

Binary sequences

\begin{code}

₂ℕ : Set
₂ℕ = ℕ → ₂

0̄ : ₂ℕ
0̄ i = ₀
1̄ : ₂ℕ
1̄ i = ₁

infixr 50 _∷_

data ₂Fin : ℕ → Set where
 ⟨⟩ : ₂Fin 0
 _∷_ : {n : ℕ} → ₂ → ₂Fin n → ₂Fin (succ n)

take : (m : ℕ) → ₂ℕ → ₂Fin m
take 0 α = ⟨⟩
take (succ n) α = α 0 ∷ take n (α ∘ succ)

drop : ℕ → ₂ℕ → ₂ℕ
drop 0 α = α
drop (succ m) α = drop m (α ∘ succ)

cons : {m : ℕ} → ₂Fin m → ₂ℕ → ₂ℕ
cons ⟨⟩      α          = α 
cons (h ∷ _) α 0        = h
cons (_ ∷ t) α (succ i) = cons t α i

Lemma[₂Fin-decidability] : (n : ℕ) → (Y : ₂Fin n → Set)
                         → (∀ s → decidable (Y s)) → decidable (∀ s → Y s)
Lemma[₂Fin-decidability] 0 Y decY = cases c₀ c₁ (decY ⟨⟩)
 where
  c₀ : Y ⟨⟩ → ∀ s → Y s
  c₀ y ⟨⟩ = y
  c₁ : ¬ (Y ⟨⟩) → ¬ (∀ s → Y s)
  c₁ f g = f (g ⟨⟩) 
Lemma[₂Fin-decidability] (succ n) Y decY = case c₀ c₁ IH₀
 where
  Y₀ : ₂Fin n → Set
  Y₀ s = Y (₀ ∷ s)
  decY₀ : ∀ s → decidable (Y₀ s)
  decY₀ s = decY (₀ ∷ s)
  IH₀ : decidable (∀ s → Y₀ s)
  IH₀ = Lemma[₂Fin-decidability] n Y₀ decY₀
  Y₁ : ₂Fin n → Set
  Y₁ s = Y (₁ ∷ s)
  decY₁ : ∀ s → decidable (Y₁ s)
  decY₁ s = decY (₁ ∷ s)
  IH₁ : decidable (∀ s → Y₁ s)
  IH₁ = Lemma[₂Fin-decidability] n Y₁ decY₁
  c₀ : (∀ s → Y₀ s) → decidable (∀ s → Y s)
  c₀ y₀ = cases sc₀ sc₁ IH₁
   where
    sc₀ : (∀ s → Y₁ s) → ∀ s → Y s
    sc₀ y₁ (₀ ∷ s) = y₀ s
    sc₀ y₁ (₁ ∷ s) = y₁ s
    sc₁ : ¬ (∀ s → Y₁ s) → ¬ (∀ s → Y s)
    sc₁ f₁ ys = f₁ (λ s → ys (₁ ∷ s))
  c₁ : ¬ (∀ s → Y₀ s) → decidable (∀ s → Y s)
  c₁ f₀ = inr (λ ys → f₀ (λ s → ys (₀ ∷ s)))

\end{code}

"Agree with" relation over infinite sequences, which is an equivalence
relation and a deciable type:

\begin{code}

infixl 10 _≡[_]_

data _≡[_]_ {X : Set} : (ℕ → X) → ℕ → (ℕ → X) → Set where
 ≡[zero] : {α β : ℕ → X} → α ≡[ 0 ] β
 ≡[succ] : {α β : ℕ → X}{n : ℕ} → α ≡[ n ] β → α n ≡ β n → α ≡[ succ n ] β

≡[]-sym : {n : ℕ}{α β : ₂ℕ} → α ≡[ n ] β → β ≡[ n ] α
≡[]-sym {0}      ≡[zero]        = ≡[zero]
≡[]-sym {succ n} (≡[succ] en e) = ≡[succ] (≡[]-sym en) (e ⁻¹)

≡[]-trans : {n : ℕ}{α₀ α₁ α₂ : ₂ℕ} → α₀ ≡[ n ] α₁ → α₁ ≡[ n ] α₂ → α₀ ≡[ n ] α₂
≡[]-trans {0}      ≡[zero]        ≡[zero]          = ≡[zero]
≡[]-trans {succ n} (≡[succ] en e) (≡[succ] en' e') = ≡[succ] (≡[]-trans en en') (e · e')

Lemma[≡[]-cons-take] : {α β : ₂ℕ} → ∀(n : ℕ) → α ≡[ n ] cons (take n α) β
Lemma[≡[]-cons-take] {α} {β} n = lemma₁ n n ≤-refl
 where
  lemma₀ : ∀(α β : ₂ℕ)(m k : ℕ) → succ m ≤ k → α m ≡ cons (take k α) β m
  lemma₀ α β m        0        ()
  lemma₀ α β 0        (succ k) r          = refl
  lemma₀ α β (succ m) (succ k) (≤-succ r) = lemma₀ (α ∘ succ) β m k r
  lemma₁ : ∀(m k : ℕ) → m ≤ k → α ≡[ m ] cons (take k α) β
  lemma₁ 0        k        ≤-zero     = ≡[zero]
  lemma₁ (succ m) 0        ()
  lemma₁ (succ m) (succ k) (≤-succ r) = ≡[succ] (lemma₁ m (succ k) (≤-r-succ r))
                                                (lemma₀ α β m (succ k) (≤-succ r))

Lemma[≡[]-≡[]-take] : {α β γ : ₂ℕ} → ∀(n : ℕ) → α ≡[ n ] β → β ≡[ n ] cons (take n α) γ
Lemma[≡[]-≡[]-take] n en = ≡[]-trans (≡[]-sym en) (Lemma[≡[]-cons-take] n)

Lemma[cons-take-0] : {α β : ₂ℕ} → ∀(n : ℕ) → β 0 ≡ cons (take n α) β n
Lemma[cons-take-0]  0       = refl
Lemma[cons-take-0] (succ n) = Lemma[cons-take-0] n

Lemma[cons-≡[]-≤] : {n m : ℕ}{α β : ₂ℕ} → (s : ₂Fin n) → m ≤ n → cons s α ≡[ m ] cons s β
Lemma[cons-≡[]-≤] _ ≤-zero     = ≡[zero]
Lemma[cons-≡[]-≤] s (≤-succ r) = ≡[succ] (Lemma[cons-≡[]-≤] s (≤-r-succ r)) (lemma s r)
 where
  lemma : {n m : ℕ}{α β : ₂ℕ} → (s : ₂Fin (succ n)) → m ≤ n → cons s α m ≡ cons s β m
  lemma (b ∷ s) ≤-zero     = refl
  lemma (b ∷ s) (≤-succ r) = lemma s r

\end{code}

The type of function extensionality

\begin{code}

Funext : Set₁
Funext = {X : Set} {Y : X → Set} {f g : (x : X) → Y x}
       → (∀(x : X) → f x ≡ g x) → f ≡ g

\end{code}
