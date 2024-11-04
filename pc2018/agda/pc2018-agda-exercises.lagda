Martin Escardo 2018.

Agda exercises for PC'18.
https://www.mathematik.uni-muenchen.de/~schwicht/pc18.php

\begin{code}

module pc2018-agda-exercises where

Ķ : {X Y : Set} → X → (Y → X)
Ķ x y = x

Ş : {X Y Z : Set} → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

rec : {X : Set} → (X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f(rec f x n)

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

data Σ {X : Set} (Y : X → Set) : Set where
  _,_ : (x : X) (y : Y x) → Σ {X} Y

π₀ : {X : Set} {Y : X → Set} → (Σ \(x : X) → Y x) → X
π₀(x , y) = x

π₁ : {X : Set} {Y : X → Set} → (t : Σ \(x : X) → Y x) → Y(π₀ t)
π₁(x , y) = y

_×_ : Set → Set → Set
A × B = Σ \(_ : A) → B

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

sym : {X : Set} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

trans : {X : Set} → {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans p refl = p

cong : {X Y : Set} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

cong₂ : {X Y Z : Set} → (f : X → Y → Z)
      → {x₀ x₁ : X}{y₀ y₁ : Y} → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl

_≡⟨_⟩_ : {X : Set} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : {X : Set} (x : X) → x ≡ x
_∎ _ = refl

infix  1 _∎
infixr 0 _≡⟨_⟩_

data type : Set where
  ι   : type
  _⇒_ : type → type → type

\end{code}

\begin{code}

data T : (σ : type) → Set where
 Zero : T ι
 Succ : T(ι ⇒ ι)
 Rec  : {σ : type}     → T((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 K    : {σ τ : type}   → T(σ ⇒ τ ⇒ σ)
 S    : {ρ σ τ : type} → T((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
 _·_  : {σ τ : type}   → T(σ ⇒ τ) → T σ → T τ

data is-weak-normal : {σ : type} → T σ → Set where
 Zero : is-weak-normal Zero
 Succ : is-weak-normal Succ
 Rec₀ : {σ : type} → is-weak-normal (Rec {σ})
 Rec₁ : {σ : type} (t : T (σ ⇒ σ)) → is-weak-normal (Rec {σ} · t)
 Rec₂ : {σ : type} (t : T (σ ⇒ σ)) (u : T σ) → is-weak-normal (Rec {σ} · t · u)
 K₀   : {σ τ : type} → is-weak-normal (K {σ} {τ})
 K₁   : {σ τ : type} (t : T σ) → is-weak-normal (K {σ} {τ} · t)
 S₀   : {ρ σ τ : type} → is-weak-normal (S {ρ} {σ} {τ})
 S₁   : {ρ σ τ : type} (t : T (ρ ⇒ σ ⇒ τ)) → is-weak-normal (S {ρ} {σ} {τ} · t)
 S₂   : {ρ σ τ : type} (t : T (ρ ⇒ σ ⇒ τ)) (u : T (ρ ⇒ σ)) → is-weak-normal (S {ρ} {σ} {τ} · t · u)


data _↦_ : {σ : type} → T σ → T σ → Set where
 Rec₀  : {σ : type} (t : T (σ ⇒ σ)) (u : T σ)
       → Rec · t · u · Zero ↦ u

 Rec₁  : {σ : type} (t : T (σ ⇒ σ)) (u : T σ) (v : T ι)
       → Rec · t · u · (Succ · v) ↦ t · (Rec · t · u · v)

 K : {σ τ : type} (t : T σ) (u : T τ)
   → K · t · u ↦ t

 S  : {ρ σ τ : type} (t : T (ρ ⇒ σ ⇒ τ)) (u : T (ρ ⇒ σ)) (v : T ρ)
    → S · t · u · v ↦ t · v · (u · v)

 A : {σ τ : type} (t t' : T(σ ⇒ τ)) (u : T σ) (w : T τ)
  → t ↦ t'
  → t · u ↦ t' · u

data _⇓_ : {σ : type} → T σ → T σ → Set where
 Refl : {σ : type} (t : T σ) → is-weak-normal t → t ⇓ t

 Succ : (t n : T ι)
      → t ⇓ n
      → Succ · t ⇓ Succ · n

 Trans : {σ : type} (t u v : T σ) → t ↦ u → u ⇓ v → t ⇓ v

 A : {σ τ : type} (t t' : T(σ ⇒ τ)) (u : T σ) (w : T τ)
  → t ⇓ t'
  → t' · u ⇓ w
  → t · u ⇓ w

eval-deterministic : {σ : type} (t u v : T σ) → t ⇓ u → t ⇓ v → u ≡ v
eval-deterministic = {!!}

data is-numeral : T ι → Set where
 Zero : is-numeral Zero
 Succ : (n : T ι) → is-numeral n → is-numeral (Succ · n)

eval-is-numeral : (t n : T ι) → t ⇓ n → is-numeral n
eval-is-numeral = {!!}

\end{code}

Tait's argument:

\begin{code}

eval-total : (t : T ι) → Σ \(n : T ι) → t ⇓ n
eval-total = γ {ι}
 where
  is-computable : {σ : type} → T σ → Set
  is-computable {ι} t        = Σ \(n : T ι) → t ⇓ n
  is-computable {σ ⇒ τ} t  = (u : T σ) → is-computable u → is-computable (t · u)

  eval-computable : {σ : type} {t u : T σ} → t ↦ u
                 → is-computable u → is-computable t
  eval-computable = {!!}

  Zero-computable : is-computable Zero
  Zero-computable = Zero , {!!}
  Succ-computable : is-computable Succ
  Succ-computable u (n , e) = Succ · n , Succ u n e
  Rec-computable : {σ : type} → is-computable (Rec {σ})
  Rec-computable = {!!}
  K-computable : {σ τ : type} → is-computable (K {σ} {τ})
  K-computable = {!!}
  S-computable : {ρ σ τ : type} → is-computable (S {ρ} {σ} {τ})
  S-computable = {!!}

  γ : {σ : type} (t : T σ) → is-computable t
  γ Zero = Zero-computable
  γ Succ = Succ-computable
  γ Rec = Rec-computable
  γ K = K-computable
  γ S = S-computable
  γ (t · u) = c
   where
    IH₀ : is-computable u
    IH₀ = γ u
    IH₁ : ∀ u → is-computable u → is-computable (t · u)
    IH₁ = γ t
    c : is-computable (t · u)
    c = IH₁ u IH₀

Set⟦_⟧ : type → Set
Set⟦ ι ⟧ = ℕ
Set⟦ σ ⇒ τ ⟧ = Set⟦ σ ⟧ → Set⟦ τ ⟧

⟦_⟧ : {σ : type} → T σ → Set⟦ σ ⟧
⟦ Zero ⟧  = zero
⟦ Succ ⟧  = succ
⟦ Rec ⟧   = rec
⟦ K ⟧     = Ķ
⟦ S ⟧     = Ş
⟦ t · u ⟧ = ⟦ t ⟧ ⟦ u ⟧

eval-sound-base : (σ : type) (t u : T σ) → t ⇓ u → ⟦ t ⟧ ≡ ⟦ u ⟧
eval-sound-base = {!!}

eval-complete-base : (t : T ι) → Σ \(n : ℕ) → ⟦ t ⟧ ≡ n
eval-complete-base = {!!}

\end{code}

\begin{code}

infixl 0 _,_
infixr 2 _⇒_
infixl 2 _·_
infix  1 _⇓_
infix  1 _↦_
infix  3 _≡_

\end{code}
