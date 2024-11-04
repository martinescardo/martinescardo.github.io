{-# OPTIONS --without-K #-}

\begin{code} 

module preliminaries where

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

J : {X : Set} → (A : {x y : X} → x ≡ y → Set)
   → ({x : X} → A (refl {X} {x})) →  {x y : X} (p : x ≡ y) → A p
J A φ refl = φ

weak-J : {X : Set} (B : (x y : X) → Set) 
 → ({x : X} → B x x) → {x y : X} → x ≡ y → B x y
weak-J {X} B = J A
 where
  A : {x y : X} → x ≡ y → Set
  A {x} {y} p = B x y

trans : {X : Set} → {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans {X} {x} {y} {z} r = weak-J (λ x y → (z : X) → y ≡ z → x ≡ z) (λ z s → s) r z

sym : {X : Set} → {x y : X} → x ≡ y → y ≡ x
sym {X} {x} {y} = weak-J (λ x y → y ≡ x) refl 

cong : {X Y : Set} → (f : X → Y) → {x x' : X} → x ≡ x' → f x ≡ f x'
cong {X} {Y} f = weak-J(λ x x' → f x ≡ f x') refl

sym-is-inverse : {X : Set} → {x y : X} → (p : x ≡ y) → refl ≡ trans (sym p) p
sym-is-inverse = J (λ p → refl ≡ trans (sym p) p) refl

data Σ {X : Set} (Y : X → Set) : Set where
     _,_ : (x₀ : X) → Y x₀ → Σ \(x : X) → Y x


π₀ : {X : Set} {Y : X → Set} → (Σ \(x : X) → Y x) → X
π₀(x , y) = x

π₁ : {X : Set} {Y : X → Set} → (z : Σ \(x : X) → Y x) → Y(π₀ z)
π₁(x , y) = y

data ∅ : Set where

∅-elim : {X : Set} → ∅ → X
∅-elim () 

data _+_ (X₀ X₁ : Set) : Set where
 in₀ : X₀ → X₀ + X₁
 in₁ : X₁ → X₀ + X₁

equality-cases : {X₀ X₁ : Set} → {A : Set} → 
 (y : X₀ + X₁) → ((x₀ : X₀) → y ≡ in₀ x₀ → A) → ((x₁ : X₁) → y ≡ in₁ x₁ → A) → A
equality-cases (in₀ x₀) f₀ f₁ = f₀ x₀ refl
equality-cases (in₁ x₁) f₀ f₁ = f₁ x₁ refl

\end{code}
