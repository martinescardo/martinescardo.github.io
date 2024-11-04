\begin{code}

{-# OPTIONS --without-K #-}

module mini-library where

id : {X : Set} → X → X
id x = x

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)

infixl 30 _∘_

record Σ {I : Set} (X : I → Set) : Set where
  constructor _,_
  field
   i : I
   x : X i

π₀ : {I : Set} {X : I → Set} → (Σ \(i : I) → X i) → I
π₀(i , x) = i

π₁ : {I : Set} {X : I → Set} → (pair : Σ \(i : I) → X i) → X(π₀ pair)
π₁(i , x) = x

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

infixl 5 _,_
infixl 5 _×_
infixl 5 _⇔_

_⇔_ : Set → Set → Set
X ⇔ Y = (X → Y) × (Y → X)

data ∅ : Set where

∅-elim : {X : Set} → ∅ → X
∅-elim ()

data _+_ (X₀ X₁ : Set) : Set where
 in₀ : X₀ → X₀ + X₁
 in₁ : X₁ → X₀ + X₁

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

J : {X : Set} (A : {x y : X} → x ≡ y → Set)
   → ({x : X} → A (refl {X} {x})) → {x y : X} (p : x ≡ y) → A p
J A φ refl = φ

\end{code}

The version of J introduced by Paulin-Mohring can be defined using J,
as is well known, but we define using pattern matching for simplicity:

\begin{code}

J' : {X : Set} (x : X) → (A : {y : X} → x ≡ y → Set)
   → A (refl {X} {x}) → {y : X} (p : x ≡ y) → A p
J' x A φ refl = φ

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

ap : {X Y : Set} → (f : X → Y) → {x x' : X} → x ≡ x' → f x ≡ f x'
ap {X} {Y} f = weak-J(λ x x' → f x ≡ f x') refl

transport : {X : Set} {P : X → Set} → {x y : X} → x ≡ y → P x → P y
transport {X} {P} = weak-J (λ x y → P x → P y) (λ p → p)

\end{code}

The above is the traditional notation. The homotopy theory notation is
this:

\begin{code}

_•_ : {X : Set} → {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p • q = trans p q

_⁻¹ : {X : Set} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = sym p

infixr 6 _≡_
infixr 7 _•_

\end{code}

Some very simple lemmas:

\begin{code}

sym-is-inverse : {X : Set} {x y : X} (p : x ≡ y) → refl ≡ p ⁻¹ • p
sym-is-inverse = J (λ p → refl ≡ (p ⁻¹) • p) refl

sym-sym-trivial : {X : Set} {x y : X} (p : x ≡ y) → p ≡ (p ⁻¹)⁻¹
sym-sym-trivial = J (λ p → p ≡ (p ⁻¹)⁻¹) refl

refl-is-right-id : {X : Set} {x y : X} (p : x ≡ y) → p ≡ p • refl
refl-is-right-id = J (λ q → q ≡ q • refl) refl

refl-is-left-id : {X : Set} {x y : X} (p : x ≡ y) → p ≡ refl • p
refl-is-left-id = J (λ q → q ≡ refl • q) refl

ap-id-is-id : {X : Set} {x y : X} (p : x ≡ y) → p ≡ ap id p
ap-id-is-id = J (λ p → p ≡ ap id p) refl

\end{code}

The following is quite involved without pattern matching; see
Nils Anders Danielsson's Agda library.

\begin{code}

Σ-≡ : {X : Set} {Y : X → Set} (x x' : X) (y : Y x) (y' : Y x')
     → (p : x ≡ x') → transport p y ≡ y' → _≡_ {Σ \x → Y x} (x , y) (x' , y')
Σ-≡ .x' x' .y y refl refl = refl

\end{code}

This notational trick is also from Nils Anders Danielsson.

\begin{code}

_≡⟨_⟩_ : {X : Set} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p • q

_∎ : {X : Set} (x : X) → x ≡ x
_∎ _ = refl

infix  1 _∎
infixr 0 _≡⟨_⟩_

\end{code}

Two more simple lemmas:

\begin{code}

sym-trans : {X : Set} {x y z : X} (p : x ≡ y) (q : y ≡ z) → (q ⁻¹) • (p ⁻¹) ≡ (p • q)⁻¹
sym-trans {X} {x} {y} {z} p = J' y  (λ q → (q ⁻¹) • (p ⁻¹) ≡ (p • q)⁻¹) trivial
   where
    trivial : refl • (p ⁻¹) ≡ (p • refl)⁻¹
    trivial = refl • (p ⁻¹) ≡⟨ (refl-is-left-id (p ⁻¹))⁻¹ ⟩
              p ⁻¹          ≡⟨ ap sym (refl-is-right-id p) ⟩
              (p • refl)⁻¹  ∎

trans-assoc : {X : Set} {x y z w : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p • q) • r ≡ p • (q • r)
trans-assoc {X} {x} {y} {z} {w} p q = J' z (λ r → (p • q) • r ≡ p • (q • r)) (trivial ⁻¹)
   where
    trivial = p • (q • refl) ≡⟨ ap (λ q → p • q) ((refl-is-right-id q)⁻¹) ⟩
              p • q          ≡⟨ refl-is-right-id _ ⟩
              (p • q) • refl ∎

\end{code}

\begin{code}

data ₂ : Set where
 ₀ : ₂
 ₁ : ₂

\end{code}
