Chuangjie Xu 2013

(Changed 9th Nov 2017. We removed the inductive definition of the
identity type ≡. We now import Id, renamed to ≡, from Vezzosi's
cubical development. We also need to replace all the uses of pattern
matching on refl by uses of J.)

\begin{code}

{-# OPTIONS --without-K #-}

module Preliminaries.SetsAndFunctions where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)

\end{code}

Identity function and function composition

\begin{code}

id : {i : Level}{X : Set i} → X → X
id x = x

infixl 31 _∘_ 

_∘_ : {i j k : Level}{X : Set i}{Y : X → Set j}{Z : (x : X) → Y x → Set k} →
      ({x : X} → (y : Y x) → Z x y) → (f : (x : X) → Y x) →
      (x : X) → Z x (f x)
g ∘ f = λ x → g(f x)

\end{code}

Subset relation

\begin{code}

Subset : {i : Level} → Set i → Set(lsuc i)
Subset {i} X = X → Set i

_∈_ : {i : Level}{X : Set i} → X → Subset X → Set i
x ∈ A = A x

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

Cartesian products and conjunctions are defined using Σ types.

\begin{code}

infixr 20 _×_

_×_ : {i j : Level} → Set i → Set j → Set(i ⊔ j)
X × Y = Σ \(x : X) → Y

\end{code}

Identity type and related lemmas:

\begin{code}

-- infix  3zero _≡_
infixr 40 _·_
infixl 50 _⁻¹

open import PathPrelude public using () renaming (Id to _≡_ ; J to J'')
open import Id public using () renaming (reflId to refl)

J : ∀ {i} {j} {X : Set i} (A : {x y : X} → x ≡ y → Set j)
   → ({x : X} → A (refl {_} {X} {x})) → {x y : X} (p : x ≡ y) → A p
J A φ {x} = J'' (λ y p → A {x} {y} p) φ

weak-J : ∀ {i} {j} {X : Set i} (B : (x y : X) → Set j) 
 → ({x : X} → B x x) → {x y : X} → x ≡ y → B x y
weak-J {i} {j} {X} B = J A
 where
  A : {x y : X} → x ≡ y → Set j
  A {x} {y} p = B x y

weak-J-comp : ∀ {i} {j} {X : Set i} (B : (x y : X) → Set j) 
 → (φ : {x : X} → B x x) {x : X} → weak-J B φ {x} {x} refl ≡ φ 
weak-J-comp B φ = refl

_⁻¹ : {i : Level}{A : Set i} → {x y : A} → x ≡ y → y ≡ x
_⁻¹ {i} {X} {x} {y} = weak-J (λ x y → y ≡ x) refl 

_·_ : {i : Level}{A : Set i} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_·_ {i} {X} {x} {y} {z} r = weak-J (λ x y → (z : X) → y ≡ z → x ≡ z) (λ z s → s) r z

transport : {i j : Level}{X : Set i}{x x' : X} → (Y : X → Set j) → x ≡ x' → Y x → Y x'
transport {i} {j} {X} Y = weak-J (λ x y → Y x → Y y) (λ p → p)

idtofun : ∀ {i} {X Y : Set i} → X ≡ Y → X → Y
idtofun = weak-J (λ X Y → X → Y) id

transport² : {i j k : Level} {X : Set i} (Y : X → Set j) (Z : (x : X) → Y x → Set k)
             {x x' : X} {y : Y x} → (p : x ≡ x') → Z x y → Z x' (transport Y p y)
transport² {i} {j} {k} {X} Y Z p = f p
 where
   A : {x x' : X} → (p : x ≡ x') → Set (j ⊔ k)
   A {x} {x'} p = {y : Y x} → Z x y → Z x' (transport Y p y)
   f : {x x' : X} → (p : x ≡ x') {y : Y x} → Z x y → Z x' (transport Y p y)
   f = J A id

ap : {i j : Level}{X : Set i}{Y : Set j} → ∀(f : X → Y) → {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
ap f = weak-J(λ x x' → f x ≡ f x') refl

fun-ap : {i j : Level}{X : Set i}{Y : X → Set j} → ∀{f g : (x : X) → Y x} → f ≡ g → ∀(x : X) → f x ≡ g x
fun-ap r x = ap (λ h → h x) r

apd : {i j : Level} {X : Set i} {Y : X → Set j} 
     → (f : (x : X) → Y x) {x₀ x₁ : X} (p : x₀ ≡ x₁)
     → transport Y p (f x₀) ≡ f x₁
apd {i} {j} {X} {Y} f = J (λ {x} {x'} p → transport Y p (f x) ≡ f x') λ {x} → refl

apd² : {i j k : Level} {X : Set i} {Y : X → Set j} {Z : Set k}
       {x₀ x₁ : X} {y₀ : Y x₀} {y₁ : Y x₁}
     → (f : (x : X) → Y x → Z) → (p : x₀ ≡ x₁) → transport Y p y₀ ≡ y₁
     → f x₀ y₀ ≡ f x₁ y₁
apd² {i} {j} {k} {X} {Y} {Z} f p = φ p
 where
   φ : {x x' : X}
      → (p : x ≡ x') {y : Y x}{y' : Y x'} → transport Y p y ≡ y' → f x y ≡ f x' y'
   φ {x} {x'} = J A λ {x y y'} → ap (f x) 
    where
      A : {x x' : X} → x ≡ x' → Set (j ⊔ k)
      A {x} {x'} p = {y : Y x} {y' : Y x'} → transport Y p y ≡ y' → f x y  ≡ f x' y'


sym-is-inverse : ∀ {i} {X : Set i} {x y : X} (p : x ≡ y) → refl ≡ p ⁻¹ · p
sym-is-inverse = J (λ p → refl ≡ (p ⁻¹) · p) refl

pair⁼ : {i j : Level}{X : Set i}{Y : X → Set j}{x x' : X}{y : Y x}{y' : Y x'}
      → (p : x ≡ x') → transport Y p y ≡ y' → (x , y) ≡ (x' , y')
pair⁼ = apd² (λ x y → (x , y)) 

ap² : {i j k : Level} {X : Set i} {Y : Set j} {Z : Set k} (f : X → Y → Z) 
       {x₀ x₁ : X} → x₀ ≡ x₁ → {y₀ y₁ : Y} → y₀ ≡ y₁
     → f x₀ y₀ ≡ f x₁ y₁
ap² {i} {j} {k} {X} {Y} {Z} f = J A λ {x} → ap (f x)
 where
   A : {x x' : X} → x ≡ x' → Set (j ⊔ k)
   A {x} {x'} p = {y y' : Y} → y ≡ y' → f x y  ≡ f x' y'

pairˣ⁼ : {i : Level}{A₀ A₁ : Set i}{a₀ a₀' : A₀}{a₁ a₁' : A₁}
       → a₀ ≡ a₀' → a₁ ≡ a₁' → (a₀ , a₁) ≡ (a₀' , a₁')
pairˣ⁼ p = ap² (λ x y → (x , y)) p 

pr₁⁼ : {i j : Level}{X : Set i}{Y : X → Set j}{w w' : Σ \(x : X) → Y x}
     → w ≡ w' → pr₁ w ≡ pr₁ w'
pr₁⁼ p = ap pr₁ p

pr₂⁼ : {i j : Level}{X : Set i}{Y : X → Set j}{w w' : Σ \(x : X) → Y x}
     → (p : w ≡ w') → transport Y (pr₁⁼ p) (pr₂ w) ≡ pr₂ w'
pr₂⁼ {i} {j} {X} {Y} {w} {w'} = J (λ {w} {w'} p → transport Y (pr₁⁼ p) (pr₂ w) ≡ pr₂ w') λ {w} → refl

-- why doesn't this work: apd {i ⊔ j} {j} {Σ Y} {λ w → Y (pr₁ w)} pr₂ {w} {w'} {ap pr₁ p}

pair⁼-η : {i j : Level} {A : Set i} {B : A → Set j} {w₀ w₁ : Σ B}
        → (p : w₀ ≡ w₁) → p ≡ pair⁼ (pr₁⁼ p) (pr₂⁼ p)
pair⁼-η = J (λ {w} {w'} p → p ≡ pair⁼ (pr₁⁼ p) (pr₂⁼ p)) refl

pr₂ˣ⁼ : {i : Level}{A₀ A₁ : Set i}{w w' : A₀ × A₁}
      → w ≡ w' → pr₂ w ≡ pr₂ w'
pr₂ˣ⁼ = ap pr₂

\end{code}

Constancy

\begin{code}

constant : {i j : Level} {X : Set i} {Y : Set j} → (X → Y) → Set(i ⊔ j)
constant f = ∀ x x' → f x ≡ f x'

Lemma[∘-constant] : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
                  → constant f → constant (g ∘ f)
Lemma[∘-constant] f g cf x x' = ap g (cf x x')

\end{code}

Empty type:

\begin{code}

data ∅ : Set where

∅-elim : {i : Level}{A : Set i} → ∅ → A
∅-elim ()

¬ : {i : Level} → Set i → Set i
¬ X = X → ∅

infix 30 _≠_

_≠_ : {i : Level} {A : Set i} → A → A → Set i
x ≠ y = ¬ (x ≡ y)

\end{code}

Singleton type:

\begin{code}

data ⒈ : Set where
 ⋆ : ⒈

unit : {X : Set} → X → ⒈
unit x = ⋆

singleton : ∀(x x' : ⒈) → x ≡ x'
singleton ⋆ ⋆ = refl

\end{code}

Disjoint union:

\begin{code}

infixr 20 _+_

data _+_ (X₀ X₁ : Set) : Set where
  inl : X₀ → X₀ + X₁
  inr : X₁ → X₀ + X₁

case : {X₀ X₁ Y : Set} → (X₀ → Y) → (X₁ → Y) → X₀ + X₁ → Y
case f₀ f₁ (inl x₀) = f₀ x₀
case f₀ f₁ (inr x₁) = f₁ x₁

equality-cases : {X₀ X₁ : Set} → {A : Set} → 
    ∀(y : X₀ + X₁) → (∀ x₀ → y ≡ inl x₀ → A) → (∀ x₁ → y ≡ inr x₁ → A) → A
equality-cases (inl x₀) f₀ f₁ = f₀ x₀ refl
equality-cases (inr x₁) f₀ f₁ = f₁ x₁ refl

cases : {X₀ X₁ Y₀ Y₁ : Set} → (X₀ → Y₀) → (X₁ → Y₁) → X₀ + X₁ → Y₀ + Y₁
cases f₀ f₁ (inl x₀) = inl (f₀ x₀)
cases f₀ f₁ (inr x₁) = inr (f₁ x₁)

Lemma[+] : {X₀ X₁ : Set} → (x : X₀ + X₁) →
             (Σ \(x₀ : X₀) → x ≡ inl x₀) + (Σ \(x₁ : X₁) → x ≡ inr x₁)
Lemma[+] (inl x₀) = inl (x₀ , refl)
Lemma[+] (inr x₁) = inr (x₁ , refl)

\end{code}

Decidability, disrectess, hproposition and hset:

\begin{code}

decidable : Set → Set
decidable A = A + ¬ A

discrete : Set → Set
discrete A = ∀(a a' : A) → decidable (a ≡ a')

hprop : Set → Set
hprop X = (x y : X) → x ≡ y

hprop-valued : {A : Set} → (A → Set) → Set
hprop-valued P = ∀ a → hprop(P a)

⒈-hprop : hprop ⒈
⒈-hprop ⋆ ⋆ = refl

Σ-hprop : {A : Set} {B : A → Set}
        → hprop A → hprop-valued B → hprop (Σ B)
Σ-hprop {A} {B} hA hB (a₀ , b₀) (a₁ , b₁) = pair⁼ (hA a₀ a₁) (hB a₁ (transport B (hA a₀ a₁) b₀) b₁)

hset : Set → Set
hset X = {x y : X} → hprop (x ≡ y)

hset-valued : {A : Set} → (A → Set) → Set
hset-valued P = ∀ a → hset(P a)

Σ-hset : {A : Set} {B : A → Set}
       → hset A → hset-valued B → hset (Σ B)
Σ-hset {A} {B} hA hB {w₀} {w₁} p q = (pair⁼-η p) · claim₂ · (pair⁼-η q)⁻¹
 where
  □ : pr₁ w₀ ≡ pr₁ w₁ → Set
  □ r = transport B r (pr₂ w₀) ≡ pr₂ w₁
  claim₀ : pr₁⁼ p ≡ pr₁⁼ q
  claim₀ = hA (pr₁⁼ p) (pr₁⁼ q)
  claim₁ : transport □ claim₀ (pr₂⁼ p) ≡ pr₂⁼ q
  claim₁ = hB (pr₁ w₁) (transport □ claim₀ (pr₂⁼ p)) (pr₂⁼ q)
  claim₂ : pair⁼ (pr₁⁼ p) (pr₂⁼ p) ≡ pair⁼ (pr₁⁼ q) (pr₂⁼ q)
  claim₂ = apd² pair⁼ claim₀ claim₁

\end{code}

The type of function extensionality

\begin{code}

Funext : Set₁
Funext = {X : Set} {Y : X → Set} {f g : (x : X) → Y x}
       → (∀(x : X) → f x ≡ g x) → f ≡ g

\end{code}

