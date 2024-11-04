
{-# OPTIONS --without-K #-}

module preliminaries where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_) public

L = Level

U : (i : L) → Set(lsuc i)
U i = Set i

-- Some stardard types

data 𝟘 {i : L} : U i where

data 𝟙 {i : L} : U i where
 zero : 𝟙

data 𝟚 {i : L} : U i where
 zero one : 𝟚

Π : {i j : L}{X : U i}(A : X → U j) → U(i ⊔ j)
Π A = ∀ x → A x

record Σ {i j : L}{X : U i}(A : X → U j) : U(i ⊔ j) where
 constructor _,_
 field
  pr₁ : X
  pr₂ : A pr₁

infix 1 _,_

_×_ : {i j : L} → U i → U j → U (i ⊔ j)
X × Y = Σ \(_ : X) → Y

infix 4 _×_

open Σ public

Σ-ind : {i j k : L} {A : U i} {B : A → U j} {C : Σ B → U k}
        → ((x : A) (y : B x) → C (x , y)) → (z : Σ B) → C z
Σ-ind g (x , y) = g x y

Σ-rec : {i j k : L} {A : U i} {B : A → U j} {C : U k}
        → ((x : A) (y : B x) → C) → Σ B → C
Σ-rec = Σ-ind


data _+_ {i j : L} (A : U i) (B : U j) : U (i ⊔ j) where
 inl : A → A + B
 inr : B → A + B

infix 3 _+_

-- We should really include the dependent version of this:
+-rec : {i j k : L} {A : U i} {B : U j} {C : U k}
      → (A → C) → (B → C) → A + B → C
+-rec f g (inl x) = f x
+-rec f g (inr y) = g y

data _≡_ {i : L}{A : U i} : A → A → U i where
 refl : (a : A) → a ≡ a

infix 10 _≡_

trans : {i : L} {X : U i} {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
trans (refl x) (refl .x) = refl x

sym : {i : L} {X : U i} → {x y : X} → x ≡ y → y ≡ x
sym (refl x) = refl x

sym-is-inverse : {i : L} {X : U i} {x y : X} (p : x ≡ y) → refl y ≡ trans (sym p) p
sym-is-inverse (refl x) = refl(refl x)

ap : {i j : L} {X : U i} {A : U j} (f : X → A) {x y : X}
   →  x ≡ y → f x ≡ f y
ap f (refl x) = refl(f x)

transport : {i j : L}{X : U i}{x y : X} → (A : X → U j) → x ≡ y → A x → A y
transport A (refl _) a = a

IdP : {i j : L} {X : U i} {x y : X} (A : X → U j)
    → x ≡ y → A x → A y → U j
IdP A p a b = transport A p a ≡ b

syntax IdP B p b₀ b₁ = b₀ ≡[ B , p ] b₁

apd : {i j : L} {X : U i} {A : X → U j} {x y : X}
    → (f : (x : X) → A x) (p : x ≡ y) → f x ≡[ A , p ] f y
apd f (refl x) = refl(f x)

Σ-≡ : {i j : L} {X : U i} {A : X → U j} {x y : X} {a : A x} {b : A y}
     → (p : x ≡ y) → a ≡[ A , p ] b → _≡_ {i ⊔ j} {Σ A} (x , a) (y , b)
Σ-≡ (refl x) (refl a) = refl(x , a)

×-≡ : {i j : L} {X : U i} {A : U j} {x y : X} {a b : A}
     → x ≡ y → a ≡ b → _≡_ {i ⊔ j} {X × A} (x , a) (y , b)
×-≡ (refl x) (refl a) = refl(x , a)

J : {i j : L} {X : U i} → (A : (x y : X) → x ≡ y → U j)
   → ((x : X) → A x x (refl x))
   →  {x y : X} (p : x ≡ y) → A x y p
J A f (refl x) = f x

isContr : {i : L} → U i → U i
isContr X = Σ \(x₀ : X) → (x : X) → x₀ ≡ x

paths-from : {i : L} {X : U i} (x : X) → U i
paths-from x = Σ \y → x ≡ y

end-point : {i : L} {X : U i} {x : X} → paths-from x → X
end-point = pr₁

trivial-loop : {i : L} {X : U i} (x : X) → paths-from x
trivial-loop x = (x , refl x)

path-from-trivial-loop : {i : L} {X : U i} {x x' : X} (r : x ≡ x') → trivial-loop x ≡ (x' , r)
path-from-trivial-loop {i} {X} = J {i} {i} {X} A (λ x → refl(x , refl x))
 where
  A : (x x' : X) → x ≡ x' → U i
  A x x' r = _≡_ {i} {Σ \(x' : X) → x ≡ x'} (trivial-loop x) (x' , r)

paths-from-is-contractible : {i : L} {X : U i} (x₀ : X) → isContr(paths-from x₀)
paths-from-is-contractible x₀ = trivial-loop x₀ , (λ t → path-from-trivial-loop (pr₂ t))
