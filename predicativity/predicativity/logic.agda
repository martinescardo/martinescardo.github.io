-- Martin Escardo, 7th August 2015.

{-# OPTIONS --without-K #-}

module logic where

open import preliminaries
open import prop
open import proptrunc
open import propisset
open import propua

-- The two canonical truth values:

true : {i : L} → Prp i
true = ₍ 𝟙 , 𝟙-isProp ₎

false : {i : L} → Prp i
false = ₍ 𝟘 , 𝟘-isProp ₎

holds→equal-true : {i : L} {p : Prp i} → p holds → p ≡ true
holds→equal-true {i} {p} h = Prp-≡ (prop-ua (holdsIsProp p) (holdsIsProp true) (λ _ → zero) (λ _ → h))

equal-true→holds : {i : L} {p : Prp i} → p ≡ true → p holds
equal-true→holds {i} {p} e = transport (λ X → X) (sym a) zero
  where
   a : p holds ≡ 𝟙
   a = ap _holds e

-- The logical connectives:

infixr 42 _⇒_
infixr 41 _∨_
infixr 40 _∧_

_∧_ _∨_ _⇒_ : {i : L} → Prp i → Prp i → Prp i

p ∧ q = ₍ p holds × q holds , isProp-closed-under-Σ (holdsIsProp p) (λ _ → holdsIsProp q) ₎

p ⇒ q = ₍ (p holds → q holds) , isProp-exponential-ideal (λ _ → holdsIsProp q) ₎

p ∨ q = ₍ ∥ p holds + q holds ∥ , ∥∥-isProp ₎

-- The quantifiers.
--
-- Because "∀" is taken, and "∃" has a slightly different meaning in
-- the HoTT book, we will have to use something else. We write a
-- small, almost invisible, dot on top of them:

∀̇ ∃̇ : {i j : L} → {X : U i} → (X → Prp j) → Prp (i ⊔ j)

∀̇ p = ₍ (∀ x → p x holds) , isProp-exponential-ideal (λ x → holdsIsProp(p x)) ₎

∃̇ p = ₍ ∥(Σ \x → p x holds)∥ , ∥∥-isProp ₎

-- Introduction principles:

true-intro : {i : L} → true {i} holds
true-intro = zero

∧-intro : {i : L} {p q : Prp i} → p holds → q holds → p ∧ q holds
∧-intro = _,_

∨-intro-L : {i : L} {p q : Prp i} → p holds → p ∨ q holds
∨-intro-L h = ∣ inl h ∣

∨-intro-R : {i : L} {p q : Prp i} → q holds → p ∨ q holds
∨-intro-R k = ∣ inr k ∣

⇒-intro : {i : L} {p q : Prp i} → (p holds → q holds) → p ⇒ q holds
⇒-intro = λ f → f

∃̇-intro : {i j : L} {X : U i} {p : X → Prp j} (x : X) → p x holds → ∃̇ p holds
∃̇-intro x h = ∣ x , h ∣

∀̇-intro : {i j : L} {X : U i} {p : X → Prp j} → ((x : X) → p x holds) → ∀̇ p holds
∀̇-intro = λ f → f

-- Elimination principles:

∧-elim-L :  {i : L} {p q : Prp i} → p ∧ q holds → p holds
∧-elim-L = pr₁

∧-elim-R :  {i : L} {p q : Prp i} → p ∧ q holds → q holds
∧-elim-R = pr₂

false-elim : {i j : L} {p : Prp i} → false {j} holds → p holds
false-elim = λ()

∨-elim :  {i : L} {p q r : Prp i} → (p holds → r holds) → (q holds → r holds)
       → p ∨ q holds → r holds
∨-elim {i} {p} {q} {r} f g = ∥∥-rec (holdsIsProp r) (+-rec f g)

⇒-elim : {i : L} {p q : Prp i} → (p holds → q holds) → p holds → q holds
⇒-elim = λ f → f

∃̇-elim : {i j : L} {X : U i} {p : X → Prp j} {r : Prp (i ⊔ j)} → ((x : X) → p x holds → r holds)
        → ∃̇ p holds → r holds
∃̇-elim {i} {j} {X} {p} {r} f = ∥∥-rec (holdsIsProp r) (Σ-rec f)

∀̇-elim : {i j : L} {X : U i} {p : X → Prp j} → ∀̇ p holds → (x : X) → p x holds
∀̇-elim = λ f → f

-- Characterizations in terms of _⇒_ and ∀̇:

_⟷_ : {i j : Level} → Prp i → Prp j → U (i ⊔ j)
p ⟷ q = (p holds → q holds) × (q holds → p holds)

infix 32 _⟷_

false-charac : {i : L} → (false {i}) ⟷ ∀̇ \r → r
false-charac {i} = (a , b)
 where
  a : false holds → (∀̇ \r → r) holds
  a = false-elim {lsuc i} {i} {(∀̇ \r → r)}
  b : (∀̇ \r → r) holds → false holds
  b φ = φ false

∧-charac : {i : L} (p q : Prp i) → p ∧ q ⟷ ∀̇ \r → (p ⇒ q ⇒ r) ⇒ r
∧-charac {i} p q = (a , b)
 where
  a : p ∧ q holds → (∀̇ \r → (p ⇒ q ⇒ r) ⇒ r) holds
  a pq = λ r pqr → pqr (∧-elim-L {i} {p} {q} pq) (∧-elim-R {i} {p} {q} pq)
  b : (∀̇ \r → (p ⇒ q ⇒ r) ⇒ r) holds → p ∧ q holds
  b φ = ∧-intro {i} {p} {q} (φ p (λ x y → x)) (φ q (λ x y → y))

∨-charac : {i : L} (p q : Prp i) → (p ∨ q) ⟷ ∀̇ \r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
∨-charac {i} p q = (a , b)
 where
   a : p ∨ q holds → (∀̇ \r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r) holds
   a pq = λ r pr qr → ∨-elim {i} {p} {q} {r} pr qr pq
   b : (∀̇ \r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r) holds → p ∨ q holds
   b φ = decrease (λ r f → φ r (λ x → f (inl x)) (λ y → f (inr y)))


∃̇-charac : {i : L} {X : U i} (p : X → Prp i) → (∃̇ p) ⟷ ∀̇ \r → (∀̇ \x → p x ⇒ r) ⇒ r
∃̇-charac {i} {X} p = (a , b)
 where
  a : (∃̇ p) holds → (∀̇ \r → (∀̇ \x → (p x ⇒ r)) ⇒ r) holds
  a ep = λ r f → ∃̇-elim {i} {i} {X} {p} {r} (λ x px → f x px) ep
  b : (∀̇ \r → (∀̇ \x → (p x ⇒ r)) ⇒ r) holds → (∃̇ p) holds
  b φ = decrease (λ r f → φ r (λ x px → f (x , px)))
