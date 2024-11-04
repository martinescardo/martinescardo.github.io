-- Martin Escardo, 3rd August 2015, updated 6th August 2015

{-
   We develop some logic in the type Prp of propositions, where we
   define the logical connectives and their introduction and
   elimination rules following the ideas of the HoTT book. We then
   prove that

      false ≡ ∀ r. r
      p ∧ q ≡ ∀ r. (p ⇒ q ⇒ r) ⇒ r
      p ∨ q ≡ ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
      ∃ p   ≡ ∀ r. (∀ x. p(x) ⇒ r) ⇒ r
-}

{-# OPTIONS --without-K #-}

module logic where

open import preliminaries
open import prop
open import proptrunc

open import propisset
open import propua

-- The two canonical truth values:

true : Prp
true = ₍ 𝟙 , 𝟙-isProp ₎

false : Prp
false = ₍ 𝟘 , 𝟘-isProp ₎

-- Propositional univalence gives that p holds ≡ (p ≡ true):

holds→equal-true : {p : Prp} → p holds → p ≡ true
holds→equal-true {p} h = Prp-≡ (prop-ua' (holdsIsProp p) (holdsIsProp true) (λ _ → zero) (λ _ → h))

equal-true→holds : {p : Prp} → p ≡ true → p holds
equal-true→holds {p} e = transport (λ X → X) (sym a) zero
  where
   a : p holds ≡ 𝟙
   a = ap _holds e

holds-is-equal-true : (p : Prp) → p holds ≡ (p ≡ true)
holds-is-equal-true p = prop-ua (holdsIsProp p) Prp-isSet holds→equal-true equal-true→holds

-- The logical connectives:

infixr 42 _⇒_
infixr 41 _∨_
infixr 40 _∧_

_∧_ _∨_ _⇒_ : Prp → Prp → Prp

p ∧ q = ₍ p holds × q holds , isProp-closed-under-Σ (holdsIsProp p) (λ _ → holdsIsProp q) ₎

p ⇒ q = ₍ (p holds → q holds) , isProp-exponential-ideal (λ _ → holdsIsProp q) ₎

p ∨ q = ₍ ∥ p holds + q holds ∥ , ∥∥-isProp ₎

-- The quantifiers.
--
-- Because "∀" is taken, and "∃" has a slightly different meaning in
-- the HoTT book, we will have to use something else. We write a
-- small, almost invisible, dot on top of them:

∀̇ ∃̇ : {X : U} → (X → Prp) → Prp

∀̇ p = ₍ (∀ x → p x holds) , isProp-exponential-ideal (λ x → holdsIsProp(p x)) ₎

∃̇ p = ₍ ∥(Σ \x → p x holds)∥ , ∥∥-isProp ₎

-- Introduction principles:

true-intro : true holds
true-intro = zero

∧-intro : {p q : Prp} → p holds → q holds → p ∧ q holds
∧-intro = _,_

∨-intro-L : {p q : Prp} → p holds → p ∨ q holds
∨-intro-L h = ∣ inl h ∣

∨-intro-R : {p q : Prp} → q holds → p ∨ q holds
∨-intro-R k = ∣ inr k ∣

⇒-intro : {p q : Prp} → (p holds → q holds) → p ⇒ q holds
⇒-intro = λ f → f

∃̇-intro : {X : U} {p : X → Prp} (x : X) → p x holds → ∃̇ p holds
∃̇-intro x h = ∣ x , h ∣

∀̇-intro : {X : U} {p : X → Prp} → ((x : X) → p x holds) → ∀̇ p holds
∀̇-intro = λ f → f

-- Elimination principles:

∧-elim-L : {p q : Prp} → p ∧ q holds → p holds
∧-elim-L = pr₁

∧-elim-R : {p q : Prp} → p ∧ q holds → q holds
∧-elim-R = pr₂

false-elim : {p : Prp} → false holds → p holds
false-elim = λ()

∨-elim : {p q r : Prp} → (p holds → r holds) → (q holds → r holds)
       → p ∨ q holds → r holds
∨-elim {p} {q} {r} f g = ∥∥-rec (holdsIsProp r) (+-rec f g)

⇒-elim : {p q : Prp} → (p holds → q holds) → p holds → q holds
⇒-elim = λ f → f

∃̇-elim : {X : U} {p : X → Prp} {r : Prp} → ((x : X) → p x holds → r holds)
        → ∃̇ p holds → r holds
∃̇-elim {X} {p} {r} f = ∥∥-rec (holdsIsProp r) (Σ-rec f)

∀̇-elim : {X : U} {p : X → Prp} → ∀̇ p holds → (x : X) → p x holds
∀̇-elim = λ f → f

-- Characterizations in terms of _⇒_ and ∀̇:

false-charac : false ≡ ∀̇ \r → r
false-charac = propext a b
 where
  a : false holds → (∀̇ \r → r) holds
  a = false-elim {(∀̇ \r → r)}
  b : (∀̇ \r → r) holds → false holds
  b φ = φ false

∧-charac : (p q : Prp) → p ∧ q ≡ ∀̇ \r → (p ⇒ q ⇒ r) ⇒ r
∧-charac p q = propext a b
 where
  a : p ∧ q holds → (∀̇ \r → (p ⇒ q ⇒ r) ⇒ r) holds
  a pq = λ r pqr → pqr (∧-elim-L {p} {q} pq) (∧-elim-R {p} {q} pq)
  b : (∀̇ \r → (p ⇒ q ⇒ r) ⇒ r) holds → p ∧ q holds
  b φ = ∧-intro {p} {q} (φ p (λ x y → x)) (φ q (λ x y → y))

∨-charac : (p q : Prp) → p ∨ q ≡ ∀̇ \r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
∨-charac p q = propext a b
 where
   a : p ∨ q holds → (∀̇ \r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r) holds
   a pq = λ r pr qr → ∨-elim {p} {q} {r} pr qr pq
   b : (∀̇ \r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r) holds → p ∨ q holds
   b φ = λ r f → φ r (λ x → f (inl x)) (λ y → f (inr y))

∃̇-charac : {X : U} (p : X → Prp) → ∃̇ p ≡ ∀̇ \r → (∀̇ \x → p x ⇒ r) ⇒ r
∃̇-charac {X} p = propext a b
 where
  a : (∃̇ p) holds → (∀̇ \r → (∀̇ \x → (p x ⇒ r)) ⇒ r) holds
  a ep = λ r f → ∃̇-elim {X} {p} {r} (λ x px → f x px) ep
  b : (∀̇ \r → (∀̇ \x → (p x ⇒ r)) ⇒ r) holds → (∃̇ p) holds
  b φ = λ r f → φ r (λ x px → f (x , px))
