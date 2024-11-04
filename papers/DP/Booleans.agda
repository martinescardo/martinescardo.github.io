module Booleans where

open import Logic
open import LogicalFacts
open import Equality

data Bool : Set where
  false : Bool
  true : Bool

either-true-or-false : ∀(x : Bool) → x ≡ true ∨ x ≡ false
either-true-or-false true = ∨-intro₀ reflexivity
either-true-or-false false = ∨-intro₁ reflexivity


true-and-false-not-equal : true ≠ false
true-and-false-not-equal ()


not-both-true-and-false : ∀(x : Bool) → ¬(x ≡ true ∧ x ≡ false)
not-both-true-and-false x = 
   true-and-false-not-equal ∘ (two-things-equal-to-a-third-are-equal x true false)


false-is-not-true :  ∀(x : Bool) → x ≡ false → x ≠ true
false-is-not-true true () 
false-is-not-true false reflexivity = λ ()

not-true-is-false : ∀(x : Bool) → x ≠ true → x ≡ false
not-true-is-false true f = ⊥-elim (f reflexivity)
not-true-is-false false f = reflexivity

not-false-is-true :  ∀(x : Bool) → x ≠ false → x ≡ true
not-false-is-true true f = reflexivity
not-false-is-true false f = ⊥-elim (f reflexivity)


boolean-not-exists-implies-forall : {X : Set} → {p : X → Bool} → 
          ¬(∃(\(x : X) → p x ≡ true)) → ∀(x : X) → p x ≡ false

boolean-not-exists-implies-forall  {X} {p} f x = 
  not-true-is-false (p x) (not-exists-implies-forall {X} {λ x → p x ≡ true} f x)


boolean-forall-implies-not-exists : {X : Set} → {p : X → Bool} → 
        (∀(x : X) → p x ≡ false) → ¬(∃(\(x : X) → p x ≡ true))

boolean-forall-implies-not-exists  {X} {p} f e = 
   forall-implies-not-exists {X} {λ x → p x ≡ true} (λ x → false-is-not-true (p x) (f x)) e


disjunction-is-existential : {A B : Ω} → 
         A ∨ B → ∃(\(x : Bool) → (x ≡ true → A) ∧ (x ≡ false → B))

disjunction-is-existential (∨-intro₀ a) = ∃-intro true (∧-intro (λ r → a) (λ()))
disjunction-is-existential (∨-intro₁ b) = ∃-intro false (∧-intro (λ()) (λ s → b))

-- This is quite useless for proofs (and not used):

if_then_else_ : {X : Set} → Bool → X → X → X
-------------

if true then x else y = x
if false then x else y = y
