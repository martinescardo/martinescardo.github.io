module DP where

{-- 
    Dubuc-Penon compactness, the Drinker Paradox and searchable sets 
    ----------------------------------------------------------------

      Martin Escardo & Paulo Oliva, November 2009
 
      This is a collection of type-theoretic theorems formulated and proved in Agda.

      To view the mathematical symbols correctly in firefox, choose
                 View -> Character encoding -> Unicode.

    ABSTRACT. DP in the name of this module stands, ambiguously, for
    drinker paradox and for Dubuc-Penon compactness. They coincide for
    inhabited sets, but not otherwise, because sets satisfying the
    DP-paradox must be inhabited, whereas the empty set is DP-compact.
    We also prove equivalence with the notion of searchability
    previously introduced and investigated by the first named author. 

    THEOREM. TFAE for any set X.

      1. X is inhabited and Dubuc-Penon compact.
      2. X is searchable. 
      3. X satisfies the boolean drinker paradox.
      4. X satisfies the limited principle of omniscience.

    NB. Some implications rely on the axiom of choice, which is provable in type theory.
--}

open import Logic
open import LogicalFacts
open import Booleans
open import Choice
open import Equality
open import EmptySet

-- (The module Logic defines the type of propositions Ω (=Set).)

-- DEFINITIONS of the notions investigated:

LPO : Set → Ω
LPO X = ∀(p : X → Bool) → (∃(\(x : X) → p(x) ≡ true)) ∨ (∀(x : X) → p(x) ≡ false)

∃-drinker-paradox : Set → Ω
∃-drinker-paradox X = ∀(p : X → Bool) → ∃(\(a : X) → ∃(\(x : X) → p x ≡ true) → p a ≡ true)

∀-drinker-paradox : Set → Ω
∀-drinker-paradox X = ∀(p : X → Bool) → ∃(\(a : X) → p a ≡ false → ∀(x : X) → p x ≡ false)

searchable : Set → Ω
searchable X = ∀(p : X → Bool) → ∃(\(a : X) → ¬¬ (∃(\(x : X) → p x ≡ true)) → p a ≡ true)

Ω₁ = Set1

Dubuc-Penon-compact : Set → Ω₁
Dubuc-Penon-compact X = ∀(A : Ω) (B : X → Ω) → (∀(x : X) → A ∨ B x) → A ∨ (∀(x : X) → B x)

{-- REMARKS:

      1. The original, well-known version of the DP paradox is the one
         involving the universal quantifier, and is usually stated for
         not-necessarily boolean-valued predicates. The roles of the
         boolean values are symmetric and can be swapped at will, and
         our formulation using false in the ∀-version simplifies the
         proofs by avoiding the swapping.

     2. In the above, Ω₁=Set1 is the first universe above Ω=Set.
        Essentially, Dubuc-Penon compactness is an axiom scheme, but
        type theory with universes allows it to be a single axiom
        living in the second universe, which quantifies over
        types/propositions of the first universe. We can think of Ω₁
        as a (somewhat restricted) type of second-order
        propositions. Notice that this is not impredicative.
--} 



-- THEOREMS. 


{-- 
    Searchable sets are originally defined using selection functions,
    but this makes no difference in type theory (or realizability)
    because the axiom of choice holds:
--}

Remark₀ : (X : Set) → 
-------
  searchable X ⇔ 
    ∃(\(ε : (X → Bool) → X) → ∀(p : X → Bool) → ¬¬(∃(\(x : X) → p x ≡ true)) → p(ε p) ≡ true)

Remark₀ X = ∧-intro AC (λ e → λ p → ∃-intro ((∃-witness e) p) ((∃-elim e) p))



Remark₁ : Dubuc-Penon-compact EmptySet
-------
Remark₁ A B f = ∨-intro₁(λ ())



Remark₂ : (X : Set) → searchable X → inhabited X
-------
Remark₂ X ε = ∃-intro (∃-witness(ε(λ x → true))) *



Theorem₀ : (X : Set) → searchable X → ∃-drinker-paradox X
-------
Theorem₀ X assumption p  = ∃-intro (∃-witness(assumption p)) ((∃-elim(assumption p)) ∘ ¬¬-intro)



Theorem₁ : (X : Set) → ∃-drinker-paradox X → ∀-drinker-paradox X
--------
Theorem₁ X ε p = ∃-intro a lemma₁
  where a : X
        a = ∃-witness(ε p)

        lemma₀ : ∃(\(x : X) → p x ≡ true) → p a ≡ true
        lemma₀ = ∃-elim(ε p)

        lemma₁ :  p a ≡ false → ∀(x : X) → p x ≡ false
        lemma₁ r = boolean-not-exists-implies-forall(contra-positive lemma₀ (false-is-not-true (p a) r))



Theorem₂ : (X : Set) → ∀-drinker-paradox X → LPO X
--------
Theorem₂ X ε p = lemma₁ (∃-intro (p a) reflexivity)
  where a : X
        a = ∃-witness(ε p)

        lemma₀ : p a ≡ false → ∀(x : X) → p x ≡ false
        lemma₀ = ∃-elim(ε p)

        lemma₁ : ∃(\(y : Bool) → p a ≡ y) → (∃(\(x : X) → p(x) ≡ true)) 
                                          ∨ (∀  (x : X) → p(x) ≡ false)
        lemma₁ (∃-intro true r) = ∨-intro₀ (∃-intro a r)
        lemma₁ (∃-intro false r) = ∨-intro₁ (lemma₀ r)


Theorem₃ : (X : Set) → inhabited X ∧ LPO X → searchable X
--------
Theorem₃ X (∧-intro (∃-intro x₀ *) d) p = lemma(d p)
  where lemma : (∃(\(x : X) → p(x) ≡ true)) ∨ (∀(x : X) → p(x) ≡ false) → 
                 ∃(\(a : X) → ¬¬(∃(\(x : X) → p x ≡ true)) → p a ≡ true)
        lemma (∨-intro₀(∃-intro a r)) = ∃-intro a (λ e → r)
        lemma (∨-intro₁ a) = ∃-intro x₀ 
                                    (λ e → ⊥-elim(contradictory (boolean-forall-implies-not-exists a) e))


Theorem₄ : (X : Set)  → Dubuc-Penon-compact X → LPO X 
--------
Theorem₄ X assumption p = conclusion
  where A : Ω 
        A = ∃(\(x : X) → p x ≡ true)
 
        B : X → Ω
        B x = (p x ≡ false)

        lemma : ∀(x : X) → A ∨ B x
        lemma x = sublemma (∃-intro (p x) reflexivity)
                    where sublemma : ∃(\(y : Bool) → p x ≡ y) → A ∨ B x
                          sublemma (∃-intro true r) = ∨-intro₀(∃-intro x r)
                          sublemma (∃-intro false r) = ∨-intro₁ r

        conclusion : (∃(\(x : X) → p(x) ≡ true)) ∨ (∀(x : X) → p(x) ≡ false)
        conclusion = assumption A B lemma



Theorem₅ : (X : Set) → LPO X → Dubuc-Penon-compact X
--------
Theorem₅ X assumption A B DP-premise = DP-conclusion 
 where lemma₀ : ∀(x : X) → ∃(\(y : Bool) → (y ≡ true → A) ∧ (y ≡ false → B x))
       lemma₀ x = disjunction-is-existential(DP-premise x)

       lemma₁ : ∃(\(p : X → Bool) → ∀(x : X) → (p x ≡ true → A) ∧ (p x ≡ false → B x))
       lemma₁ = AC lemma₀

       p : X → Bool
       p = ∃-witness lemma₁

       lemma₂ : ∀(x : X) → (p x ≡ true → A) ∧ (p x ≡ false → B x)
       lemma₂ = ∃-elim lemma₁

       lemma₃ : (∃(\(x : X) → p(x) ≡ true)) ∨ (∀(x : X) → p(x) ≡ false) → A ∨ (∀(x : X) → B x)
       lemma₃ (∨-intro₀(∃-intro x r)) = ∨-intro₀(∧-elim₀(lemma₂ x) r)
       lemma₃ (∨-intro₁ f) = ∨-intro₁(λ x → ∧-elim₁(lemma₂ x) (f x))

       DP-conclusion : A ∨ (∀(x : X) → B x)
       DP-conclusion = lemma₃(assumption p)
