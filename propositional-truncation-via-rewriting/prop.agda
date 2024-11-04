-- Martin Escardo, 3rd August 2015.

{-# OPTIONS --without-K #-}

module prop where

open import preliminaries
open import isprop public

-- The type of small propositions is large:
Prp : {i : 𝕃} → U(lsuc i)
Prp{i} = Σ \(P : U i) → isProp P

-- Destructors:

_holds : {i : 𝕃} → Prp{i} → U i
_holds = pr₁

holdsIsProp : {i : 𝕃} (p : Prp{i}) → isProp(p holds)
holdsIsProp = pr₂

-- The idea of the terminology is that we cannot assert a point of the
-- type Prop, as it is a pair, but we can assert that it holds, meaning
-- that we assert that its first component has an inhabitant, as it is
-- a truth-value (a type P with the asserted side-condition isProp P).

-- We have the following judgemental equalities:
--
--    (β₁)   ( P , isp ) holds = P,
--    (β₂)   holdsIsProp ( P , isp ) = isp,
--    (η)    p = ( p holds , holdsIsProp p ).

-- NB. holdsIsProp shows that _holds is an embedding in the sense of
-- the HoTT book https://homotopytypetheory.org/book/.

Prop-≡ : {i : 𝕃} {p q : Prp{i}} → p holds ≡ q holds → p ≡ q
Prop-≡ {i} {p} {q} e = e'
 where
   e' : p ≡ q
   e' = Σ-≡ e (isProp-isProp (transport isProp e (holdsIsProp p)) (holdsIsProp q))

-- Propositional univalence says that any two (logically) equivalent
-- propositions are equal:

postulate propua : {i : 𝕃} {P Q : U i} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q

-- It can be formulated as follows:

propext : {i : 𝕃} {p q : Prp{i}} → (p holds → q holds) → (q holds → p holds) → p ≡ q
propext {i} {p} {q} f g = Prop-≡ (propua (holdsIsProp p) (holdsIsProp q) f g)
