-- Martin Escardo, 3rd August 2015

{-

 We use type-in-type to get impredicativity à la Voevodsky
 (propositional resizing) in Agda.

 No other module in this development uses type-in-type.

 Because of limitations of Agda, or perhaps of our ability to exploit
 Agda, we can only resize from the second universe to the first.

 Curiously, if we write "U" rather than "Set" below, then other
 modules don't type check, even though U=Set by definition. I am not
 sure why this is the case. But it is possible to still use U in other
 modules, and we do.

-}

{-# OPTIONS --type-in-type #-}
{-# OPTIONS --without-K #-}

module prop where

open import preliminaries

-- A proposition is a type with at most one element:

open import isprop public

-- A truth value is a type together with a witness that it is a
-- proposition. "Prop" is an Agda reserved, but unused,
-- keyword, and Agda won't let us use it as an identifier:

Prp : Set
Prp = Σ \(P : Set) → isProp P

-- We could use the pair constructor _,_ from Σ, but this doesn't type
-- check when used in a module without the option type-in-type. The
-- reason is that the types of Σ and _,_ are different with(out)
-- type-in-type. To circumvent this, we define another another binary
-- operator ₍_,_₎, which does type check when used without
-- type-in-type. The reason this works is that the type of this new
-- operator is the same with or without type-in-type:

₍_,_₎ : (P : Set) → isProp P → Prp
₍_,_₎ = _,_

-- It is also necessary, for the same reason, to specialize the
-- types of the projections:

_holds : Prp → Set
_holds = pr₁

infix 20 _holds

holdsIsProp : (p : Prp) → isProp(p holds)
holdsIsProp = pr₂

-- NB. holdsIsProp shows that _holds is an embedding in the sense of
-- the HoTT book.

Prp-≡ : {p q : Prp} → p holds ≡ q holds → p ≡ q
Prp-≡ {p} {q} e = Σ-≡ e (isProp-isProp (transport isProp e (holdsIsProp p)) (holdsIsProp q))

-- open import propua -- <-- Doesn't work. We have to repeat the postulate literally:

postulate prop-ua' : {P Q : Set} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q

-- (Why? Moreover, there is an example in which we need to use both
-- prop-ua and prop-ua'.)

propext : {p q : Prp} → (p holds → q holds) → (q holds → p holds) → p ≡ q
propext {p} {q} f g = Prp-≡ e
 where
  e : p holds ≡ q holds
  e = prop-ua' (holdsIsProp p) (holdsIsProp q) f g
