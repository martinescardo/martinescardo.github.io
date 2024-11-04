-- Martin Escardo, 3rd August 2015, last updated 5th August 2015

{-
   A small type of propositions à la Voevodsky in Agda.

   (There is also a predicative version at
   http://www.cs.bham.ac.uk/~mhe/predicativity/)
-}

module index where

{- 
   We use type-in-type to get an experimental implementation of
   impredicativity à la Voevodsky (propositional resizing) in Agda.

   Only the tiny module prop.agda needs to use type-in-type. All the
   other modules work without it.

   Because of limitations of Agda, or perhaps of our ability to exploit
   Agda, we can only resize from the second universe U₁=Set₁ to the
   first universe U=Set₀.

   A difference of this kind of impredicativity with CoC's
   impredicativity is that the "axioms" of unique choice and
   description hold. Our truth values are types with at most one
   element, and yet they are proof relevant in some sense.

   zip file with agda source available at
   http://www.cs.bham.ac.uk/~mhe/impredicativity/impredicativity.zip

   This type checks in Agda 2.4.2.2

   Click at a module name to navigate to it.
-}

{- 
   A truth value is a type together with a witness that it is a
   proposition. The following module defines the type Prp:U of truth
   values in U, which amounts to impredicativity. It is the only rogue
   module that uses type-in-type to define 

         Prp = Σ(P:U).isProp P 

   so that Prp:U.
-}

open import prop

{-
   NB. The option type-in-type is not inherited from prop.agda. For
   example, the following type checks with type-in-type, but fails to
   type check in this module, as it should:
-}

{- Fails to type check (good!):
set : Set
set = Set
-}

{-
   The type of propositions is a set, assuming functional and
   propositional extensionality:
-}

open import propisset

{-
   Using impredicativity, we can define propositional truncation by
   universal quantification over truth values (as Voevodsky does):
-}

open import proptrunc

{- 
   We then develop some amount of logic in the type Prp of
   propositions, where we define the logical connectives and their
   introduction and elimination rules following the ideas of the HoTT
   book. We then prove that

      false = ∀ r. r
      p ∧ q = ∀ r. (p ⇒ q ⇒ r) ⇒ r
      p ∨ q = ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
      ∃ p   = ∀ r. (∀ x. p(x) ⇒ r) ⇒ r 
-}

open import logic

{- 
   We then prove the axiom of description: for any set X and any
   p:X→Prp,
    
       (∃! p) = true → Σ(x:X).p(x)=true.
-}

open import description

{- We then get quotients (incomplete for the moment): -}

open import quotient


