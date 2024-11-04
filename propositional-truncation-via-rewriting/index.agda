-- Martin Escardo, September 2017, based on earlier ideas and Agda files.

module index where

-- The large type of propositions:

open import prop

-- The type of propositions is a set, assuming functional and
-- propositional extensionality:

open import propisset

-- We can define large propositional truncation by universal
-- quantification over propositions. Then by resizing it we get the
-- usual propositional truncation. But we only apply resizing to large
-- propositions which arise as truncations.

open import proptrunc

-- We then develop some amount of logic in the type Prop of
-- propositions, where we define the logical connectives and their
-- introduction and elimination rules following the ideas of the HoTT
-- book. We then prove that
--
--      false = ∀ r. r
--      p ∧ q = ∀ r. (p ⇒ q ⇒ r) ⇒ r
--      p ∨ q = ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
--      ∃ p   = ∀ r. (∀ x. p(x) ⇒ r) ⇒ r

open import logic

-- We then prove the axiom of description: for any set X and any
-- p:X→Prop,
--
--     (∃!(x:X).p(x))=true → Σ(x:X).p(x)=true.

open import description
