module EmptySet where

open import Logic

data EmptySet : Set where
-- nothing defined here: there are no constructors of this type.

unique-map-from-empty-set : {X : Set} → EmptySet → X
unique-map-from-empty-set = λ ()

the-empty-set-is-not-inhabited : ¬(inhabited EmptySet)
the-empty-set-is-not-inhabited (∃-intro () *)
