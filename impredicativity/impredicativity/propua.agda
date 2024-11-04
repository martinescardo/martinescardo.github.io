{-# OPTIONS --without-K #-}

module propua where

open import preliminaries
open import isprop

postulate prop-ua : {P Q : U} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q
