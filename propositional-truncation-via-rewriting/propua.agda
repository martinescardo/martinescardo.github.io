{-# OPTIONS --without-K #-}

module propua where

open import preliminaries
open import isprop

postulate prop-ua : {i : 𝕃} {P Q : U i} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q
