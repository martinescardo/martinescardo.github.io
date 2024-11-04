{-# OPTIONS --without-K #-}

module funext where

open import preliminaries

postulate funext : {i j : 𝕃} {X : Set i} {Y : X → Set j} {f g : (x : X) → Y x}
                → ((x : X) → f x ≡ g x) → f ≡ g
