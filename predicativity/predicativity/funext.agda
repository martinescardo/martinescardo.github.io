{-# OPTIONS --without-K #-}

module funext where

open import preliminaries

postulate funext : {i j : Level} {X : U i} {Y : X → U j} {f g : (x : X) → Y x}
                → ((x : X) → f x ≡ g x) → f ≡ g
