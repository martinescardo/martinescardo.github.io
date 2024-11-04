Chuangjie Xu 2012

(Modified 9th Nov 2017 to use cubicaltt instead of a postulate).

\begin{code}

{-# OPTIONS --cubical  --without-K #-}

module UsingFunext.Funext where

open import Preliminaries.SetsAndFunctions using (_≡_ ; refl ; Funext)
open import Primitives renaming (_≡_ to _≣_ ; primIdPath to fromPath')
open import Id renaming (pathToId to fromPath)
open import PathPrelude public using () renaming (funExt to funExtPath)
  
toPath : ∀ {i} {X : Set i} {x y : X} → x ≡ y → x ≣ y
toPath {i} {X} {x} = J P base
  where
   P : (y : X) → Id x y → Set i
   P y p = x ≣ y
   base : P x (reflId)
   base = λ i → x

-- fromPath : ∀ {i} {X : Set i} {x y : X} → x ≣ y → Id x y

funext : Funext
funext h = fromPath (funExtPath λ x → toPath(h x))

funext² : {X : Set}
          {Y : X → Set}
          {Z : (x : X) → (y : Y x) → Set} →
          {f g : (x : X) → (y : Y x) → Z x y}
        → (∀ x y → f x y ≡ g x y) → f ≡ g
funext² ex = funext (λ x → funext (ex x))

funext³ : {X : Set}
          {Y : X → Set}
          {Z : (x : X) → Y x → Set}
          {W : (x : X) → (y : Y x) → Z x y → Set}
          {f g : (x : X) → (y : Y x) → (z : Z x y) → W x y z}
        → (∀ x y z → f x y z ≡ g x y z) → f ≡ g
funext³ ex = funext (λ x → funext (λ y → funext (ex x y)))

funext⁴ : {X : Set}
          {Y : X → Set}
          {Z : (x : X) → Y x → Set}
          {W : (x : X) → (y : Y x) → Z x y → Set}
          {U : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → Set}
          {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w}
        → (∀ x y z w → f x y z w ≡ g x y z w) → f ≡ g
funext⁴ ex = funext (λ x → funext (λ y → funext (λ z → funext (ex x y z))))

funext⁵ : {X : Set}
          {Y : X → Set}
          {Z : (x : X) → Y x → Set}
          {W : (x : X) → (y : Y x) → Z x y → Set}
          {U : (x : X) → (y : Y x) → (z : Z x y) → W x y z → Set}
          {V : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w → Set}
          {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → (u : U x y z w) → V x y z w u}
        → (∀ x y z w u → f x y z w u ≡ g x y z w u) → f ≡ g
funext⁵ ex = funext (λ x → funext (λ y → funext (λ z → funext (λ w → funext (ex x y z w)))))

\end{code}
