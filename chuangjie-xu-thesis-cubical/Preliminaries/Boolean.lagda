Chuangjie Xu, 2014

(Changes not needed for the cubical version of 9th Nov 2017)

\begin{code}

{-# OPTIONS --without-K #-}

module Preliminaries.Boolean where

open import Preliminaries.SetsAndFunctions
open import Preliminaries.HSet

\end{code}

Booleans, basic operations and properties

\begin{code}

data ₂ : Set where
 ₀ : ₂
 ₁ : ₂

{-# BUILTIN BOOL ₂ #-}

if : {X : Set} → ₂ → X → X → X
if ₀ x₀ x₁ = x₀
if ₁ x₀ x₁ = x₁

Lemma[₁≠₀] : ₁ ≠ ₀
Lemma[₁≠₀] p = idtofun a ⋆
 where
   f : ₂ → Set
   f ₀ = ∅
   f ₁ = ⒈
   a : ⒈ ≡ ∅ 
   a = ap f p 

Lemma[₀≠₁] : ₀ ≠ ₁
Lemma[₀≠₁] p = Lemma[₁≠₀](p ⁻¹)

₂-discrete : discrete ₂
₂-discrete ₀ ₀ = inl refl 
₂-discrete ₀ ₁ = inr Lemma[₀≠₁]
₂-discrete ₁ ₀ = inr Lemma[₁≠₀]
₂-discrete ₁ ₁ = inl refl

₂-hset : hset ₂
₂-hset = discrete-is-hset ₂-discrete

Lemma[b≡₀∨b≡₁] : ∀{b : ₂} → (b ≡ ₀) + (b ≡ ₁)
Lemma[b≡₀∨b≡₁] {₀} = inl refl
Lemma[b≡₀∨b≡₁] {₁} = inr refl

Lemma[b≠₀→b≡₁] : {b : ₂} → ¬ (b ≡ ₀) → b ≡ ₁
Lemma[b≠₀→b≡₁] {₀} f = ∅-elim (f refl)
Lemma[b≠₀→b≡₁] {₁} f = refl

Lemma[b≠₁→b≡₀] : {b : ₂} → ¬ (b ≡ ₁) → b ≡ ₀
Lemma[b≠₁→b≡₀] {₀} f = refl
Lemma[b≠₁→b≡₀] {₁} f = ∅-elim (f refl)

\end{code}
