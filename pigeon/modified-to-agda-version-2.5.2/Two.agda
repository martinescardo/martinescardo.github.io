module Two where

data ₂ : Set where
 ₀ : ₂
 ₁ : ₂

not : ₂ → ₂
not ₀ = ₁
not ₁ = ₀

open import Logic
open import Equality

two-equality-cases : {R : Ω} → 
 ∀(b : ₂) → (b ≡ ₀ → R) → (b ≡ ₁ → R) → R

two-equality-cases ₀  f₀ f₁ = f₀ reflexivity
two-equality-cases ₁  f₀ f₁ = f₁ reflexivity

