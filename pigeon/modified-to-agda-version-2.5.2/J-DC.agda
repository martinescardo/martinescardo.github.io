module J-DC where

open import Logic
open import LogicalFacts
open import JK-LogicalFacts
open import Naturals
open import Addition
open import JK-Monads
open import Choice
open import Equality
open import J-Shift

-----------------------------------------------------------
--                                                       --
-- Translation of dependent choice for a particular case --
--                                                       --
-----------------------------------------------------------

J-∀-double-shift : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
---------------
     (∀(n : ℕ) → ∀(x : ℕ) → J∃ \(y : ℕ) → P n x y) →
     J(∀(n : ℕ) → ∀(x : ℕ) → ∃ \(y : ℕ) → P n x y)

J-∀-double-shift {R} f = J-∀-shift {R} (λ n → J-∀-shift (f n))


J-DC-ℕ : {R : Ω} {P : ℕ → ℕ → ℕ → Ω} →
-------
      ∀(x₀ : ℕ) → 
     (∀(n : ℕ) → ∀(x : ℕ) → J∃ \(y : ℕ) → P n x y) → 
     J∃ \(α : ℕ → ℕ) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(n + 1)))

J-DC-ℕ {R} x₀ f = (J-functor {R} (DC x₀)) (J-∀-double-shift f)
