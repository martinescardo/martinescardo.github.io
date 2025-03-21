module Choice where

open import Logic
open import Induction
open import Equality

AC : {X : Set} {Y : X → Set} {A : (x : X) → Y x → Ω} →
--
      (∀(x : X) → ∃(\(y : Y x) → A x y))
     → ∃(\(f : ((x : X) → Y x)) → ∀(x : X) → A x (f x))

AC g = ∃-intro (\x → ∃-witness (g x)) (\x → ∃-elim (g x))


DC : {X : Set} {P : ℕ → X → X → Ω} →
--
    ∀(x₀ : X) → (∀(n : ℕ) → ∀(x : X) → ∃(\(y : X) → P n x y))
 →  ∃(\(α : ℕ → X) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(succ n))))

DC {X} x₀ g = ∃-intro α (∧-intro reflexivity (\n → ∃-elim(g n (α n))))
    where α : ℕ → X
          α = induction x₀ (λ k x → ∃-witness(g k x)) 

-- Dependently typed, dependent choice:

DDC : {X : ℕ → Set} {P : (n : ℕ) → X n → X(succ n) → Ω} →
---
    ∀(x₀ : X O) → (∀(n : ℕ) → ∀(x : X n) → ∃(\(y : X(succ n)) → P n x y))
 →  ∃(\(α : (n : ℕ) → X n) → α O ≡ x₀ ∧ (∀(n : ℕ) → P n (α n) (α(succ n))))

DDC {X} x₀ g = ∃-intro α (∧-intro reflexivity (\n → ∃-elim(g n (α n))))
    where α : (n : ℕ) → X n
          α = induction x₀ (λ k x → ∃-witness(g k x)) 
