Chuangjie Xu, 2012

\begin{code}

module Space-product where

open import Mini-library
open import Cons
open import Space


-- Products of C-spaces

infixl 3 _⊗_

_⊗_ : Space → Space → Space
(X , P , pc₀ , pc₁ , pc₂) ⊗ (Y , Q , qc₀ , qc₁ , qc₂) =
                  X × Y , R , rc₀ , rc₁ , rc₂
 where
  R : Subset(₂ℕ → X × Y)
  R r = ((π₀ ∘ r) ∈ P) ∧ ((π₁ ∘ r) ∈ Q)

  rc₀ : ∀(r : ₂ℕ → X × Y) → constant r → r ∈ R
  rc₀ r cr = ∧-intro c₀ c₁
   where
    c₀ : π₀ ∘ r ∈ P
    c₀ = pc₀ (π₀ ∘ r) (λ α β → cong π₀ (cr α β))
    c₁ : π₁ ∘ r ∈ Q
    c₁ = qc₀ (π₁ ∘ r) (λ α β → cong π₁ (cr α β))

  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(r : ₂ℕ → X × Y) →  r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rinR = ∧-intro c₀ c₁
   where
    c₀ : π₀ ∘ (r ∘ t) ∈ P
    c₀ = pc₁ t uc (π₀ ∘ r) (∧-elim₀ rinR)
    c₁ : π₁ ∘ (r ∘ t) ∈ Q
    c₁ = qc₁ t uc (π₁ ∘ r) (∧-elim₁ rinR)

  rc₂ : ∀(r : ₂ℕ → X × Y) → (∃ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r ex = ∧-intro c₀ c₁
   where
    n : ℕ
    n = ∃-witness ex
    prf : ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R
    prf = ∃-elim ex
    c₀ : π₀ ∘ r ∈ P
    c₀ = pc₂ (π₀ ∘ r) (∃-intro n (λ s → ∧-elim₀(prf s)))
    c₁ : π₁ ∘ r ∈ Q
    c₁ = qc₂ (π₁ ∘ r) (∃-intro n (λ s → ∧-elim₁(prf s)))

\end{code}