Chuangjie Xu, 2012

\begin{code}

module Space-product where

open import Mini-library
open import Setoid
open import ConsHeadTail
open import Space
open import Uniform-continuity


-- Products of C-spaces

infixl 3 _⊗_

_⊗_ : Space → Space → Space
(X , P , pc₀ , pc₁ , pc₂ , pc₃) ⊗ (Y , Q , qc₀ , qc₁ , qc₂ , qc₃) =
                  X ✻ Y , R , rc₀ , rc₁ , rc₂ , rc₃
 where
  _≋_ : Ũ (X ✻ Y) → Ũ (X ✻ Y) → Set
  _≋_ = E (X ✻ Y)

  eπ₀ : E-map (X ✻ Y) X
  eπ₀ = E-π₀ {X} {Y}
  eπ₁ : E-map (X ✻ Y) Y
  eπ₁ = E-π₁ {X} {Y}

  R : Subset(E-map-₂ℕ (X ✻ Y))
  R r =   (⟨ X ✻ Y ∣ X ⟩ eπ₀ ◎ r ∈ P)
        ∧ (⟨ X ✻ Y ∣ Y ⟩ eπ₁ ◎ r ∈ Q)

  rc₀ : ∀(r : E-map-₂ℕ (X ✻ Y)) → constant {E₂ℕ} {X ✻ Y} r → r ∈ R
  rc₀ r cr = ∧-intro (pc₀ (⟨ X ✻ Y ∣ X ⟩ eπ₀ ◎ r) (λ α β → π₀ (cr α β)))
                     (qc₀ (⟨ X ✻ Y ∣ Y ⟩ eπ₁ ◎ r) (λ α β → π₁ (cr α β)))

  rc₁ : ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(r : E-map-₂ℕ (X ✻ Y)) → r ∈ R →
         ⟨ X ✻ Y ⟩ r ◎ t ∈ R
  rc₁ t uc r (pP , qQ) = ∧-intro (pc₁ t uc (⟨ X ✻ Y ∣ X ⟩ eπ₀ ◎ r) pP)
                                 (qc₁ t uc (⟨ X ✻ Y ∣ Y ⟩ eπ₁ ◎ r) qQ)

  rc₂ : ∀(r : E-map-₂ℕ (X ✻ Y)) →
         (∃ \(n : ℕ) → (s : ₂Fin n) → ⟨ X ✻ Y ⟩ r ◎ (E-cons s) ∈ R) →
         r ∈ R
  rc₂ r (n , f) = ∧-intro (pc₂ (⟨ X ✻ Y ∣ X ⟩ eπ₀ ◎ r) (n , λ s → ∧-elim₀(f s)))
                          (qc₂ (⟨ X ✻ Y ∣ Y ⟩ eπ₁ ◎ r) (n , λ s → ∧-elim₁(f s)))

  rc₃ : ∀(r r' : E-map-₂ℕ (X ✻ Y)) → (∀(α : ₂ℕ) → π₀ r α ≋ π₀ r' α) → r ∈ R → r' ∈ R
  rc₃ r r' f (pP , qQ) = ∧-intro (pc₃ (⟨ X ✻ Y ∣ X ⟩ eπ₀ ◎ r)
                                      (⟨ X ✻ Y ∣ X ⟩ eπ₀ ◎  r')
                                      (λ α → ∧-elim₀ (f α)) pP)
                                 (qc₃ (⟨ X ✻ Y ∣ Y ⟩ eπ₁ ◎ r)
                                      (⟨ X ✻ Y ∣ Y ⟩ eπ₁ ◎ r')
                                      (λ α → ∧-elim₁ (f α)) qQ)

\end{code}