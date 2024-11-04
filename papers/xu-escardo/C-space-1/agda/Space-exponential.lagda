Chuangjie Xu, 2012

\begin{code}

module Space-exponential where

open import Mini-library
open import Cons
open import Space
open import Extensionality

-- Exponentials of C-spaces

infixr 3 _⇒_

_⇒_ : Space → Space → Space
(X , P , P-conds) ⇒ (Y , Q , qc₀ , qc₁ , qc₂) =
            CtsXtoY , R , rc₀ , rc₁ , rc₂
 where
  CtsXtoY : Set
  CtsXtoY = Σ \(f : X → Y) →
             continuous {X , P , P-conds} {Y , Q , qc₀ , qc₁ , qc₂} f

  R : Subset(₂ℕ → CtsXtoY)
  R r = ∀(p : ₂ℕ → X) → p ∈ P → ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
                                (λ α → (π₀ ∘ r)(t α)(p α)) ∈ Q

  rc₀ : ∀(r : ₂ℕ → CtsXtoY) → constant r → r ∈ R
  rc₀ r cr p pP t uct = subst {₂ℕ → Y} {λ q → q ∈ Q} claim₂ claim₀
   where
    claim₀ : (π₀(r 0̄)) ∘ p ∈ Q
    claim₀ = π₁(r 0̄) p pP
    claim₁ : ∀(α : ₂ℕ) → π₀(r 0̄)(p α) ≡ (π₀ ∘ r) (t α) (p α)
    claim₁ α = fun-cong (cong π₀ (cr 0̄ (t α))) (p α)
    claim₂ : (π₀(r 0̄)) ∘ p ≡ λ α → (π₀ ∘ r)(t α)(p α)
    claim₂ = extensionality claim₁
             --------------

  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → uniformly-continuous-₂ℕ t →
             ∀(r : ₂ℕ → CtsXtoY) → r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rR p pP t' uc' = rR p pP (t ∘ t') (Lemma[∘-UC] t uc t' uc')

  rc₂ : ∀(r : ₂ℕ → CtsXtoY) →
         (∃ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r ex p pP t uc = qc₂ (λ α → (π₀ ∘ r)(t α)(p α)) (∃-intro n' prf)
   where
    n : ℕ
    n = ∃-witness ex
    ps : ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R
    ps = ∃-elim ex
    n' : ℕ
    n' = ∃-witness (coverage-axiom n t uc)
    prf : ∀(s' : ₂Fin n') → (λ α → (π₀ ∘ r)(t(cons s' α))(p(cons s' α))) ∈ Q
    prf s' = subst {₂ℕ → Y} {λ q → q ∈ Q} claim₂ claim₀
     where
      s'' : ₂Fin n
      s'' = ∃-witness (∃-elim (coverage-axiom n t uc) s')
      t'' : ₂ℕ → ₂ℕ
      t'' = ∃-witness (∃-elim (∃-elim (coverage-axiom n t uc) s'))
      uct'' : uniformly-continuous-₂ℕ t''
      uct'' = ∧-elim₀ (∃-elim (∃-elim (∃-elim (coverage-axiom n t uc) s')))
      eq : t ∘ (cons s') ≡ (cons s'') ∘ t''
      eq = ∧-elim₁ (∃-elim (∃-elim (∃-elim (coverage-axiom n t uc) s')))
      ps'inP : (p ∘ (cons s')) ∈ P
      ps'inP = ∧-elim₀ (∧-elim₁ P-conds) (cons s') (Lemma[cons-UC] s') p pP
      claim₀ : (λ α → (π₀ ∘ r)(cons s'' (t'' α))(p(cons s' α))) ∈ Q
      claim₀ = ps s'' (p ∘ (cons s')) ps'inP t'' uct''
      claim₁ : ∀(α : ₂ℕ) → (π₀ ∘ r)(cons s'' (t'' α))(p(cons s' α)) ≡
                           (π₀ ∘ r)(t(cons s' α))(p(cons s' α))
      claim₁ α = cong (λ x → (π₀ ∘ r)(x α)(p(cons s' α))) (sym eq)
      claim₂ :  (λ α → (π₀ ∘ r)(cons s'' (t'' α))(p(cons s' α)))
              ≡ (λ α → (π₀ ∘ r)(t (cons s' α))(p(cons s' α)))
      claim₂ = extensionality claim₁
               --------------

\end{code}