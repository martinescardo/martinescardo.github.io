Chuangjie Xu, 2012

\begin{code}

module Space-exponential where

open import Mini-library
open [_]
open import ConsHeadTail
open import Space

-- Exponentials of C-spaces

infixr 3 _⇒_

_⇒_ : Space → Space → Space
(X , P , P-conds) ⇒ (Y , Q , qc₀ , qc₁ , qc₂ , qc₃) =
            CtsXtoY , R , rc₀ , rc₁ , rc₂ , rc₃
 where
  CtsXtoY : Set
  CtsXtoY = Σ \(f : X → Y) →
             continuous {X , P , P-conds} {Y , Q , qc₀ , qc₁ , qc₂ , qc₃} f

  R : Subset(₂ℕ → CtsXtoY)
  R r = ∀(p : ₂ℕ → X) → p ∈ P → ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
                                (λ α → (π₀ ∘ r)(t α)(p α)) ∈ Q

  rc₀ : ∀(r : ₂ℕ → CtsXtoY) → constant r → r ∈ R
  rc₀ r cr p pP t uc = qc₃ ((π₀(r 0̄)) ∘ p)
                          (λ α → (π₀ ∘ r)(t α)(p α)) claim₀ claim₁
   where
    claim₀ : (π₀(r 0̄)) ∘ p ∈ Q
    claim₀ = π₁(r 0̄) p pP
    claim₁ : [ (∀(α : ₂ℕ) → π₀(r 0̄)(p α) ≡ (π₀ ∘ r)(t α)(p α)) ]
    claim₁ = hide (λ α → (fun-cong (cong π₀ (reveal cr 0̄ (t α))) (p α)))

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
    prf s' = qc₃ (λ α → (π₀ ∘ r)(cons s'' (t'' α))(p(cons s' α)))
                 (λ α → (π₀ ∘ r)(t (cons s' α))(p(cons s' α)))
                 claim₀ claim₁
     where
      s'' : ₂Fin n
      s'' = ∃-witness (∃-elim (coverage-axiom n t uc) s')
      t'' : ₂ℕ → ₂ℕ
      t'' = ∃-witness (∃-elim (∃-elim (coverage-axiom n t uc) s'))
      uct'' : uniformly-continuous-₂ℕ t''
      uct'' = ∧-elim₀ (∃-elim (∃-elim (∃-elim (coverage-axiom n t uc) s')))
      eq : [ t ∘ (cons s') ≡ (cons s'') ∘ t'' ]
      eq = ∧-elim₁ (∃-elim (∃-elim (∃-elim (coverage-axiom n t uc) s')))
      ps'inP : (p ∘ (cons s')) ∈ P
      ps'inP = ∧-elim₀ (∧-elim₁ P-conds) (cons s') (Lemma[cons-UC] s') p pP
      claim₀ : (λ α → (π₀ ∘ r)(cons s'' (t'' α))(p(cons s' α))) ∈ Q
      claim₀ = ps s'' (p ∘ (cons s')) ps'inP t'' uct''
      claim₁ : [ (∀(α : ₂ℕ) → (π₀ ∘ r)(cons s'' (t'' α))(p(cons s' α)) ≡
                              (π₀ ∘ r)(t(cons s' α))(p(cons s' α))) ]
      claim₁ = hide (λ α → cong (λ x → (π₀ ∘ r)(x α)(p(cons s' α))) (sym (reveal eq)))

  rc₃ : ∀(r r' : ₂ℕ → CtsXtoY) → r ∈ R → [ ((α : ₂ℕ) → r α ≡ r' α) ] → r' ∈ R
  rc₃ r r' rR f p pP t uct = qc₃ (λ α → (π₀ ∘ r)(t α)(p α))
                                 (λ α → (π₀ ∘ r')(t α)(p α))
                                 (rR p pP t uct) claim
   where
    claim : [ (∀(α : ₂ℕ) → (π₀ ∘ r)(t α)(p α) ≡ (π₀ ∘ r')(t α)(p α)) ]
    claim = hide (λ α → fun-cong (cong π₀ (reveal f (t α))) (p α))

\end{code}