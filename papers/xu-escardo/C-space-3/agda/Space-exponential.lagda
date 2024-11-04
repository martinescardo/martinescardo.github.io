Chuangjie Xu, 2012

\begin{code}

module Space-exponential where

open import Mini-library
open import Setoid
open import ConsHeadTail
open import Space
open import Uniform-continuity

-- Exponentials of C-spaces

exp : (X Y : Space) →
      E-map-₂ℕ (MapSetoid X Y) → E-map-₂ℕ-₂ℕ → E-map-₂ℕ (U X) →
      E-map-₂ℕ (U Y)
exp X Y (r , er) (t , et) (p , ep) = q , eq
 where
  _≈_ : Ũ (U Y) → Ũ (U Y) → Set
  _≈_ = E (U Y)
  q : ₂ℕ → Ũ (U Y)
  q α = π₀ (π₀ (r (t α))) (p α)
  eq : ∀(α β : ₂ℕ) → α ≣ β → q α ≈ q β
  eq α β e = Trans (U Y) (q α) (π₀ (π₀ (r (t β))) (p α)) (q β) claim₀ claim₁
   where
    claim₀ : π₀ (π₀ (r (t α))) (p α) ≈ π₀ (π₀ (r (t β))) (p α)
    claim₀ = er (t α) (t β) (et α β e) (p α)
    claim₁ : π₀ (π₀ (r (t β))) (p α) ≈ π₀ (π₀ (r (t β))) (p β)
    claim₁ = π₁ (π₀ (r (t β))) (p α) (p β) (ep α β e)


infixr 3 _⇒_

_⇒_ : Space → Space → Space
X ⇒ Y = MapSetoid X Y , R , rc₀ , rc₁ , rc₂ , rc₃
 where
  _~_ : Ũ (U X) → Ũ (U X) → Set
  _~_ = E (U X)
  _≈_ : Ũ (U Y) → Ũ (U Y) → Set
  _≈_ = E (U Y)
  _≋_ : Ũ (MapSetoid X Y) → Ũ (MapSetoid X Y) → Set
  _≋_ = E (MapSetoid X Y)

  R : Subset (E-map-₂ℕ (MapSetoid X Y))
  R r = ∀(p : E-map-₂ℕ (U X)) → p ∈ Probe X → ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → exp X Y r t p ∈ Probe Y

  rc₀ : ∀(r : E-map-₂ℕ (MapSetoid X Y)) → constant {E₂ℕ} {MapSetoid X Y} r → r ∈ R
  rc₀ r cr p pP t uc = cond₃ Y q (exp X Y r t p) claim₀ claim₁
   where
    q : E-map-₂ℕ (U Y)
    q = qq , eqq
     where
      qq : ₂ℕ → Ũ (U Y)
      qq = π₀ (π₀ (π₀ r 0̄)) ∘ (π₀ p)
      eqq : ∀(α β : ₂ℕ) → α ≣ β → qq α ≈ qq β
      eqq α β e = π₁ (π₀ (π₀ r 0̄)) (π₀ p α) (π₀ p β) (π₁ p α β e)
    claim₀ : ∀(α : ₂ℕ) → π₀ q α ≈ π₀ (exp X Y r t p) α
    claim₀ α = cr 0̄ (π₀ t α) (π₀ p α)
    claim₁ : q ∈ Probe Y
    claim₁ = π₁ (π₀ r 0̄) p pP

  rc₁ : ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(r : E-map-₂ℕ (MapSetoid X Y)) → r ∈ R →
         ⟨ MapSetoid X Y ⟩ r ◎ t ∈ R
  rc₁ t uc r rR p pP t' uc' = rR p pP (t ◎ t') (Lemma[◎-UC] t uc t' uc')

  rc₂ : ∀(r : E-map-₂ℕ (MapSetoid X Y)) →
         (∃ \(n : ℕ) → ∀(s : ₂Fin n) → ⟨ MapSetoid X Y ⟩ r ◎ (E-cons s) ∈ R) →
          r ∈ R
  rc₂ r (n , pr) p pP t uc = cond₂ Y (exp X Y r t p) (m , prf)
   where
    m : ℕ
    m = ∃-witness (Axiom[coverage] n t uc)
    prf : ∀(s : ₂Fin m) → ⟨ U Y ⟩ (exp X Y r t p) ◎ (E-cons s) ∈ Probe Y
    prf s = cond₃ Y q (⟨ U Y ⟩ (exp X Y r t p) ◎ (E-cons s)) claim₁ claim₂
     where
      s' : ₂Fin n
      s' = ∃-witness (∃-elim (Axiom[coverage] n t uc) s)
      t' : E-map-₂ℕ-₂ℕ
      t' = ∃-witness (∃-elim (∃-elim (Axiom[coverage] n t uc) s))
      uc' : t' ∈ C
      uc' = ∧-elim₀ (∃-elim (∃-elim (∃-elim (Axiom[coverage] n t uc) s)))
      q : E-map-₂ℕ (U Y)
      q = qq , eqq
       where
        qq : ₂ℕ → Ũ (U Y)
        qq α = π₀ (π₀ (π₀ r (cons s' (π₀ t' α)))) (π₀ p (cons s α))
        eqq : ∀(α β : ₂ℕ) → α ≣ β → qq α ≈ qq β
        eqq α β e = Trans (U Y) (π₀ (π₀ (π₀ r (cons s' (π₀ t' α)))) (π₀ p (cons s α)))
                                (π₀ (π₀ (π₀ r (cons s' (π₀ t' β)))) (π₀ p (cons s α)))
                                (π₀ (π₀ (π₀ r (cons s' (π₀ t' β)))) (π₀ p (cons s β)))
                                claim₂ claim₄
         where
          claim₀ : cons s' (π₀ t' α) ≣ cons s' (π₀ t' β)
          claim₀ = Lemma[cons-E-map] s' (π₀ t' α) (π₀ t' β) (π₁ t' α β e)
          claim₁ : π₀ r (cons s' (π₀ t' α)) ≋ π₀ r (cons s' (π₀ t' β))
          claim₁ = π₁ r (cons s' (π₀ t' α)) (cons s' (π₀ t' β)) claim₀
          claim₂ :  π₀ (π₀ (π₀ r (cons s' (π₀ t' α)))) (π₀ p (cons s α))
                  ≈ π₀ (π₀ (π₀ r (cons s' (π₀ t' β)))) (π₀ p (cons s α))
          claim₂ = claim₁ (π₀ p (cons s α))
          claim₃ : π₀ p (cons s α) ~ π₀ p (cons s β)
          claim₃ = π₁ p (cons s α) (cons s β) (Lemma[cons-E-map] s α β e)
          claim₄ :  π₀ (π₀ (π₀ r (cons s' (π₀ t' β)))) (π₀ p (cons s α))
                  ≈ π₀ (π₀ (π₀ r (cons s' (π₀ t' β)))) (π₀ p (cons s β))
          claim₄ = π₁ (π₀ (π₀ r (cons s' (π₀ t' β)))) (π₀ p (cons s α)) (π₀ p (cons s β)) claim₃
      claim₀ : ∀(α : ₂ℕ) → cons s' (π₀ t' α) ≣ π₀ t (cons s α)
      claim₀ α i = sym (∧-elim₁ (∃-elim (∃-elim (∃-elim (Axiom[coverage] n t uc) s))) α i)
      claim₁ : ∀(α : ₂ℕ) →  π₀ (π₀ (π₀ r (cons s' (π₀ t' α)))) (π₀ p (cons s α))
                          ≈ π₀ (π₀ (π₀ r (π₀ t (cons s α)))) (π₀ p (cons s α))
      claim₁ α = π₁ r (cons s' (π₀ t' α)) (π₀ t (cons s α)) (claim₀ α) (π₀ p (cons s α))
      claim₂ : q ∈ Probe Y
      claim₂ = pr s' (⟨ U X ⟩ p ◎ (E-cons s))
                     (cond₁ X (E-cons s) (Lemma[E-cons-UC] s) p pP) t' uc'

  rc₃ : ∀(r r' : E-map-₂ℕ (MapSetoid X Y)) → (∀(α : ₂ℕ) → π₀ r α ≋ π₀ r' α) → r ∈ R → r' ∈ R
  rc₃ r r' f rR p pP t uc = cond₃ Y (exp X Y r t p) (exp X Y r' t p) claim₀ claim₁
   where
    claim₀ : ∀(α : ₂ℕ) → π₀ (exp X Y r t p) α ≈ π₀ (exp X Y r' t p) α
    claim₀ α = f (π₀ t α) (π₀ p α)
    claim₁ : exp X Y r t p ∈ Probe Y
    claim₁ = rR p pP t uc

\end{code}