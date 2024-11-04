Chuangjie Xu 2012

\begin{code}

module Space-coproduct where

open import Mini-library
open import Setoid
open import ConsHeadTail
open import Space
open import Uniform-continuity


infixl 3 _⊕_

_⊕_ : Space → Space → Space
(X , P , pc₀ , pc₁ , pc₂ , pc₃) ⊕ (Y , Q , qc₀ , qc₁ , qc₂ , qc₃) =
                  X ✣ Y , R , rc₀ , rc₁ , rc₂ , rc₃
 where
  _≋_ : Ũ (X ✣ Y) → Ũ (X ✣ Y) → Set
  _≋_ = E (X ✣ Y)

  lemma-≋ : ∀(z : Ũ (X ✣ Y)) → (∃ \(x : Ũ X) → z ≋ in₀ x) ∨ (∃ \(y : Ũ Y) → z ≋ in₁ y)
  lemma-≋ (in₀ x) = in₀ (x , Refl X x)
  lemma-≋ (in₁ y) = in₁ (y , Refl Y y)

  R : Subset (E-map-₂ℕ (X ✣ Y))
  R r = ∃ \(n : ℕ) → ∀(s : ₂Fin n) →
            (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p α)))
          ∨ (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q α)))

  rc₀ : ∀(r : E-map-₂ℕ (X ✣ Y)) → constant {E₂ℕ} {X ✣ Y} r → r ∈ R
  rc₀ r cr = 0 , prf
   where
    claim₀ : (∃ \(x : Ũ X) → π₀ r 0̄ ≋ in₀ x) →
             ∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons ⟨⟩ α) ≋ in₀ (π₀ p α))
    claim₀ (x , eq) = p , pP , f
     where
      p : E-map-₂ℕ X
      p = (λ α → x) , (λ α β eq → Refl X x)
      pP : p ∈ P
      pP = pc₀ p (λ α β → Refl X x)
      f : ∀(α : ₂ℕ) → π₀ r (cons ⟨⟩ α) ≋ in₀ x
      f α = Trans (X ✣ Y) (π₀ r (cons ⟨⟩ α)) (π₀ r 0̄) (in₀ x) (cr (cons ⟨⟩ α) 0̄) eq
    claim₁ : (∃ \(y : Ũ Y) → π₀ r 0̄ ≋ in₁ y) →
             ∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons ⟨⟩ α) ≋ in₁ (π₀ q α))
    claim₁ (y , eq) = q , qQ , f
     where
      q : E-map-₂ℕ Y
      q = (λ α → y) , (λ α β eq → Refl Y y)
      qQ : q ∈ Q
      qQ = qc₀ q (λ α β → Refl Y y)
      f : ∀(α : ₂ℕ) → π₀ r (cons ⟨⟩ α) ≋ in₁ y
      f α = Trans (X ✣ Y) (π₀ r (cons ⟨⟩ α)) (π₀ r 0̄) (in₁ y) (cr (cons ⟨⟩ α) 0̄) eq
    prf : ∀(s : ₂Fin 0) →
            (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p α)))
          ∨ (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q α)))
    prf ⟨⟩ = cases claim₀ claim₁ (lemma-≋ (π₀ r 0̄))

  rc₁ : ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(r : E-map-₂ℕ (X ✣ Y)) → r ∈ R →
         ⟨ X ✣ Y ⟩ r ◎ t ∈ R
  rc₁ t uc r (n , f) = m , prf
   where
    m : ℕ
    m = ∃-witness (uc n)
    prf : ∀(s : ₂Fin m) →
            (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (π₀ t (cons s α)) ≋ in₀ (π₀ p α)))
          ∨ (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (π₀ t (cons s α)) ≋ in₁ (π₀ q α)))
    prf s = cases claim₀ claim₁ (f s')
     where
      s' : ₂Fin n
      s' = ∃-witness (∃-elim (Axiom[coverage] n t uc) s)
      t' : E-map-₂ℕ-₂ℕ
      t' = ∃-witness (∃-elim (∃-elim (Axiom[coverage] n t uc) s))
      uc' : t' ∈ C
      uc' = ∧-elim₀ (∃-elim (∃-elim (∃-elim (Axiom[coverage] n t uc) s)))
      eq : ∀(α : ₂ℕ) → π₀ t (cons s α) ≣ cons s' (π₀ t' α)
      eq = ∧-elim₁ (∃-elim (∃-elim (∃-elim (Axiom[coverage] n t uc) s)))
      claim₀ : (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s' α) ≋ in₀ (π₀ p α))) →
                ∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (π₀ t (cons s α)) ≋ in₀ (π₀ p α))
      claim₀ (p , pP , h) = pt' , pt'P , h'
       where
        pt' : E-map-₂ℕ X
        pt' = ⟨ X ⟩ p ◎ t'
        pt'P : pt' ∈ P
        pt'P = pc₁ t' uc' p pP
        h' : ∀(α : ₂ℕ) → π₀ r (π₀ t (cons s α)) ≋ in₀ (π₀ p (π₀ t' α))
        h' α = Trans (X ✣ Y) (π₀ r (π₀ t (cons s α))) (π₀ r (cons s' (π₀ t' α))) (in₀ (π₀ p (π₀ t' α)))
                             (π₁ r (π₀ t (cons s α)) (cons s' (π₀ t' α)) (eq α)) (h (π₀ t' α))
      claim₁ : (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s' α) ≋ in₁ (π₀ q α))) →
                ∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (π₀ t (cons s α)) ≋ in₁ (π₀ q α))
      claim₁ (q , qQ , h) = qt' , qt'Q , h'
       where
        qt' : E-map-₂ℕ Y
        qt' = ⟨ Y ⟩ q ◎ t'
        qt'Q : qt' ∈ Q
        qt'Q = qc₁ t' uc' q qQ
        h' : ∀(α : ₂ℕ) → π₀ r (π₀ t (cons s α)) ≋ in₁ (π₀ q (π₀ t' α))
        h' α = Trans (X ✣ Y) (π₀ r (π₀ t (cons s α))) (π₀ r (cons s' (π₀ t' α))) (in₁ (π₀ q (π₀ t' α)))
                             (π₁ r (π₀ t (cons s α)) (cons s' (π₀ t' α)) (eq α)) (h (π₀ t' α))

  rc₂ : ∀(r : E-map-₂ℕ (X ✣ Y)) →
         (∃ \(n : ℕ) → (s : ₂Fin n) → ⟨ X ✣ Y ⟩ r ◎ (E-cons s) ∈ R) → r ∈ R
  rc₂ r (n , f) = k + n , prf
   where
    k : ℕ
    k = ∃-witness (max-fin (λ s → ∃-witness (f s)))
    prf : ∀(s : ₂Fin (k + n)) →
            (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p α)))
          ∨ (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q α)))
    prf s = cases claim₀ claim₁ (∃-elim (f s₀) s₁)
     where
      s₀ : ₂Fin n
      s₀ = Ftake k n s
      l : ℕ
      l = ∃-witness (f s₀)
      l≤k : l ≤ k
      l≤k = ∃-elim (max-fin (λ s → ∃-witness (f s))) s₀
      m : ℕ
      m = ∃-witness (Lemma[≤-∃] l k l≤k)
      eq : k ≡ m + l
      eq = trans (sym (∃-elim (Lemma[≤-∃] l k l≤k))) (Lemma[n+m=m+n] l m)
      s₁ : ₂Fin l
      s₁ = Ftake m l (subst {ℕ} {λ x → ₂Fin x} eq (Fdrop k n s))
      s₂ : ₂Fin m
      s₂ = Fdrop m l (subst {ℕ} {λ x → ₂Fin x} eq (Fdrop k n s))
      lemma : ∀(α : ₂ℕ) → cons s α ≣ cons s₀ (cons s₁ (cons s₂ α))
      lemma α i = sym (Lemma[cons-Ftake-Fdrop]² n m l k eq s α i)
      claim₀ : (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s₀ (cons s₁ α)) ≋ in₀ (π₀ p α))) →
                ∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p α))
      claim₀ (p , pP , f) = ps₂ , ps₂P , f'
       where
        ps₂ : E-map-₂ℕ X
        ps₂ = ⟨ X ⟩ p ◎ (E-cons s₂)
        ps₂P : ps₂ ∈ P
        ps₂P = pc₁ (E-cons s₂) (Lemma[E-cons-UC] s₂) p pP
        f' : ∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p (cons s₂ α))
        f' α = Trans (X ✣ Y) (π₀ r (cons s α))
                             (π₀ r (cons s₀ (cons s₁ (cons s₂ α))))
                             (in₀ (π₀ p (cons s₂ α)))
                             (π₁ r (cons s α) (cons s₀ (cons s₁ (cons s₂ α))) (lemma α))
                             (f (cons s₂ α))
      claim₁ : (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s₀ (cons s₁ α)) ≋ in₁ (π₀ q α))) →
                ∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q α))
      claim₁ (q , qQ , f) = qs₂ , qs₂Q , f'
       where
        qs₂ : E-map-₂ℕ Y
        qs₂ = ⟨ Y ⟩ q ◎ (E-cons s₂)
        qs₂Q : qs₂ ∈ Q
        qs₂Q = qc₁ (E-cons s₂) (Lemma[E-cons-UC] s₂) q qQ
        f' : ∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q (cons s₂ α))
        f' α = Trans (X ✣ Y) (π₀ r (cons s α))
                             (π₀ r (cons s₀ (cons s₁ (cons s₂ α))))
                             (in₁ (π₀ q (cons s₂ α)))
                             (π₁ r (cons s α) (cons s₀ (cons s₁ (cons s₂ α))) (lemma α))
                             (f (cons s₂ α))

  rc₃ : ∀(r r' : E-map-₂ℕ (X ✣ Y)) → (∀(α : ₂ℕ) → π₀ r α ≋ π₀ r' α) → r ∈ R → r' ∈ R
  rc₃ r r' eq (n , f) = n , f'
   where
    f' : ∀(s : ₂Fin n) →
           (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r' (cons s α) ≋ in₀ (π₀ p α)))
         ∨ (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r' (cons s α) ≋ in₁ (π₀ q α)))
    f' s = cases claim₀ claim₁ (f s)
     where
      claim₀ : (∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p α))) →
                ∃ \(p : E-map-₂ℕ X) → (p ∈ P) ∧ (∀(α : ₂ℕ) → π₀ r' (cons s α) ≋ in₀ (π₀ p α))
      claim₀ (p , pP , h) = p , pP , h'
       where
        h' : ∀(α : ₂ℕ) → π₀ r' (cons s α) ≋ in₀ (π₀ p α)
        h' α = Trans (X ✣ Y) (π₀ r' (cons s α)) (π₀ r (cons s α)) (in₀ (π₀ p α))
                     (Sym (X ✣ Y) (π₀ r (cons s α)) (π₀ r' (cons s α)) (eq (cons s α))) (h α)
      claim₁ : (∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q α))) →
                ∃ \(q : E-map-₂ℕ Y) → (q ∈ Q) ∧ (∀(α : ₂ℕ) → π₀ r' (cons s α) ≋ in₁ (π₀ q α))
      claim₁ (q , qQ , h) = q , qQ , h'
       where
        h' : ∀(α : ₂ℕ) → π₀ r' (cons s α) ≋ in₁ (π₀ q α)
        h' α = Trans (X ✣ Y) (π₀ r' (cons s α)) (π₀ r (cons s α)) (in₁ (π₀ q α))
                     (Sym (X ✣ Y) (π₀ r (cons s α)) (π₀ r' (cons s α)) (eq (cons s α))) (h α)

\end{code}
