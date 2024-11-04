Chuangjie Xu, 2012

\begin{code}

module Space-discrete where

open import Mini-library
open import Setoid
open import ConsHeadTail
open import Space
open import Uniform-continuity

\end{code}

The locally constant functions ₂ℕ → X on any set X form a
C-topology on X. Any space with such a C-topology is
discrete, i.e. all maps from it to any other space is continuous.

\begin{code}

LC-topology : (X : Setoid) → probe-axioms X (locally-constant {X})
LC-topology X = c₀ , c₁ , c₂ , c₃
 where
  _~_ : Ũ X → Ũ X → Set
  _~_ = E X

  LC : Subset (E-map-₂ℕ X)
  LC = locally-constant {X}

  c₀ : ∀(p : E-map-₂ℕ X) → constant {E₂ℕ} {X} p → p ∈ LC
  c₀ p cp = 0 , λ α β aw → cp α β

  c₁ : ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(p : E-map-₂ℕ X) → p ∈ LC →
        ⟨ X ⟩ p ◎ t ∈ LC
  c₁ (t , _) uc (p , _) (n , pr) = m , prf
   where
    m : ℕ
    m = ∃-witness (uc n)
    prf : ∀(α β : ₂ℕ) → α ≣ m ≣ β → p (t α) ~ p (t β)
    prf α β aw = pr (t α) (t β) (∃-elim (uc n) α β aw)

  c₂ : ∀(p : E-map-₂ℕ X) →
        (∃ \(n : ℕ) → ∀(s : ₂Fin n) → ⟨ X ⟩ p ◎ (E-cons s) ∈ LC) →
        p ∈ LC
  c₂ (p , ep) (n , pr) = m , prf
   where
    f : ₂Fin n → ℕ
    f s = ∃-witness (pr s)
    max-of-f : ∃ \(k : ℕ) → ∀(s : ₂Fin n) → f s ≤ k
    max-of-f = max-fin f
    k : ℕ
    k = ∃-witness max-of-f
    m : ℕ
    m = n + k
    prf : ∀(α β : ₂ℕ) → α ≣ m ≣ β → p α ~ p β
    prf α β awm = goal
     where
      awn : α ≣ n ≣ β
      awn i i<n = awm i (Lemma[a≤b≤c→a≤c] i<n (Lemma[a≤a+b] n k))
      claim₀ : take n α ≡ take n β
      claim₀ = Lemma[≣_≣-take] n α β awn
      s : ₂Fin n
      s = take n α
      α' : ₂ℕ
      α' = drop n α
      β' : ₂ℕ
      β' = drop n β
      claim₁ : α ≣ cons s α'
      claim₁ i = sym (Lemma[cons-take-drop] n α i)
      claim₂ : p α ~ p (cons s α')
      claim₂ = ep α (cons s α') claim₁
      claim₃ : cons s β' ≣ β
      claim₃ i = subst {₂Fin n} {λ x → cons x β' i ≡ β i}
                       (sym claim₀) (Lemma[cons-take-drop] n β i)
      claim₄ : p (cons s β') ~ p β
      claim₄ = ep (cons s β') β claim₃
      awk : α' ≣ k ≣ β'
      awk = Lemma[≣_≣-drop] n k α β awm
      claim₅ : p (cons s α') ~ p (cons s β')
      claim₅ = ∃-elim (pr s) α' β' (λ i r → awk i (Lemma[a<b≤c→a<c] r (∃-elim max-of-f s)))
      claim₆ : p α ~ p (cons s β')
      claim₆ = Trans X (p α) (p (cons s α')) (p (cons s β')) claim₂ claim₅
      goal : p α ~ p β
      goal = Trans X (p α) (p (cons s β')) (p β) claim₆ claim₄

  c₃ : ∀(p p' : E-map-₂ℕ X) → (∀(α : ₂ℕ) → π₀ p α ~ π₀ p' α) → p ∈ LC → p' ∈ LC
  c₃ (p , _) (p' , _) f (n , pr) = n , prf
   where
    prf : ∀(α β : ₂ℕ) → α ≣ n ≣ β → p' α ~ p' β
    prf α β aw = goal
     where
      claim₀ : p' α ~ p α
      claim₀ = Sym X (p α) (p' α) (f α)
      claim₁ : p' α ~ p β
      claim₁ = Trans X (p' α) (p α) (p β) claim₀ (pr α β aw)
      goal : p' α ~ p' β
      goal = Trans X (p' α) (p β) (p' β) claim₁ (f β)


Discrete-Space : Setoid → Space
Discrete-Space X = X , locally-constant {X} , LC-topology X

\end{code}

All the uniformly continuous maps ₂ℕ → ₂ (and ₂ℕ → ℕ) are
locally constant. And hence they form a C-topology for ₂ (and ℕ).

\begin{code}

-- The coproduct 1 + 1

₂Space : Space
₂Space = Discrete-Space (E₂)


-- The natural numbers object

ℕSpace : Space
ℕSpace = Discrete-Space (Eℕ)


Lemma[discreteness] : {X : Setoid} → ∀{Y : Space} → ∀(f : E-map X (U Y)) →
                       continuous {Discrete-Space X} {Y} f
Lemma[discreteness] {X} {Y , Q , qc₀ , _ , qc₂ , _} f p (n , pr) = qc₂ f∘p (n , prf)
 where
  f∘p : E-map-₂ℕ Y
  f∘p = ⟨ X ∣ Y ⟩ f ◎ p
  prf : ∀(s : ₂Fin n) → ⟨ Y ⟩ f∘p ◎ (E-cons s) ∈ Q
  prf s = qc₀ fps claim₁
   where
    fps : E-map-₂ℕ Y
    fps = ⟨ Y ⟩ f∘p ◎ (E-cons s)
    claim₀ : constant {E₂ℕ} {X} (⟨ X ⟩ p ◎ (E-cons s))
    claim₀ α β = pr (cons s α) (cons s β) (Lemma[cons-≣_≣] s α β)
    claim₁ : constant {E₂ℕ} {Y} fps
    claim₁ α β = π₁ f (π₀ p (cons s α)) (π₀ p (cons s β)) (claim₀ α β)

\end{code}