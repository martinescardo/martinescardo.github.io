\begin{code}

module Cons where

open import Mini-library


-- The concatenation maps and some of their properties

cons : {m : ℕ} → ₂Fin m → ₂ℕ → ₂ℕ
cons ⟨⟩      α i        = α i
cons (h ∷ _) α 0        = h
cons (_ ∷ t) α (succ i) = cons t α i


Lemma[cons-≣_≣] : {n : ℕ} → ∀(s : ₂Fin n) → ∀(α β : ₂ℕ) → cons s α ≣ n ≣ cons s β
Lemma[cons-≣_≣] ⟨⟩      α β i        ()
Lemma[cons-≣_≣] (b ∷ s) α β 0        r          = refl
Lemma[cons-≣_≣] (b ∷ s) α β (succ i) (≤-succ r) = Lemma[cons-≣_≣] s α β i r

Lemma[cons-take-≣_≣] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ cons (take n α) β
Lemma[cons-take-≣_≣] 0        α β i        ()
Lemma[cons-take-≣_≣] (succ n) α β 0        r          = refl
Lemma[cons-take-≣_≣] (succ n) α β (succ i) (≤-succ r) = Lemma[cons-take-≣_≣] n (α ∘ succ) β i r

Lemma[cons-take-drop] : ∀(n : ℕ) → ∀(α : ₂ℕ) →
                         ∀(i : ℕ) → cons (take n α) (drop n α) i ≡ α i
Lemma[cons-take-drop] 0        α i        = refl
Lemma[cons-take-drop] (succ n) α 0        = refl
Lemma[cons-take-drop] (succ n) α (succ i) = Lemma[cons-take-drop] n (α ∘ succ) i


Lemma[cons-drop] : ∀(n : ℕ) → ∀(α : ₂ℕ) → ∀(i : ℕ) → drop n α i ≡ α (i + n)
Lemma[cons-drop] 0        α i = refl
Lemma[cons-drop] (succ n) α i = Lemma[cons-drop] n (α ∘ succ) i


Lemma[cons-UC] : ∀{n : ℕ} → ∀(s : ₂Fin n) → uniformly-continuous-₂ℕ (cons s)
Lemma[cons-UC] ⟨⟩      m        = ∃-intro m (λ α β z → z)
Lemma[cons-UC] (b ∷ s) 0        = ∃-intro 0 (λ α β _ i → λ ())
Lemma[cons-UC] (b ∷ s) (succ m) = ∃-intro k prf
 where
  k : ℕ
  k = ∃-witness (Lemma[cons-UC] s m)
  prf : ∀(α β : ₂ℕ) → α ≣ k ≣ β →
         ∀(i : ℕ) → i < succ m → cons (b ∷ s) α i ≡ cons (b ∷ s) β i
  prf α β aw 0        r          = refl
  prf α β aw (succ i) (≤-succ r) = ∃-elim (Lemma[cons-UC] s m) α β aw i r

\end{code}