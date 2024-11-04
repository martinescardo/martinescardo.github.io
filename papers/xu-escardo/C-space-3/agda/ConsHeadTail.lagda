\begin{code}

module ConsHeadTail where

open import Mini-library
open import Setoid
open import Uniform-continuity


-- The concatenation maps and some of their properties

cons : {m : ℕ} → ₂Fin m → ₂ℕ → ₂ℕ
cons ⟨⟩      α i        = α i
cons (h ∷ _) α 0        = h
cons (_ ∷ t) α (succ i) = cons t α i

cons₀ : ₂ℕ → ₂ℕ
cons₀ α 0        = ₀
cons₀ α (succ i) = α i
cons₁ : ₂ℕ → ₂ℕ
cons₁ α 0        = ₁
cons₁ α (succ i) = α i

Lemma[cons-E-map] : ∀{m : ℕ} → ∀(s : ₂Fin m) → ∀(α β : ₂ℕ) → α ≣ β → cons s α ≣ cons s β
Lemma[cons-E-map] ⟨⟩      α β eq i        = eq i
Lemma[cons-E-map] (h ∷ _) α β eq 0        = refl
Lemma[cons-E-map] (_ ∷ t) α β eq (succ i) = Lemma[cons-E-map] t α β eq i

E-cons : {m : ℕ} → ₂Fin m → E-map E₂ℕ E₂ℕ
E-cons s = cons s , Lemma[cons-E-map] s

Lemma[E-cons-UC] : ∀{m : ℕ} → ∀(s : ₂Fin m) → uniformly-continuous-₂ℕ (E-cons s)
Lemma[E-cons-UC] ⟨⟩      m        = m , λ α β e → e
Lemma[E-cons-UC] (h ∷ _) 0        = 0 , λ α β e i → λ ()
Lemma[E-cons-UC] (h ∷ t) (succ m) = k , prf
 where
  k : ℕ
  k = ∃-witness (Lemma[E-cons-UC] t m)
  prf : ∀(α β : ₂ℕ) → α ≣ k ≣ β → cons (h ∷ t) α ≣ succ m ≣ cons (h ∷ t) β
  prf α β e 0        r          = refl
  prf α β e (succ i) (≤-succ r) = ∃-elim (Lemma[E-cons-UC] t m) α β e i r


Lemma[cons-drop] : ∀(n : ℕ) → ∀(α : ₂ℕ) → ∀(i : ℕ) → drop n α i ≡ α (i + n)
Lemma[cons-drop] 0        α i = refl
Lemma[cons-drop] (succ n) α i = Lemma[cons-drop] n (α ∘ succ) i


Lemma[cons-take-drop] : ∀(n : ℕ) → ∀(α : ₂ℕ) → cons (take n α) (drop n α) ≣ α
Lemma[cons-take-drop] 0        α i        = refl
Lemma[cons-take-drop] (succ n) α 0        = refl
Lemma[cons-take-drop] (succ n) α (succ i) = Lemma[cons-take-drop] n (α ∘ succ) i


Lemma[cons-≣_≣] : {n : ℕ} → ∀(s : ₂Fin n) → ∀(α β : ₂ℕ) → cons s α ≣ n ≣ cons s β
Lemma[cons-≣_≣] ⟨⟩      α β i        ()
Lemma[cons-≣_≣] (b ∷ s) α β 0        r          = refl
Lemma[cons-≣_≣] (b ∷ s) α β (succ i) (≤-succ r) = Lemma[cons-≣_≣] s α β i r


Ftake : {X : Set} → (n k : ℕ) → Vec X (n + k) → Vec X k
Ftake n 0        v       = ⟨⟩
Ftake n (succ k) (h ∷ t) = h ∷ Ftake n k t

Fdrop : {X : Set} → (n k : ℕ) → Vec X (n + k) → Vec X n
Fdrop n 0        v       = v
Fdrop n (succ k) (h ∷ t) = Fdrop n k t

Lemma[cons-Ftake-Fdrop] : ∀(n k : ℕ) → ∀(s : ₂Fin (n + k)) → ∀(α : ₂ℕ) →
                          cons (Ftake n k s) (cons (Fdrop n k s) α) ≣ cons s α
Lemma[cons-Ftake-Fdrop] n 0        s       α i        = refl
Lemma[cons-Ftake-Fdrop] n (succ k) (b ∷ _) α 0        = refl
Lemma[cons-Ftake-Fdrop] n (succ k) (_ ∷ s) α (succ i) = Lemma[cons-Ftake-Fdrop] n k s α i

Lemma[cons-Ftake-Fdrop]² : ∀(n m l k : ℕ) → (eq : k ≡ m + l) →
                            ∀(s : ₂Fin (k + n)) → ∀(α : ₂ℕ) →
    cons (Ftake k n s) 
         (cons (Ftake m l (subst {ℕ} {λ x → ₂Fin x} eq (Fdrop k n s)))
               (cons (Fdrop m l ((subst {ℕ} {λ x → ₂Fin x} eq (Fdrop k n s)))) α))
  ≣ cons s α
Lemma[cons-Ftake-Fdrop]² n m l k eq s α = goal
 where
  ss : ₂Fin k
  ss = Fdrop k n s
  ss' : ₂Fin (m + l)
  ss' = subst {ℕ} {λ x → ₂Fin x} eq ss
  Q : (i : ℕ) → ₂Fin i  → Set
  Q i t = cons (Ftake k n s) (cons t α) ≣ cons s α
  claim₀ : cons (Ftake k n s) (cons ss α) ≣ cons s α
  claim₀ = Lemma[cons-Ftake-Fdrop] k n s α
  claim₁ : cons (Ftake k n s) (cons ss' α) ≣ cons s α
  claim₁ = Lemma[subst] ℕ ₂Fin Q k (m + l) eq ss claim₀
  claim₂ : cons (Ftake m l ss') (cons (Fdrop m l ss') α) ≣ cons ss' α
  claim₂ = Lemma[cons-Ftake-Fdrop] m l ss' α
  claim₃ :  cons (Ftake k n s) (cons (Ftake m l ss') (cons (Fdrop m l ss') α))
          ≣ cons (Ftake k n s) (cons ss' α)
  claim₃ = Lemma[cons-E-map] (Ftake k n s)
                             (cons (Ftake m l ss') (cons (Fdrop m l ss') α))
                             (cons ss' α) claim₂
  goal : cons (Ftake k n s) (cons (Ftake m l ss') (cons (Fdrop m l ss') α)) ≣ cons s α
  goal i = trans (claim₃ i) (claim₁ i)


Lemma[cons-take-≣_≣] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ cons (take n α) β
Lemma[cons-take-≣_≣] 0        α β i        ()
Lemma[cons-take-≣_≣] (succ n) α β 0        r          = refl
Lemma[cons-take-≣_≣] (succ n) α β (succ i) (≤-succ r) = Lemma[cons-take-≣_≣] n (α ∘ succ) β i r

\end{code}