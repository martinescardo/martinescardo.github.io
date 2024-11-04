\begin{code}

module ConsHeadTail where

open import Mini-library
open [_]
open import Extensionality



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

Lemma[cons-take-drop]' : ∀(n : ℕ) → ∀(α : ₂ℕ) → [ cons (take n α) (drop n α) ≡ α ]
Lemma[cons-take-drop]' n α = hide (reveal extensionality (Lemma[cons-take-drop] n α))


Lemma[cons-drop] : ∀(n : ℕ) → ∀(α : ₂ℕ) → ∀(i : ℕ) → drop n α i ≡ α (i + n)
Lemma[cons-drop] 0        α i = refl
Lemma[cons-drop] (succ n) α i = Lemma[cons-drop] n (α ∘ succ) i


Lemma[cons-UC] : ∀{n : ℕ} → ∀(s : ₂Fin n) → uniformly-continuous-₂ℕ (cons s)
Lemma[cons-UC] ⟨⟩      m        = ∃-intro m (hide (λ α β z → z))
Lemma[cons-UC] (b ∷ s) 0        = ∃-intro 0 (hide (λ α β _ i → λ ()))
Lemma[cons-UC] (b ∷ s) (succ m) = ∃-intro k prf
 where
  k : ℕ
  k = ∃-witness (Lemma[cons-UC] s m)
  pr : ∀(α β : ₂ℕ) → α ≣ k ≣ β →
         ∀(i : ℕ) → i < succ m → [ cons (b ∷ s) α i ≡ cons (b ∷ s) β i ]
  pr α β aw 0        r          = hide refl
  pr α β aw (succ i) (≤-succ r) = 
           hide (reveal (∃-elim (Lemma[cons-UC] s m)) α β aw i r)
  prf : [ (∀(α β : ₂ℕ) → α ≣ k ≣ β →
            (cons (b ∷ s) α) ≣ succ m ≣ (cons (b ∷ s) β)) ]
  prf = hide (λ α β aw i r → reveal (pr α β aw i r))


Ftake : {X : Set} → (n k : ℕ) → Vec X (n + k) → Vec X k
Ftake n 0        v       = ⟨⟩
Ftake n (succ k) (h ∷ t) = h ∷ Ftake n k t

Fdrop : {X : Set} → (n k : ℕ) → Vec X (n + k) → Vec X n
Fdrop n 0        v       = v
Fdrop n (succ k) (h ∷ t) = Fdrop n k t


Lemma[cons-Ftake-Fdrop] : ∀(n k : ℕ) → ∀(s : ₂Fin (n + k)) → ∀(α : ₂ℕ) → ∀(i : ℕ) →
                          cons (Ftake n k s) (cons (Fdrop n k s) α) i ≡ cons s α i
Lemma[cons-Ftake-Fdrop] n 0        s       α i        = refl
Lemma[cons-Ftake-Fdrop] n (succ k) (b ∷ _) α 0        = refl
Lemma[cons-Ftake-Fdrop] n (succ k) (_ ∷ s) α (succ i) = Lemma[cons-Ftake-Fdrop] n k s α i


Lemma[cons-Ftake-Fdrop]² :
  ∀(n m l k : ℕ) → (eq : k ≡ m + l) → ∀(s : ₂Fin (k + n)) → ∀(α : ₂ℕ) →
   [  cons (Ftake k n s) 
          (cons (Ftake m l (subst {ℕ} {λ x → ₂Fin x} eq (Fdrop k n s)))
                (cons (Fdrop m l ((subst {ℕ} {λ x → ₂Fin x} eq (Fdrop k n s)))) α))
    ≡ cons s α ]
Lemma[cons-Ftake-Fdrop]² n m l k eq s α = goal
 where
  ss : ₂Fin k
  ss = Fdrop k n s
  ss' : ₂Fin (m + l)
  ss' = subst {ℕ} {λ x → ₂Fin x} eq ss
  Q : (j : ℕ) → ₂Fin j  → Set
  Q j t = [ cons (Ftake k n s) (cons t α) ≡ cons s α ]
  claim₀ : [ cons (Ftake k n s) (cons ss α) ≡ cons s α ]
  claim₀ = hide (reveal extensionality (Lemma[cons-Ftake-Fdrop] k n s α))
  claim₁ : [ cons (Ftake k n s) (cons ss' α) ≡ cons s α ]
  claim₁ = Lemma[subst] ℕ ₂Fin Q k (m + l) eq ss claim₀
  claim₂ : [ cons (Ftake m l ss') (cons (Fdrop m l ss') α) ≡ cons ss' α ]
  claim₂ = hide (reveal extensionality (Lemma[cons-Ftake-Fdrop] m l ss' α))
  goal : [ cons (Ftake k n s) (cons (Ftake m l ss') (cons (Fdrop m l ss') α))
         ≡ cons s α ]
  goal = hide (subst {₂ℕ} {λ x → cons (Ftake k n s) x ≡ cons s α}
                     (sym (reveal claim₂)) (reveal claim₁))


\end{code}