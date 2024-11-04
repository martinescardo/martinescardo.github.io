Chuangjie Xu, 2012

The axiom of uniform continuity is not provable in system T or
HAω. But it can be realized in our model by the following Fan
functional:

       fan : Map ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace) ℕSpace

which continuously computes the moduli of uniform continuity.

\begin{code}


module Fan where

open import Mini-library
open import ConsHeadTail
open import Uniform-continuity
open import Setoid
open import Space
open import Space-exponential
open import Space-discrete
open import Space-cantor
open import Least-moduli-of-uniform-continuity


\end{code}

To show the continuity of the fan functional, we need the
following auxiliaries.

\begin{code}


_×2 : ℕ → ℕ
_×2 0        = 0
_×2 (succ n) = succ (succ (n ×2))

Lemma[n≤2n] : ∀(n : ℕ) → n ≤ (n ×2)
Lemma[n≤2n] 0        = ≤-zero
Lemma[n≤2n] (succ n) = Lemma[a≤b≤c→a≤c] (≤-succ (Lemma[n≤2n] n))
                                        (Lemma[n≤n+1] (succ (n ×2)))

Lemma[n<m→2n<2m] : ∀(n m : ℕ) → n < m → (n ×2) < (m ×2)
Lemma[n<m→2n<2m] 0        0        ()
Lemma[n<m→2n<2m] 0        (succ m) _          = ≤-succ ≤-zero
Lemma[n<m→2n<2m] (succ n) 0        ()
Lemma[n<m→2n<2m] (succ n) (succ m) (≤-succ r) = ≤-succ (≤-succ (Lemma[n<m→2n<2m] n m r))


_×2+1 : ℕ → ℕ
_×2+1 = succ ∘ _×2

Lemma[n≤2n+1] : ∀(n : ℕ) → n ≤ (n ×2+1)
Lemma[n≤2n+1] n = Lemma[a≤b≤c→a≤c] (Lemma[n≤2n] n) (Lemma[n≤n+1] (n ×2))

Lemma[n<m→2n+1<2m+1] : ∀(n m : ℕ) → n < m → (n ×2+1) < (m ×2+1)
Lemma[n<m→2n+1<2m+1] n m r = ≤-succ (Lemma[n<m→2n<2m] n m r)


\end{code}

Here is the fan functional, which calculates smallest moduli, using
the moduli obtained by Yoneda Lemma.

\begin{code}


fan : Map ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace) ℕSpace
fan = (f , ef) , cts
 where
  f : Ũ (U ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace)) → ℕ
  f φ = LM p n
   where
    p : ₂ℕ → ℕ
    p = π₀ (∃-witness (Lemma[Yoneda] {ℕSpace} φ))
    n : ℕ
    n = ∃-witness (∃-elim (Lemma[Yoneda] {ℕSpace} φ))

  ef : ∀(φ φ' : Ũ (U ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace))) →
        E (U ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace)) φ φ' → f φ ≡ f φ'
  ef φ φ' eφφ = trans claim₀ claim₁
   where
    q : ₂ℕ → ℕ
    q = π₀ (∃-witness (Lemma[Yoneda] {ℕSpace} φ))
    n : ℕ
    n = ∃-witness (∃-elim (Lemma[Yoneda] {ℕSpace} φ))
    prn : ∀(α β : ₂ℕ) → α ≣ n ≣ β → q α ≡ q β
    prn = ∃-elim (∃-elim (Lemma[Yoneda] {ℕSpace} φ))
    q' : ₂ℕ → ℕ
    q' = π₀ (∃-witness (Lemma[Yoneda] {ℕSpace} φ'))
    n' : ℕ
    n' = ∃-witness (∃-elim (Lemma[Yoneda] {ℕSpace} φ'))
    prn' : ∀(α β : ₂ℕ) → α ≣ n' ≣ β → q' α ≡ q' β
    prn' = ∃-elim (∃-elim (Lemma[Yoneda] {ℕSpace} φ'))
    eqq' : ∀(α : ₂ℕ) → q α ≡ q' α
    eqq' α = eφφ (Lemma[₂ℕ-to-Map-ℕ-₂] α)
    pr'n' : ∀(α β : ₂ℕ) → α ≣ n ≣ β → q' α ≡ q' β
    pr'n' α β awn = trans (sym (eqq' α)) (trans (prn α β awn) (eqq' β))
    claim₀ : LM q n ≡ LM q' n
    claim₀ = Lemma[LM-E-map] q q' eqq' n
    claim₁ : LM q' n ≡ LM q' n'
    claim₁ = Lemma[LM-least] q' n pr'n' n' prn'

  cts : continuous {(ℕSpace ⇒ ₂Space) ⇒ ℕSpace} {ℕSpace} (f , ef)
  cts (p , ep) pr = n , prf
   where
    t₀ : ₂ℕ → ₂ℕ
    t₀ α = α ∘ _×2
    et₀ : ∀(α β : ₂ℕ) → α ≣ β → t₀ α ≣ t₀ β
    et₀ α β e i = e (i ×2)
    uct₀ : (t₀ , et₀) ∈ C
    uct₀ m = (m ×2) , prf₀
     where
      prf₀ : ∀(α β : ₂ℕ) → α ≣ m ×2 ≣ β → t₀ α ≣ m ≣ t₀ β
      prf₀ α β aw i i<m = aw (i ×2) (Lemma[n<m→2n<2m] i m i<m)

    t₁ : ₂ℕ → ₂ℕ
    t₁ α = α ∘ _×2+1
    et₁ : ∀(α β : ₂ℕ) → α ≣ β → t₁ α ≣ t₁ β
    et₁ α β e i = e (i ×2+1)
    uct₁ : (t₁ , et₁) ∈ C
    uct₁ m = (m ×2+1) , prf₁
     where
      prf₁ : ∀(α β : ₂ℕ) → α ≣ m ×2+1 ≣ β → t₁ α ≣ m ≣ t₁ β
      prf₁ α β aw i i<m = aw (i ×2+1) (Lemma[n<m→2n+1<2m+1] i m i<m)


    t₁' : ₂ℕ → Ũ(U(ℕSpace ⇒ ₂Space))
    t₁' = π₀ (∃-witness (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] (t₁ , et₁) uct₁))
    et₁' : ∀(α β : ₂ℕ) → α ≣ β → π₀ (π₀ (t₁' α)) ≣  π₀ (π₀ (t₁' β))
    et₁' = π₁ (∃-witness (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] (t₁ , et₁) uct₁))
    pr₁ : (t₁' , et₁') ∈ Probe (ℕSpace ⇒ ₂Space)
    pr₁ = ∃-elim (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] (t₁ , et₁) uct₁)

    merge : ₂ℕ → ₂ℕ → ₂ℕ
    merge α β 0               = α 0
    merge α β 1               = β 0
    merge α β (succ (succ i)) = merge (α ∘ succ) (β ∘ succ) i

    lemma : ∀(α β γ : ₂ℕ) → ∀(k : ℕ) → α ≣ k ≣ β → merge α γ ≣ k ×2 ≣ merge β γ
    lemma α β γ 0        aw i ()
    lemma α β γ (succ k) aw 0 r = aw zero (≤-succ ≤-zero)
    lemma α β γ (succ k) aw 1 r = refl
    lemma α β γ (succ k) aw (succ (succ i)) (≤-succ (≤-succ r)) =
          lemma (α ∘ succ) (β ∘ succ) (γ ∘ succ) k aw' i r
     where
      aw' : α ∘ succ ≣ k ≣ β ∘ succ
      aw' j j<k = aw (succ j) (≤-succ j<k)

    lemma₀ : ∀(α β : ₂ℕ) → t₀ (merge α β) ≣ α
    lemma₀ α β 0        = refl
    lemma₀ α β (succ i) = lemma₀ (α ∘ succ) (β ∘ succ) i

    lemma₁ : ∀(α β : ₂ℕ) → t₁ (merge α β) ≣ β
    lemma₁ α β 0        = refl
    lemma₁ α β (succ i) = lemma₁ (α ∘ succ) (β ∘ succ) i

    lemma₁' : ∀(α : ₂ℕ) → ∀(φ : Map ℕSpace ₂Space) →
               π₀ (π₀ (t₁' (merge α (π₀ (π₀ φ))))) ≣ π₀ (π₀ φ)
    lemma₁' α φ = lemma₁ α (π₀ (π₀ φ))

    q : ₂ℕ → ℕ
    q = π₀ (exp (ℕSpace ⇒ ₂Space) ℕSpace (p , ep) (t₀ , et₀) (t₁' , et₁'))
    eq : ∀(α β : ₂ℕ) → α ≣ β → q α ≡ q β
    eq = π₁ (exp (ℕSpace ⇒ ₂Space) ℕSpace (p , ep) (t₀ , et₀) (t₁' , et₁'))
    ucq : uniformly-continuous-ℕ (q , eq)
    ucq = pr (t₁' , et₁') pr₁ (t₀ , et₀) uct₀

    n : ℕ
    n = ∃-witness ucq

    claim : ∀(α β : ₂ℕ) → α ≣ n ≣ β →
             ∀(φ : Map ℕSpace ₂Space) → π₀ (π₀ (p α)) φ ≡ π₀ (π₀ (p β)) φ
    claim α β aw φ = trans (sym claim₅) (trans claim₄ claim₆)
     where
      γ : ₂ℕ
      γ = π₀ (π₀ φ)
      aw' : merge α γ ≣ n ≣ merge β γ
      aw' = Lemma[≣_≣-≤] (n ×2) (merge α γ) (merge β γ) (lemma α β γ n aw) n (Lemma[n≤2n] n)
      claim₀ : π₀ (π₀ (p (t₀ (merge α γ)))) (t₁' (merge α γ))
             ≡ π₀ (π₀ (p (t₀ (merge β γ)))) (t₁' (merge β γ))
      claim₀ = ∃-elim ucq (merge α γ) (merge β γ) aw'
      claim₁ : π₀ (π₀ (p (t₀ (merge α γ)))) (t₁' (merge α γ))
             ≡ π₀ (π₀ (p α)) (t₁' (merge α γ))
      claim₁ = ep (t₀ (merge α γ)) α (lemma₀ α γ) (t₁' (merge α γ))
      claim₂ : π₀ (π₀ (p α)) (t₁' (merge α γ))
             ≡ π₀ (π₀ (p (t₀ (merge β γ)))) (t₁' (merge β γ))
      claim₂ = trans (sym claim₁) claim₀
      claim₃ : π₀ (π₀ (p (t₀ (merge β γ)))) (t₁' (merge β γ))
             ≡ π₀ (π₀ (p β)) (t₁' (merge β γ))
      claim₃ = ep (t₀ (merge β γ)) β (lemma₀ β γ) (t₁' (merge β γ))
      claim₄ : π₀ (π₀ (p α)) (t₁' (merge α γ))
             ≡ π₀ (π₀ (p β)) (t₁' (merge β γ))
      claim₄ = trans claim₂ claim₃
      claim₅ : π₀ (π₀ (p α)) (t₁' (merge α γ))
             ≡ π₀ (π₀ (p α)) φ
      claim₅ = π₁ (π₀ (p α)) (t₁' (merge α γ)) φ (lemma₁' α φ)
      claim₆ : π₀ (π₀ (p β)) (t₁' (merge β γ))
             ≡ π₀ (π₀ (p β)) φ
      claim₆ = π₁ (π₀ (p β)) (t₁' (merge β γ)) φ (lemma₁' β φ)

    prf : ∀(α β : ₂ℕ) → α ≣ n ≣ β → (f ∘ p) α ≡ (f ∘ p) β  
    prf α β aw = ef (p α) (p β) (claim α β aw)


\end{code}
