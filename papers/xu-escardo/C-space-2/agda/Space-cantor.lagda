Chuangjie Xu 2012

\begin{code}

module Space-cantor where

open import Mini-library
open [_]
open import ConsHeadTail
open import Space
open import Space-discrete
open import Space-exponential

\end{code}

The Cantor space ₂ℕ with the monoid C form a C-space, which
is isomorphic to the exponential ℕSpace ⇒ ₂Space.

\begin{code}

Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] : (r : ₂ℕ → ₂ℕ) → r ∈ C →
     ∃ \(φ : ₂ℕ → U (ℕSpace ⇒ ₂Space)) → φ ∈ Probe (ℕSpace ⇒ ₂Space)
Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] r ucr = ∃-intro φ prf
 where
  φ : ₂ℕ → U (ℕSpace ⇒ ₂Space)
  φ α = r α , Lemma[discreteness] {ℕ} {₂Space} (r α)
  prf : ∀(p : ₂ℕ → ℕ) → uniformly-continuous-ℕ p →
        ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
        uniformly-continuous-₂ (λ α → (π₀ ∘ φ)(t α)(p α))
  prf p ucp t uct = ∃-intro l (hide (λ α β awl → reveal (prf' α β awl)))
   where
    m : ℕ
    m = ∃-witness ucp
    f : ₂Fin m → ℕ
    f s = p (cons s 0̄)
    eq : ∀(α : ₂ℕ) → [ p α ≡ f (take m α) ]
    eq α = hide (reveal (∃-elim ucp) α (cons (take m α) 0̄) (Lemma[cons-take-≣_≣] m α 0̄))
    k' : ℕ
    k' = ∃-witness (max-fin f)
    k'-max : ∀(α : ₂ℕ) → [ p α ≤ k' ]
    k'-max α = hide (subst {ℕ} {λ i → i ≤ k'} (sym (reveal (eq α))) (∃-elim (max-fin f) (take m α)))
    k : ℕ
    k = succ k'
    k-max : ∀(α : ₂ℕ) → [ p α < k ]
    k-max α = hide (≤-succ (reveal (k'-max α)))
    ucrt : uniformly-continuous-₂ℕ (r ∘ t)
    ucrt = Lemma[∘-UC] r ucr t uct
    n : ℕ
    n = ∃-witness (ucrt k)
    l : ℕ
    l = maximum m n
    m≤l : m ≤ l
    m≤l = ∧-elim₀ (Lemma[≤-max] m n)
    n≤l : n ≤ l
    n≤l = ∧-elim₁ (Lemma[≤-max] m n)
    prf' : ∀(α β : ₂ℕ) → α ≣ l ≣ β → [ r(t α)(p α) ≡ r(t β)(p β) ]
    prf' α β awl = hide (subst {ℕ} {λ i → r(t α)(p α) ≡ r(t β) i} (reveal eqp) (reveal subgoal))
     where
      awm : α ≣ m ≣ β
      awm i i<m = awl i (Lemma[a<b≤c→a<c] i<m m≤l)
      eqp : [ p α ≡ p β ]
      eqp = hide (reveal (∃-elim ucp) α β awm)
      awn : α ≣ n ≣ β
      awn i i<n = awl i (Lemma[a<b≤c→a<c] i<n n≤l)
      awk : [ r (t α) ≣ k ≣ r (t β) ]
      awk = hide (reveal (∃-elim (ucrt k)) α β awn)
      subgoal : [ r(t α)(p α) ≡ r(t β)(p α) ]
      subgoal = hide (reveal awk (p α) (reveal (k-max α)))

\end{code}

As the underlining category C contains only one object, the
Yoneda lemma equivalently says that the set of continuous maps
from the Yoneda embedding to any C-space is isomorphic to the
C-topology of that space.

\begin{code}

Lemma[Yoneda] : ∀{X : Space} → Map (ℕSpace ⇒ ₂Space) X →
                 ∃ \(p : ₂ℕ → U X) → p ∈ Probe X
Lemma[Yoneda] {X} (f , cts) = (f ∘ ID) , (cts ID ID-is-a-probe)
 where
  ID : ₂ℕ → U(ℕSpace ⇒ ₂Space)
  ID = ∃-witness (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] id Lemma[id-UC])
  ID-is-a-probe : ID ∈ Probe(ℕSpace ⇒ ₂Space)
  ID-is-a-probe = ∃-elim (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] id Lemma[id-UC])

\end{code}