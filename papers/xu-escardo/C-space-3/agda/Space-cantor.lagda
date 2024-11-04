Chuangjie Xu 2012

\begin{code}

module Space-cantor where

open import Mini-library
open import Setoid
open import ConsHeadTail
open import Uniform-continuity
open import Space
open import Space-exponential
open import Space-discrete

\end{code}

The Cantor space ₂ℕ with the monoid C form a C-space, which
is isomorphic to the exponential ℕSpace ⇒ ₂Space.

\begin{code}

Lemma[₂ℕ-to-Map-ℕ-₂] : ₂ℕ → Map ℕSpace ₂Space
Lemma[₂ℕ-to-Map-ℕ-₂] α = ᾱ , cts
 where
  ᾱ : E-map Eℕ E₂
  ᾱ = α , Lemma[₂ℕ-E-map] α
  cts : continuous {ℕSpace} {₂Space} ᾱ
  cts = Lemma[discreteness] {Eℕ} {₂Space} ᾱ


Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] : (r : E-map-₂ℕ-₂ℕ) → r ∈ C →
     ∃ \(φ : E-map-₂ℕ (U (ℕSpace ⇒ ₂Space))) → φ ∈ Probe (ℕSpace ⇒ ₂Space)
Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] (r , er) ucr = φ , prf
 where
  φ : E-map-₂ℕ (U (ℕSpace ⇒ ₂Space))
  φ = ϕ , er
   where
    ϕ : ₂ℕ → Map ℕSpace ₂Space
    ϕ α = ψ , Lemma[discreteness] {Eℕ} {₂Space} ψ
     where
      ψ : E-map Eℕ E₂
      ψ = r α , Lemma[₂ℕ-E-map] (r α)

  prf : φ ∈ Probe (ℕSpace ⇒ ₂Space)
  prf (p , ep) (n , pr) (t , et) uct = m , goal
   where
    f : ₂Fin n → ℕ
    f s = p (cons s 0̄)
    k : ℕ
    k = succ (∃-witness (max-fin f))
    claim₀ : ∀(α : ₂ℕ) → p α ≡ f (take n α)
    claim₀ α = pr α (cons (take n α) 0̄) (Lemma[cons-take-≣_≣] n α 0̄)
    claim₁ : ∀(α : ₂ℕ) → f (take n α) < k
    claim₁ α = ≤-succ (∃-elim (max-fin f) (take n α))
    claim₂ : ∀(α : ₂ℕ) → p α < k
    claim₂ α = subst {ℕ} {λ x → x < k} (sym (claim₀ α)) (claim₁ α)
    ucrt : uniformly-continuous-₂ℕ ((r , er) ◎ (t , et))
    ucrt = Lemma[◎-UC] (r , er) ucr (t , et) uct
    l : ℕ
    l = ∃-witness (ucrt k)
    m : ℕ
    m = maximum n l
    n≤m : n ≤ m
    n≤m = ∧-elim₀ (Lemma[≤-max] n l)
    l≤m : l ≤ m
    l≤m = ∧-elim₁ (Lemma[≤-max] n l)
    goal : ∀(α β : ₂ℕ) → α ≣ m ≣ β → r (t α) (p α) ≡ r (t β) (p β)
    goal α β awm = subst {ℕ} {λ x → r(t α)(p α) ≡ r(t β)x} eqp subgoal
     where
      awn : α ≣ n ≣ β
      awn i i<n = awm i (Lemma[a<b≤c→a<c] i<n n≤m)
      eqp : p α ≡ p β
      eqp = pr α β awn
      awl : α ≣ l ≣ β
      awl i i<l = awm i (Lemma[a<b≤c→a<c] i<l l≤m)
      awk : r(t α) ≣ k ≣ r(t β)
      awk = ∃-elim (ucrt k) α β awl
      subgoal : r(t α)(p α) ≡ r(t β)(p α)
      subgoal = awk (p α) (claim₂ α)

\end{code}

As the underlining category C contains only one object, the
Yoneda lemma equivalently says that the set of continuous maps
from the Yoneda embedding to any QC-space is isomorphic to the
QC-topology of that space.

\begin{code}

ID : E-map-₂ℕ (U (ℕSpace ⇒ ₂Space))
ID = ∃-witness (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] (E-id {E₂ℕ}) Lemma[id-UC])
ID-is-a-probe : ID ∈ Probe (ℕSpace ⇒ ₂Space)
ID-is-a-probe = ∃-elim (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] (E-id {E₂ℕ}) Lemma[id-UC])

Lemma[Yoneda] : ∀{X : Space} → Map (ℕSpace ⇒ ₂Space) X → ∃ \(p : E-map-₂ℕ (U X)) → p ∈ Probe X
Lemma[Yoneda] {X} (f , cts) = ⟨ U (ℕSpace ⇒ ₂Space) ∣ U X ⟩ f ◎ ID , cts ID ID-is-a-probe

\end{code}