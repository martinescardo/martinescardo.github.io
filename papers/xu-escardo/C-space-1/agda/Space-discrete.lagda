Chuangjie Xu, 2012

\begin{code}

module Space-discrete where

open import Mini-library
open import Cons
open import Space
open import Extensionality

\end{code}

The locally constant functions ₂ℕ → X on any set X form a
C-topology on X. Any space with such a C-topology is
discrete, i.e. all maps from it to any other space is continuous.

\begin{code}

locally-constant-topology : ∀{X : Set} → probe-axioms X locally-constant
locally-constant-topology {X} = c₀ , c₁ , c₂
 where
  c₀ : ∀(p : ₂ℕ → X) → constant p → locally-constant p
  c₀ p cp = ∃-intro 0 (λ α β _ → cp α β)

  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → X) → locally-constant p →
           locally-constant (p ∘ t)
  c₁ t uct p ucp = ∃-intro n prf
   where
    m : ℕ
    m = ∃-witness ucp
    n : ℕ
    n = ∃-witness(uct m)
    prf : ∀(α β : ₂ℕ) → α ≣ n ≣ β → p(t α) ≡ p(t β)
    prf α β awn = ∃-elim ucp (t α) (t β) (∃-elim (uct m) α β awn)

  c₂ : ∀(p : ₂ℕ → X) →
           (∃ \(n : ℕ) → ∀(s : ₂Fin n) → locally-constant (p ∘ (cons s))) →
           locally-constant p
  c₂ p ex = ∃-intro (n + k) prf
   where
    n : ℕ
    n = ∃-witness ex
    f : ₂Fin n → ℕ
    f s = ∃-witness (∃-elim ex s)
    k : ℕ
    k = ∃-witness (max-fin f)
    k-max : ∀(s : ₂Fin n) → f s ≤ k
    k-max = ∃-elim (max-fin f)
    fact : ∀(s : ₂Fin n) → ∀(α β : ₂ℕ) → α ≣ k ≣ β → p(cons s α) ≡ p(cons s β)
    fact s α β awk = ∃-elim (∃-elim ex s) α β 
                           (Lemma[≣_≣-≤] k α β awk (f s) (k-max s))
    prf : ∀(α β : ₂ℕ) → α ≣ n + k ≣ β → p α ≡ p β
    prf α β awnk = subst {₂ℕ} {λ x → p α ≡ p x}
                         pβ (subst {₂ℕ} {λ x → p x ≡ p(cons s β')}
                                   pα (fact s α' β' awk))
     where
      s : ₂Fin n
      s = take n α
      lemma : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ≣ n ≣ β → take n α ≡ take n β
      lemma 0 α β aw = refl
      lemma (succ n) α β aw = subst {₂Fin n} {λ t → α 0 ∷ take n (α ∘ succ) ≡ β 0 ∷ t} eqt claim
       where
        eqh : α 0 ≡ β 0
        eqh = aw 0 (≤-succ ≤-zero)
        aw' : α ∘ succ ≣ n ≣ β ∘ succ
        aw' i r = aw (succ i) (≤-succ r) 
        eqt : take n (α ∘ succ) ≡ take n (β ∘ succ)
        eqt = lemma n (α ∘ succ) (β ∘ succ) aw'
        claim : α 0 ∷ take n (α ∘ succ) ≡ β 0 ∷ take n (α ∘ succ)
        claim = cong (λ h → h ∷ take n (α ∘ succ)) eqh
      lemma' : ∀(a b : ℕ) → a ≤ a + b
      lemma' a 0        = Lemma[n≤n] a
      lemma' a (succ b) = Lemma[a≤b≤c→a≤c] (lemma' a b) (le (a + b))
       where
        le : ∀(c : ℕ) → c ≤ succ c
        le 0        = ≤-zero
        le (succ c) = ≤-succ (le c)
      awn : α ≣ n ≣ β
      awn i i<n = awnk i (Lemma[a≤b≤c→a≤c] i<n (lemma' n k))
      eqs : take n α ≡ take n β
      eqs = lemma n α β awn
      α' : ₂ℕ
      α' = drop n α
      pα : cons s α' ≡ α
      pα = extensionality (Lemma[cons-take-drop] n α)
           --------------
      β' : ₂ℕ
      β' = drop n β
      pβ : cons s β' ≡ β
      pβ = subst {₂Fin n} {λ x → cons x β' ≡ β}
                 (sym eqs) (extensionality (Lemma[cons-take-drop] n β))
      awk : α' ≣ k ≣ β'
      awk i i<k = trans (trans eqα subgoal) (sym eqβ)
       where
        i+n<k+n : i + n < k + n
        i+n<k+n = Lemma[a<b→a+c<b+c] {i} {k} {n} i<k
        i+n<n+k : i + n < n + k
        i+n<n+k = subst {ℕ} {λ m → (i + n) < m} (Lemma[n+m=m+n] k n) i+n<k+n
        subgoal : α (i + n) ≡ β (i + n)
        subgoal = awnk (i + n) i+n<n+k
        le : (n i : ℕ) → (α : ₂ℕ) → drop n α i ≡ α (i + n)
        le 0 i α = refl
        le (succ n) i α = le n i (α ∘ succ)
        eqα : α' i ≡ α (i + n)
        eqα = le n i α
        eqβ : β' i ≡ β (i + n)
        eqβ = le n i β


Discrete-Space : Set → Space
Discrete-Space X = X , locally-constant , locally-constant-topology

\end{code}

All the uniformly continuous maps ₂ℕ → ₂ (and ₂ℕ → ℕ) are
locally constant. And hence they form a C-topology for ₂ (and ℕ).

\begin{code}

-- The coproduct 1 + 1

₂Space : Space
₂Space = Discrete-Space ₂


-- The natural numbers object

ℕSpace : Space
ℕSpace = Discrete-Space ℕ


Lemma[discreteness] : {X : Set} → ∀{Y : Space} → ∀(f : X → U Y) →
  continuous {Discrete-Space X} {Y} f
Lemma[discreteness] {X} {Y , Q , qc₀ , _ , qc₂} f p plc = qc₂ (f ∘ p) (∃-intro m claim)
 where
  m : ℕ
  m = ∃-witness plc
  claim : ∀(s : ₂Fin m) → (f ∘ p ∘ (cons s)) ∈ Q
  claim s = qc₀ (f ∘ p ∘ (cons s)) claim₁
   where
    claim₀ : constant (p ∘ (cons s))
    claim₀ α β = ∃-elim plc (cons s α) (cons s β) (Lemma[cons-≣_≣] s α β)
    claim₁ : constant (f ∘ p ∘ (cons s))
    claim₁ = Lemma[∘-constant] (p ∘ (cons s)) f claim₀

\end{code}