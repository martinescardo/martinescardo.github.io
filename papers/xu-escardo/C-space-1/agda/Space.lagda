Martin Escardo, Chuangjie Xu 2012

\begin{code}

module Space where

open import Mini-library
open import Cons
open import Extensionality

\end{code}

The site we are working with is the monoid of uniformly continuous
endo-functions of the Cantor space with a coverage in which, for each
natural number n, there is a family of concatenation maps "cons s"
indexed by finite binary sequence s of length n.

\begin{code}

-- The monoid of uniformly continuous ₂ℕ → ₂ℕ

C : Subset(₂ℕ → ₂ℕ)
C = uniformly-continuous-₂ℕ

\end{code}

The coverage axiom amounts to uniform continuity of endo-functions of
the Cantor space in the following sense.

\begin{code}

coverage-axiom : ∀(m : ℕ) → ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
                  ∃ \(n : ℕ) → ∀(s : ₂Fin n) →
                   ∃ \(s' : ₂Fin m) → ∃ \(t' : ₂ℕ → ₂ℕ) →
                    (t' ∈ C) ∧ (t ∘ (cons s) ≡ (cons s') ∘ t')
coverage-axiom m t uct = ∃-intro n prf
 where
  n : ℕ
  n = ∃-witness (uct m)
  prf : ∀(s : ₂Fin n) → ∃ \(s' : ₂Fin m) → ∃ \(t' : ₂ℕ → ₂ℕ) →
         (t' ∈ C) ∧ (t ∘ (cons s) ≡ (cons s') ∘ t')
  prf s = ∃-intro s' (∃-intro t' (∧-intro c₀ c₁))
   where
    s' : ₂Fin m
    s' = take m (t (cons s (λ i → ₀)))
    t' : ₂ℕ → ₂ℕ
    t' α = drop m (t (cons s α))
    c₀ : t' ∈ C
    c₀ k = ∃-intro l prf₀
     where
      ucts : uniformly-continuous-₂ℕ (t ∘ (cons s))
      ucts = Lemma[∘-UC] t uct (cons s) (Lemma[cons-UC] s)
      l : ℕ
      l = ∃-witness (ucts (k + m))
      eq : ∀(α : ₂ℕ) → ∀(i : ℕ) → t' α i ≡ t (cons s α) (i + m)
      eq α i = Lemma[cons-drop] m (t (cons s α)) i
      prf₀ : ∀(α β : ₂ℕ) → α ≣ l ≣ β → ∀(i : ℕ) → i < k → t' α i ≡ t' β i
      prf₀ α β awl i i<k = subst {₂} {λ b → t' α i ≡ b}
                                 (sym(eq β i)) claim₂
       where
        claim₀ : t (cons s α) ≣ k + m ≣ t (cons s β)
        claim₀ = ∃-elim (ucts (k + m)) α β awl
        claim₁ : t (cons s α) (i + m) ≡ t (cons s β) (i + m)
        claim₁ = claim₀ (i + m) (Lemma[a<b→a+c<b+c] {i} {k} {m} i<k)
        claim₂ : t' α i ≡ t (cons s β) (i + m)
        claim₂ = subst {₂} {λ b → b ≡ t (cons s β) (i + m)}
                           (sym(eq α i)) claim₁
    c₁ : t ∘ (cons s) ≡ (cons s') ∘ t'
    c₁ = extensionality (λ α → (extensionality (λ i → (prf₁ α i))))
         --------------         --------------
     where
      prf₁ : ∀(α : ₂ℕ) → ∀(i : ℕ) → t (cons s α) i ≡ cons s' (t' α) i
      prf₁ α i = subst {₂Fin m} {λ x → t (cons s α) i ≡ cons x (t' α) i} claim₂ claim₀
       where
        claim₀ : t (cons s α) i ≡ cons (take m (t (cons s α))) (t' α) i
        claim₀ = sym (Lemma[cons-take-drop] m (t (cons s α)) i)
        claim₁ : t (cons s α) ≣ m ≣ t (cons s 0̄)
        claim₁ = ∃-elim (uct m) (cons s α) (cons s 0̄) (Lemma[cons-≣_≣] s α 0̄)
        claim₂ : take m (t (cons s α)) ≡ s'
        claim₂ = Lemma[≣_≣-take] m (t (cons s α)) (t (cons s 0̄)) claim₁

\end{code}

Instead of working with whole category of sheaves over the above site,
we consider only those concrete sheaves which amount to the following
C-spaces. To topologize a set X, we use functions ₂ℕ → X, called
probes, rather than subsets of X, called open. Thus a topology on a
set X, in our sense, is a set of maps ₂ℕ → X, called the probes,
satisfying some conditions. We call it the C-topology.

\begin{code}

probe-axioms : (X : Set) → Subset(₂ℕ → X) → Set
probe-axioms X P =
    (∀(p : ₂ℕ → X) → constant p → p ∈ P)
  ∧ (∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → X) → p ∈ P → p ∘ t ∈ P)
  ∧ (∀(p : ₂ℕ → X) → (∃ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P)

TopologyOn : Set → Set₁
TopologyOn X = Σ \(P : Subset(₂ℕ → X)) → probe-axioms X P

Space : Set₁
Space = Σ \(X : Set) → TopologyOn X

U : Space → Set
U = π₀

Probe : (X : Space) → Subset(₂ℕ → U X) 
Probe X = π₀ (π₁ X)

cond₀ : (X : Space) →
        ∀(p : ₂ℕ → U X) → constant p → p ∈ Probe X
cond₀ X = π₀ (π₁ (π₁ X))

cond₁ : (X : Space) →
        ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
        p ∘ t ∈ Probe X
cond₁ X = π₀ (π₁ (π₁ (π₁ X)))

cond₂ : (X : Space) →
        ∀(p : ₂ℕ → U X) → (∃ \(n : ℕ) → ∀(s : ₂Fin n) → p ∘ (cons s) ∈ Probe X) →
        p ∈ Probe X
cond₂ X = π₁ (π₁ (π₁ (π₁ X)))


\end{code}

Then we define continuous functions between spaces and show that they
do form a category.

\begin{code}

continuous : {X Y : Space} → (U X → U Y) → Set
continuous {X} {Y} f = ∀ p → p ∈ Probe X → f ∘ p ∈ Probe Y

Map : Space → Space → Set
Map X Y = Σ \(f : U X → U Y) → continuous {X} {Y} f

id-is-continuous : ∀{X : Space} → continuous {X} {X} id
id-is-continuous p pinP = pinP

∘-preserves-continuity : {X Y Z : Space} →
    ∀(f : U X → U Y) → continuous {X} {Y} f →
    ∀(g : U Y → U Z) → continuous {Y} {Z} g →
    continuous {X} {Z} (g ∘ f)
∘-preserves-continuity f fcts g gcts p pinP = gcts(f ∘ p)(fcts p pinP)


-- Initial C-space
-- The C-topology is empty

∅Space : Space
∅Space = ∅ , P , c₀ , c₁ , c₂
 where
  P : Subset (₂ℕ → ∅)
  P p = ∅
  c₀ : ∀(p : ₂ℕ → ∅) → constant p → p ∈ P
  c₀ p _ = p 0̄
  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → ∅) → p ∈ P → p ∘ t ∈ P
  c₁ _ _ p _ = p 0̄
  c₂ : ∀(p : ₂ℕ → ∅) → (∃ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P
  c₂ p _ = p 0̄


-- Terminal C-space
-- The unit map to ⒈ is the only probe

⒈Space : Space
⒈Space = ⒈ , P , c₀ , c₁ , c₂
 where
  P : Subset (₂ℕ → ⒈)
  P p = ⒈
  c₀ : ∀(p : ₂ℕ → ⒈) → constant p → p ∈ P
  c₀ _ _ = ⋆
  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → ⒈) → p ∈ P → p ∘ t ∈ P
  c₁ _ _ _ _ = ⋆
  c₂ : ∀(p : ₂ℕ → ⒈) → (∃ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P
  c₂ _ _ = ⋆

\end{code}
