Martin Escardo, Chuangjie Xu 2012

\begin{code}

module Space where

open import Mini-library
open import Setoid
open import Uniform-continuity
open import ConsHeadTail

\end{code}

The site we are working with is the monoid of uniformly continuous
endo-functions of the Cantor space with a coverage in which, for each
natural number n, there is a family of concatenation maps "cons s"
indexed by finite binary sequence s of length n.

\begin{code}

-- The monoid of uniformly continuous ₂ℕ → ₂ℕ

C : Subset E-map-₂ℕ-₂ℕ
C = uniformly-continuous-₂ℕ

\end{code}

The coverage axiom amounts to uniform continuity of endo-functions of
the Cantor space in the following sense.

\begin{code}

Axiom[coverage] : ∀(m : ℕ) → ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C →
                   ∃ \(n : ℕ) → ∀(s : ₂Fin n) →
                    ∃ \(s' : ₂Fin m) → ∃ \(t' : E-map-₂ℕ-₂ℕ) →
                     (t' ∈ C) ∧ (∀(α : ₂ℕ) → π₀ t (cons s α) ≣ cons s' (π₀ t' α))
Axiom[coverage] m (t , et) uc = n , prf
 where
  n : ℕ
  n = ∃-witness (uc m)
  prf : ∀(s : ₂Fin n) → ∃ \(s' : ₂Fin m) → ∃ \(t' : E-map-₂ℕ-₂ℕ) →
         (t' ∈ C) ∧ (∀(α : ₂ℕ) → t (cons s α) ≣ cons s' (π₀ t' α))
  prf s = s' , (t' , et') , uc' , pr
   where
    s' : ₂Fin m
    s' = take m (t (cons s 0̄))
    t' : ₂ℕ → ₂ℕ
    t' α = drop m (t (cons s α))
    et' : ∀(α β : ₂ℕ) → α ≣ β → t' α ≣ t' β
    et' α β e = Lemma[drop-≣] m (t (cons s α)) (t (cons s β)) e'
     where
      e' : t (cons s α) ≣ t (cons s β)
      e' = et (cons s α) (cons s β) (Lemma[cons-E-map] s α β e)
    uc' : (t' , et') ∈ C
    uc' k = l , claim
     where
      ucts : uniformly-continuous-₂ℕ ((t , et) ◎ (E-cons s))
      ucts = Lemma[◎-UC] (t , et) uc (E-cons s) (Lemma[E-cons-UC] s)
      l : ℕ
      l = ∃-witness (ucts (k + m))
      claim : ∀(α β : ₂ℕ) → α ≣ l ≣ β → t' α ≣ k ≣ t' β
      claim α β eq i i<k = trans (trans claim₁ claim₀) (sym claim₂)
       where
        claim₀ : t (cons s α) (i + m) ≡ t (cons s β) (i + m)
        claim₀ = (∃-elim (ucts (k + m)) α β eq) (i + m) (Lemma[a<b→a+c<b+c] i k m i<k)
        claim₁ : t' α i ≡ t (cons s α) (i + m)
        claim₁ = Lemma[cons-drop] m (t (cons s α)) i
        claim₂ : t' β i ≡ t (cons s β) (i + m)
        claim₂ = Lemma[cons-drop] m (t (cons s β)) i
    pr : ∀(α : ₂ℕ) → t (cons s α) ≣ cons s' (t' α)
    pr α i = subst {₂Fin m} {λ x → t (cons s α) i ≡ cons x (t' α) i} claim₂ claim₀
     where
      claim₀ : t (cons s α) i ≡ cons (take m (t (cons s α))) (t' α) i
      claim₀ = sym (Lemma[cons-take-drop] m (t (cons s α)) i)
      claim₁ : t (cons s α) ≣ m ≣ t (cons s 0̄)
      claim₁ = ∃-elim (uc m) (cons s α) (cons s 0̄) (Lemma[cons-≣_≣] s α 0̄)
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

probe-axioms : (A : Setoid) → Subset(E-map-₂ℕ A) → Set
probe-axioms A P =
    (∀(p : E-map-₂ℕ A) → constant {E₂ℕ} {A} p → p ∈ P)
  ∧ (∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(p : E-map-₂ℕ A) → p ∈ P →
      ⟨ A ⟩ p ◎ t ∈ P)
  ∧ (∀(p : E-map-₂ℕ A) →
      (∃ \(n : ℕ) → ∀(s : ₂Fin n) → ⟨ A ⟩ p ◎ (E-cons s) ∈ P) → p ∈ P)
  ∧ (∀(p p' : E-map-₂ℕ A) → (∀(α : ₂ℕ) → E A (π₀ p α) (π₀ p' α)) → p ∈ P → p' ∈ P)


∏ : (X : Set) (Y : X → Set) → Set
∏ X Y = (x : X) → (Y x)
syntax ∏ A (λ x → B) = Π[ x ∶ A ] B

TopologyOn : Setoid → Set₁
TopologyOn A = Σ \(P : Subset(E-map-₂ℕ A)) → probe-axioms A P

Space : Set₁
Space = Σ \(A : Setoid) → TopologyOn A

U : Space → Setoid
U (A , _) = A

Ū : Space → Set
Ū X = Ũ (U X)

Probe : (X : Space) → Subset(E-map-₂ℕ (U X)) 
Probe (_ , P , _) = P

cond₀ : (X : Space) →
         ∀(p : E-map-₂ℕ (U X)) → constant {E₂ℕ} {U X} p → p ∈ Probe X
cond₀ (_ , _ , c , _) = c

cond₁ : (X : Space) →
         ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(p : E-map-₂ℕ (U X)) → p ∈ Probe X →
          ⟨ U X ⟩ p ◎ t ∈ Probe X
cond₁ (_ , _ , _ , c , _) = c

cond₂ : (X : Space) →
         ∀(p : E-map-₂ℕ (U X)) →
          (∃ \(n : ℕ) → ∀(s : ₂Fin n) → ⟨ U X ⟩ p ◎ (E-cons s) ∈ Probe X) →
           p ∈ Probe X
cond₂ (_ , _ , _ , _ , c , _) = c

cond₃ : (X : Space) →
         ∀(p p' : E-map-₂ℕ (U X)) → (∀(α : ₂ℕ) → E (U X) (π₀ p α) (π₀ p' α)) →
          p ∈ Probe X → p' ∈ Probe X
cond₃ (_ , _ , _ , _ , _ , c) = c

\end{code}

Then we define continuous functions between spaces and show that they
do form a category.

\begin{code}

continuous : {X Y : Space} → (E-map (U X) (U Y)) → Set
continuous {A , P , _} {B , Q , _} f = ∀ p → p ∈ P → ⟨ A ∣ B ⟩ f ◎ p ∈ Q

Map : Space → Space → Set
Map X Y = Σ \(f : E-map (U X) (U Y)) → continuous {X} {Y} f

MapSetoid : Space → Space → Setoid
MapSetoid X Y = Map X Y , _≋_ , c₀ , c₁ , c₂
 where
  _≈_ : Ũ (U Y) → Ũ (U Y) → Set
  _≈_ = E (U Y)
  _≋_ : Map X Y → Map X Y → Set
  ((f , _) , _) ≋ ((f' , _) , _) = ∀(x : Ũ (U X)) → f x ≈ f' x
  c₀ : ∀(f : Map X Y) → f ≋ f
  c₀ ((f , _) , _) x = π₀ (π₁ (π₁ (U Y))) (f x)
  c₁ : ∀(f f' : Map X Y) → f ≋ f' → f' ≋ f
  c₁ ((f , _) , _) ((f' , _) , _) e x = π₀ (π₁ (π₁ (π₁ (U Y)))) (f x) (f' x) (e x)
  c₂ : ∀(f₀ f₁ f₂ : Map X Y) → f₀ ≋ f₁ → f₁ ≋ f₂ → f₀ ≋ f₂
  c₂ ((f₀ , _) , _) ((f₁ , _) , _) ((f₂ , _) , _) e e' x =
          π₁ (π₁ (π₁ (π₁ (U Y)))) (f₀ x) (f₁ x) (f₂ x) (e x) (e' x)

id-is-continuous : ∀{X : Space} → continuous {X} {X} (E-id {U X})
id-is-continuous p pinP = pinP

◎-preserves-continuity : {X Y Z : Space} →
    ∀(f : E-map (U X) (U Y)) → continuous {X} {Y} f →
    ∀(g : E-map (U Y) (U Z)) → continuous {Y} {Z} g →
    continuous {X} {Z} (⟨ U X ∣ U Y ∣ U Z ⟩ g ◎ f)
◎-preserves-continuity {X} {Y} f cf g cg p pP = cg (⟨ U X ∣ U Y ⟩ f ◎ p) (cf p pP)


-- Initial C-space
-- The C-topology is empty

∅Space : Space
∅Space = E∅ , P , c₀ , c₁ , c₂ , c₃
 where
  P : Subset (E-map-₂ℕ E∅)
  P p = ∅
  c₀ : ∀(p : E-map-₂ℕ E∅) → constant {E₂ℕ} {E∅} p → p ∈ P
  c₀ p _ = π₀ p 0̄
  c₁ : ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(p : E-map-₂ℕ E∅) → p ∈ P →
        ⟨ E∅ ⟩ p ◎ t ∈ P
  c₁ _ _ p _ = π₀ p 0̄
  c₂ : ∀(p : E-map-₂ℕ E∅) →
        (∃ \(n : ℕ) → ∀(s : ₂Fin n) → ⟨ E∅ ⟩ p ◎ (E-cons s) ∈ P) →
         p ∈ P
  c₂ p _ = π₀ p 0̄
  c₃ : ∀(p p' : E-map-₂ℕ E∅) → (∀(α : ₂ℕ) → E E∅ (π₀ p α) (π₀ p' α)) → p ∈ P → p' ∈ P
  c₃ p _ _ _ = π₀ p 0̄


-- Terminal C-space
-- The unit map to ⒈ is the only probe

⒈Space : Space
⒈Space = E⒈ , P , c₀ , c₁ , c₂ , c₃
 where
  P : Subset (E-map-₂ℕ E⒈)
  P p = ⒈
  c₀ : ∀(p : E-map-₂ℕ E⒈) → constant {E₂ℕ} {E⒈} p → p ∈ P
  c₀ _ _ = ⋆
  c₁ : ∀(t : E-map-₂ℕ-₂ℕ) → t ∈ C → ∀(p : E-map-₂ℕ E⒈) → p ∈ P →
        ⟨ E⒈ ⟩ p ◎ t ∈ P
  c₁ _ _ _ _ = ⋆
  c₂ : ∀(p : E-map-₂ℕ E⒈) →
        (∃ \(n : ℕ) → ∀(s : ₂Fin n) → ⟨ E⒈ ⟩ p ◎ (E-cons s) ∈ P) →
         p ∈ P
  c₂ _ _ = ⋆
  c₃ : ∀(p p' : E-map-₂ℕ E⒈) → (∀(α : ₂ℕ) → π₀ p α ≡ π₀ p' α) → p ∈ P → p' ∈ P
  c₃ _ _ _ _ = ⋆

\end{code}
