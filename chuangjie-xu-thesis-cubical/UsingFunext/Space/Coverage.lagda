Chuangjie Xu 2012

\begin{code}

{-# OPTIONS --without-K #-}

module UsingFunext.Space.Coverage where

open import Preliminaries.SetsAndFunctions hiding (_+_)
open import Preliminaries.NaturalNumber
open import Preliminaries.Boolean
open import Preliminaries.Sequence
open import UsingFunext.Funext
open import Continuity.UniformContinuity

\end{code}

The site we are working with is the monoid of uniformly continuous
endo-functions of the Cantor space with a coverage in which, for each
natural number n, there is a family of concatenation maps "cons s"
indexed by finite binary sequence s of length n.

The monoid of uniformly continuous ₂ℕ → ₂ℕ:

\begin{code}

C : Subset(₂ℕ → ₂ℕ)
C = uniformly-continuous-₂ℕ

\end{code}

The coverage axiom amounts to uniform continuity of endo-functions of
the Cantor space in the following sense.

\begin{code}

Theorem[Coverage-axiom] : ∀(m : ℕ) → ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
                   Σ \(n : ℕ) → ∀(s : ₂Fin n) →
                    Σ \(s' : ₂Fin m) → Σ \(t' : ₂ℕ → ₂ℕ) →
                     (t' ∈ C) × (t ∘ cons s ≡ cons s' ∘ t')
Theorem[Coverage-axiom] m t tC = n , prf
 where
  n : ℕ
  n = pr₁ (tC m)
  prf : ∀(s : ₂Fin n) → Σ \(s' : ₂Fin m) → Σ \(t' : ₂ℕ → ₂ℕ) →
         (t' ∈ C) × (t ∘ cons s ≡ cons s' ∘ t')
  prf s = s' ,  t' , t'C , e
   where
    s' : ₂Fin m
    s' = take m (t (cons s zerō))

    t' : ₂ℕ → ₂ℕ
    t' α = drop m (t (cons s α))

    t'C : t' ∈ C
    t'C k = Lemma[LM-₂ℕ-least-modulus] t' l prt'
     where
      ucts : uniformly-continuous-₂ℕ (t ∘ (cons s))
      ucts = Lemma[∘-UC] t tC (cons s) (Lemma[cons-UC] s)
      l : ℕ
      l = pr₁ (ucts (k + m))
      prts : ∀(α β : ₂ℕ) → α ≡[ l ] β → t (cons s α) ≡[ k + m ] t (cons s β)
      prts = pr₁ (pr₂ (ucts (k + m)))
      eq : ∀(α : ₂ℕ) → ∀(i : ℕ) → t' α i ≡ t (cons s α) (i + m)
      eq α i = Lemma[drop+] m (t (cons s α)) i
      claim₀ : ∀(α β : ₂ℕ) → α ≡[ l ] β → t (cons s α) ≡[ k + m ] t (cons s β) →
                ∀(i : ℕ) → i < k → t' α i ≡ t' β i
      claim₀ α β el ekm i i<k = sclaim₂ · (eq β i)⁻¹
       where
        sclaim₀ : ∀(i : ℕ) → i < (k + m) → t (cons s α) i ≡ t (cons s β) i
        sclaim₀ = Lemma[≡[]-<] ekm
        sclaim₁ : t (cons s α) (i + m) ≡ t (cons s β) (i + m)
        sclaim₁ = sclaim₀ (i + m) (Lemma[a<b→a+c<b+c] i k m i<k)
        sclaim₂ : t' α i ≡ t (cons s β) (i + m)
        sclaim₂ = eq α i · sclaim₁ 
      claim₁ : ∀(α β : ₂ℕ) → α ≡[ l ] β
             → t (cons s α) ≡[ k + m ] t (cons s β) → t' α ≡[ k ] t' β
      claim₁ α β el ekm = Lemma[<-≡[]] (claim₀ α β el ekm)
      prt' : ∀(α β : ₂ℕ) → α ≡[ l ] β → t' α ≡[ k ] t' β
      prt' α β el = claim₁ α β el (prts α β el)
    ex : ∀(α : ₂ℕ) → ∀(i : ℕ) → t (cons s α) i ≡ cons s' (t' α) i
    ex α i = sclaim₀ · sclaim₃
     where
      sclaim₀ : t (cons s α) i ≡ cons (take m (t (cons s α))) (t' α) i
      sclaim₀ = (Lemma[cons-take-drop] m (t (cons s α)) i)⁻¹
      sclaim₁ : t (cons s α) ≡[ m ] t (cons s zerō)
      sclaim₁ = pr₁ (pr₂ (tC m)) (cons s α) (cons s zerō) (Lemma[cons-≡[]] s α zerō)
      sclaim₂ : take m (t (cons s α)) ≡ s'
      sclaim₂ = Lemma[≡[]-take] sclaim₁
      sclaim₃ : cons (take m (t (cons s α))) (t' α) i ≡ cons s' (t' α) i
      sclaim₃ = ap (λ x → cons x (t' α) i) sclaim₂
    e : t ∘ cons s ≡ cons s' ∘ t'
    e = funext² ex
       ---------

\end{code}

A special case of Theorem[Coverage-axiom]:

\begin{code}

Theorem[Coverage-axiom]₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
                   Σ \(n : ℕ) → ∀(s : ₂Fin n) →
                    Σ \(i : ₂) → Σ \(t' : ₂ℕ → ₂ℕ) →
                     (t' ∈ C) × (t ∘ cons s ≡ cons (i ∷ ⟨⟩) ∘ t')
Theorem[Coverage-axiom]₁ t tC = n , prf
 where
  n : ℕ
  n = pr₁ (Theorem[Coverage-axiom] (succ zero) t tC)
  prf : ∀(s : ₂Fin n) → Σ \(i : ₂) → Σ \(t' : ₂ℕ → ₂ℕ) →
         (t' ∈ C) × (t ∘ cons s ≡ cons (i ∷ ⟨⟩) ∘ t')
  prf s = i , pr₂ (pr₂ (Theorem[Coverage-axiom] (succ zero) t tC) s)
   where
    to₂ : ₂Fin (succ zero) → ₂
    to₂ (i ∷ ⟨⟩) = i
    i : ₂
    i = to₂ (pr₁ (pr₂ (Theorem[Coverage-axiom] (succ zero) t tC) s))
    

\end{code}
