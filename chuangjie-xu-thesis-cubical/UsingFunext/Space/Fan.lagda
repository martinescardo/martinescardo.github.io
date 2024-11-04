Chuangjie Xu 2012

The axiom of uniform continuity is not provable in HAω, but can be
realized in our model by the following Fan functional:

       fan : Map ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace) ℕSpace

which continuously computes the least moduli of uniform continuity.

\begin{code}

{-# OPTIONS --without-K #-}

module UsingFunext.Space.Fan where

open import Preliminaries.SetsAndFunctions hiding (_+_)
open import Preliminaries.NaturalNumber
open import Preliminaries.Boolean
open import Preliminaries.Sequence
open import Continuity.UniformContinuity
open import UsingFunext.Funext
open import UsingFunext.Space.Coverage
open import UsingFunext.Space.Space
open import UsingFunext.Space.CartesianClosedness
open import UsingFunext.Space.DiscreteSpace
open import UsingFunext.Space.YonedaLemma

\end{code}

To show the continuity of the fan functional, we need the following auxiliaries.

\begin{code}

_×2 : ℕ → ℕ
_×2 zero        = zero
_×2 (succ n) = succ (succ (n ×2))

Lemma[n≤2n] : ∀(n : ℕ) → n ≤ (n ×2)
Lemma[n≤2n] zero        = ≤-zero
Lemma[n≤2n] (succ n) = ≤-trans (≤-succ (Lemma[n≤2n] n)) (Lemma[n≤n+1] (succ (n ×2)))

Lemma[n<m→2n<2m] : ∀(n m : ℕ) → n < m → (n ×2) < (m ×2)
Lemma[n<m→2n<2m] zero        zero        ()
Lemma[n<m→2n<2m] zero        (succ m) _          = ≤-succ ≤-zero
Lemma[n<m→2n<2m] (succ n) zero        ()
Lemma[n<m→2n<2m] (succ n) (succ m) (≤-succ r) = ≤-succ (≤-succ (Lemma[n<m→2n<2m] n m r))


_×2+1 : ℕ → ℕ
_×2+1 zero        = succ zero
_×2+1 (succ n) = succ (succ (n ×2+1))

Lemma[n≤2n+1] : ∀(n : ℕ) → n ≤ (n ×2+1)
Lemma[n≤2n+1] zero        = ≤-zero
Lemma[n≤2n+1] (succ n) = ≤-trans (≤-succ (Lemma[n≤2n+1] n)) (Lemma[n≤n+1] (succ (n ×2+1)))

Lemma[n<m→2n+1<2m+1] : ∀(n m : ℕ) → n < m → (n ×2+1) < (m ×2+1)
Lemma[n<m→2n+1<2m+1] zero        zero        ()
Lemma[n<m→2n+1<2m+1] zero        (succ m) _          = ≤-succ (≤-succ ≤-zero)
Lemma[n<m→2n+1<2m+1] (succ n) zero        ()
Lemma[n<m→2n+1<2m+1] (succ n) (succ m) (≤-succ r) = ≤-succ (≤-succ (Lemma[n<m→2n+1<2m+1] n m r))


\end{code}

Here is the fan functional, which calculates smallest moduli, using
the moduli obtained by Yoneda Lemma.

\begin{code}


fan : Map ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace) ℕSpace
fan = f , cts
 where
  f : U((ℕSpace ⇒ ₂Space) ⇒ ℕSpace) → ℕ
  f φ = pr₁ (pr₂ (Lemma[Yoneda] ℕSpace φ))
  cts : continuous ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace) ℕSpace f
  cts p pr = Lemma[LM-ℕ-least-modulus] (f ∘ p) n prf
   where
    t₀ : ₂ℕ → ₂ℕ
    t₀ α = α ∘ _×2
    uct₀ : t₀ ∈ C
    uct₀ m = Lemma[LM-₂ℕ-least-modulus] t₀ (m ×2) prf₁
     where
      prf₀ : ∀(α β : ₂ℕ) → α ≡[ m ×2 ] β → ∀(i : ℕ) → i < m → t₀ α i ≡ t₀ β i
      prf₀ α β aw i i<m = Lemma[≡[]-<] aw (i ×2) (Lemma[n<m→2n<2m] i m i<m)
      prf₁ : ∀(α β : ₂ℕ) → α ≡[ m ×2 ] β → t₀ α ≡[ m ] t₀ β
      prf₁ α β aw = Lemma[<-≡[]] (prf₀ α β aw)

    t₁ : ₂ℕ → ₂ℕ
    t₁ α = α ∘ _×2+1
    uct₁ : t₁ ∈ C
    uct₁ m = Lemma[LM-₂ℕ-least-modulus] t₁ (m ×2+1) prf₁ 
     where
      prf₀ : ∀(α β : ₂ℕ) → α ≡[ m ×2+1 ] β → ∀(i : ℕ) → i < m → t₁ α i ≡ t₁ β i
      prf₀ α β aw i i<m = Lemma[≡[]-<] aw (i ×2+1) (Lemma[n<m→2n+1<2m+1] i m i<m)
      prf₁ : ∀(α β : ₂ℕ) → α ≡[ m ×2+1 ] β → t₁ α ≡[ m ] t₁ β
      prf₁ α β aw = Lemma[<-≡[]] (prf₀ α β aw)

    t₁' : ₂ℕ → U(ℕSpace ⇒ ₂Space)
    t₁' = pr₁ (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] t₁ uct₁)
    prf₁ : t₁' ∈ Probe (ℕSpace ⇒ ₂Space)
    prf₁ = pr₂ (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] t₁ uct₁)

    merge : ₂ℕ → ₂ℕ → ₂ℕ
    merge α β zero               = α zero
    merge α β (succ zero)               = β zero
    merge α β (succ (succ i)) = merge (α ∘ succ) (β ∘ succ) i

    lemma' : ∀(α β γ : ₂ℕ) → ∀(k : ℕ) → α ≡[ k ] β → ∀(i : ℕ) → i < (k ×2)
           → merge α γ i ≡ merge β γ i
    lemma' α β γ zero        aw i ()
    lemma' α β γ (succ k) aw zero r = Lemma[≡[]-<] aw zero (≤-succ ≤-zero)
    lemma' α β γ (succ k) aw (succ zero) r = refl
    lemma' α β γ (succ k) aw (succ (succ i)) (≤-succ (≤-succ r)) =
          lemma' (α ∘ succ) (β ∘ succ) (γ ∘ succ) k (Lemma[≡[]-succ] aw) i r

    lemma : ∀(α β γ : ₂ℕ) → ∀(k : ℕ) → α ≡[ k ] β → merge α γ ≡[ k ×2 ] merge β γ
    lemma α β γ k ek = Lemma[<-≡[]] (lemma' α β γ k ek)

    lemma₀ : ∀(α β : ₂ℕ) → t₀ (merge α β) ≡ α
    lemma₀ α β = funext (le α β)
                --------
     where
      le : ∀(α β : ₂ℕ) → ∀(i : ℕ) → t₀ (merge α β) i ≡ α i
      le α β zero        = refl
      le α β (succ i) = le (α ∘ succ) (β ∘ succ) i

    lemma₁ : ∀(α β : ₂ℕ) → ∀(i : ℕ) → t₁ (merge α β) i ≡ β i
    lemma₁ α β zero        = refl
    lemma₁ α β (succ i) = lemma₁ (α ∘ succ) (β ∘ succ) i

    lemma₁' : ∀(α : ₂ℕ) → ∀(φ : Map ℕSpace ₂Space) → t₁' (merge α (pr₁  φ)) ≡ φ
    lemma₁' α (γ , ctsγ) = Lemma[Map-₂-≡] ℕSpace (β , ctsβ) (γ , ctsγ) claim
     where
      β : ₂ℕ
      β = pr₁ (t₁' (merge α γ))
      ctsβ : continuous ℕSpace ₂Space β
      ctsβ = pr₂ (t₁' (merge α γ))
      claim : ∀(i : ℕ) → β i ≡ γ i
      claim = lemma₁ α γ 

    q : ₂ℕ → ℕ
    q α = (pr₁ ∘ p)(t₀ α)(t₁' α)
    ucq : locally-constant q
    ucq = pr t₁' prf₁ t₀ uct₀

    n : ℕ
    n = pr₁ ucq

    claim : ∀(α β : ₂ℕ) → α ≡[ n ] β → p α ≡ p β
    claim α β en = Lemma[Map-ℕ-≡] (ℕSpace ⇒ ₂Space) (pα , ctsα) (pβ , ctsβ) sclaim
     where
      pα : Map ℕSpace ₂Space → ℕ
      pα = pr₁ (p α)
      ctsα : continuous (ℕSpace ⇒ ₂Space) ℕSpace pα
      ctsα = pr₂ (p α)
      pβ : Map ℕSpace ₂Space → ℕ
      pβ = pr₁ (p β)
      ctsβ : continuous (ℕSpace ⇒ ₂Space) ℕSpace pβ
      ctsβ = pr₂ (p β)
      sclaim : ∀(γ : Map ℕSpace ₂Space) → pα γ ≡ pβ γ
      sclaim (γ , ctsγ) = ssclaim₄
       where
        eγ : merge α γ ≡[ n ] merge β γ
        eγ = Lemma[≡[]-≤] (lemma α β γ n en) (Lemma[n≤2n] n)
        ssclaim₀ :   (pr₁ ∘ p)(t₀ (merge α γ))(t₁' (merge α γ))
                   ≡ (pr₁ ∘ p)(t₀ (merge β γ))(t₁' (merge β γ))
        ssclaim₀ = pr₁ (pr₂ ucq) (merge α γ) (merge β γ) eγ
        ssclaim₁ :   (pr₁ ∘ p)(α)(t₁' (merge α γ))
                   ≡ (pr₁ ∘ p)(t₀ (merge β γ))(t₁' (merge β γ))
        ssclaim₁ = transport (λ x → (pr₁ ∘ p)(x)(t₁' (merge α γ))
                                  ≡ (pr₁ ∘ p)(t₀ (merge β γ))(t₁' (merge β γ)))
                             (lemma₀ α γ) ssclaim₀
        ssclaim₂ : pr₁ (p α) (t₁' (merge α γ)) ≡ pr₁ (p β) (t₁' (merge β γ))
        ssclaim₂ = transport (λ x → (pr₁ ∘ p)(α)(t₁' (merge α γ)) ≡ (pr₁ ∘ p)(x)(t₁' (merge β γ)))
                             (lemma₀ β γ) ssclaim₁
        ssclaim₃ : pr₁ (p α) (γ , ctsγ) ≡ pr₁ (p β) (t₁' (merge β γ))
        ssclaim₃ = transport (λ x → pr₁ (p α) (x) ≡ pr₁ (p β) (t₁' (merge β γ)))
                             (lemma₁' α (γ , ctsγ)) ssclaim₂
        ssclaim₄ : pr₁ (p α) (γ , ctsγ) ≡ pr₁ (p β) (γ , ctsγ)
        ssclaim₄ = transport (λ x → pr₁ (p α) (γ , ctsγ) ≡ pr₁ (p β) (x))
                             (lemma₁' β (γ , ctsγ)) ssclaim₃

    prf : ∀(α β : ₂ℕ) → α ≡[ n ] β → (f ∘ p) α ≡ (f ∘ p) β
    prf α β en = ap f (claim α β en)


fan-behaviour : ∀(f : U ((ℕSpace ⇒ ₂Space) ⇒ ℕSpace)) →
                ∀(α β : U (ℕSpace ⇒ ₂Space)) → pr₁ α ≡[ pr₁ fan f ] pr₁ β → pr₁ f α ≡ pr₁ f β
fan-behaviour f α β r = eqα · claim · eqβ ⁻¹
 where
  f' : ₂ℕ → ℕ
  f' = pr₁ (Lemma[Yoneda] ℕSpace f)
  claim : f' (pr₁ α) ≡ f' (pr₁ β)
  claim = pr₁(pr₂ (pr₂ (Lemma[Yoneda] ℕSpace f))) (pr₁ α) (pr₁ β) r
  eqα : pr₁ f α ≡ f' (pr₁ α)
  eqα = ap (pr₁ f) (Lemma[ID-≡] α)
  eqβ : pr₁ f β ≡ f' (pr₁ β)
  eqβ = ap (pr₁ f) (Lemma[ID-≡] β)

\end{code}
