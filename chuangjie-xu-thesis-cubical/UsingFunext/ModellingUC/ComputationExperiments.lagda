Chuangjie Xu & Martin Escardo 2014 (updated in February 2015)

(Modified 9th Nov 2017, to show that the original non-normalizing term
now normalizes to zero as predicted. The original normal form (367
lines) is included for the record.)

Experiment of computing moduli of uniform continuity

\begin{code}

{-# OPTIONS --cubical #-}
{-# OPTIONS --without-K #-}

module UsingFunext.ModellingUC.ComputationExperiments where

open import Preliminaries.SetsAndFunctions hiding (_+_)
open import Preliminaries.NaturalNumber
open import Preliminaries.Boolean
open import Preliminaries.Sequence
open import UsingFunext.Space.Space
open import UsingFunext.Space.DiscreteSpace
open import UsingFunext.Space.CartesianClosedness
open import UsingFunext.Space.YonedaLemma
open import UsingFunext.Space.Fan
open import UsingFunext.ModellingUC.UCinT

\end{code}

We define an abbreviation of the interpretation of closed terms with
meaning in the function space ₂ℕ → ℕ:

\begin{code}

⟦_⟧ : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ) → ₂ℕ → ℕ
⟦ t ⟧ α = pr₁ (pr₁ ⟦ t ⟧ᵐ ⋆) (ID α)

modu : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ) → ℕ
modu F = pr₁ fan (pr₁ ⟦ F ⟧ᵐ ⋆)

ONE TWO THREE FOUR FIVE : {n : ℕ}{Γ : Cxt n} → Tm Γ Ⓝ
ONE   = SUCC ∙ ZERO
TWO   = SUCC ∙ ONE
THREE = SUCC ∙ TWO
FOUR  = SUCC ∙ THREE
FIVE  = SUCC ∙ FOUR

\end{code}

Both F₁ and F₂ is constant.

\begin{code}

F₁ F₂ : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ)

F₁ = LAM TWO

F₁-interpretation : ⟦ F₁ ⟧ ≡ λ α → succ (succ zero)
F₁-interpretation = refl

F₂ = LAM (IF ∙ ⊤ ∙ TWO ∙ TWO)

F₂-interpretation : ⟦ F₂ ⟧ ≡ λ α → succ (succ zero)
F₂-interpretation = refl

\end{code}

\begin{code}

open import Continuity.UniformContinuity
open import UsingFunext.Funext

F₁-F₂-same-interpretation : ⟦ F₁ ⟧ ≡ ⟦ F₂ ⟧
F₁-F₂-same-interpretation = refl

modu-F₁-normal-form : modu F₁ ≡ zero
modu-F₁-normal-form = refl

modu-F₂-normal-form : modu F₂ ≡ zero
modu-F₂-normal-form = refl

\end{code}

This is the normal form computed by the original version that doesn't use cubical Agda:

\begin{code}

old-modu-F₂-normal-form : modu F₂ ≡ LM {ℕ} (_≡_ {_} {ℕ}) ℕ-discrete (λ α → (succ (succ zero)))
 (zero +
 pr₁
 (transport {_} {_}
  {(x : ℕ → ₂) → ℕ → ₂} {λ x → x} {λ x → x}
  (λ x →
     Σ {_} {_} {ℕ}
     (λ n →
        Σ {_} {_}
        {(α β : ℕ → ₂) →
         _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (succ (succ zero)) (succ (succ zero))}
        (λ x₁ →
           (n' : ℕ) →
           ((α β : ℕ → ₂) →
            _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (succ (succ zero)) (succ (succ zero))) →
           n ≤ n')))
  (_⁻¹ {_} {(x : ℕ → ₂) → ℕ → ₂} {λ x → x}
   {λ x → x}
   (funext {ℕ → ₂} {λ _ → (x : ℕ) → ₂} {λ x → x} {λ x → x}
    (λ x → funext {ℕ} {λ y → ₂} {x} {x} (λ i → refl {_} {_} {x i}))))
  (transport {_} {_}
   {(x : ℕ → ₂) → ℕ → ₂} {λ x → x} {λ x → x}
   (λ x →
      (p : (ℕ → ₂) → ℕ) →
      Σ {_} {_} {ℕ}
      (λ n →
         Σ {_} {_}
         {(α β : ℕ → ₂) →
          _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
         (λ x₁ →
            (n' : ℕ) →
            ((α β : ℕ → ₂) →
             _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
            n ≤ n')) →
      (t : (ℕ → ₂) → ℕ → ₂) →
      ((m : ℕ) →
       Σ {_} {_} {ℕ}
       (λ n →
          Σ {_} {_}
          {(α β : ℕ → ₂) → _≡[_]_ {₂} α n β → _≡[_]_ {₂} (t α) m (t β)}
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → ₂) → _≡[_]_ {₂} α n' β → _≡[_]_ {₂} (t α) m (t β)) →
             n ≤ n'))) →
      Σ {_} {_} {ℕ}
      (λ n →
         Σ {_} {_}
         {(α β : ℕ → ₂) →
          _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
         (λ x₁ →
            (n' : ℕ) →
            ((α β : ℕ → ₂) →
             _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
            n ≤ n')))
   (_⁻¹ {_} {(x : ℕ → ₂) → ℕ → ₂} {λ x → x}
    {λ x → x}
    (funext {ℕ → ₂} {λ _ → (x : ℕ) → ₂} {λ x → x} {λ x → x}
     (λ x → funext {ℕ} {λ y → ₂} {x} {x} (λ i → refl {_} {_} {x i}))))
   (transport {_} {_}
    {(ℕ → ₂) →
     Σ {_} {_}
     {ℕ →
      Σ {_} {_} {ℕ → ℕ}
      (λ f →
         (p : (ℕ → ₂) → ℕ) →
         Σ {_} {_} {ℕ}
         (λ n →
            Σ {_} {_}
            {(α β : ℕ → ₂) →
             _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → ₂) →
                _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
               n ≤ n')) →
         Σ {_} {_} {ℕ}
         (λ n →
            Σ {_} {_}
            {(α β : ℕ → ₂) →
             _≡[_]_ {₂} α n β →
             _≡_ {_} {ℕ} (f (p α)) (f (p β))}
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → ₂) →
                _≡[_]_ {₂} α n' β →
                _≡_ {_} {ℕ} (f (p α)) (f (p β))) →
               n ≤ n')))}
     (λ f →
        (p : (ℕ → ₂) → ℕ) →
        Σ {_} {_} {ℕ}
        (λ n →
           Σ {_} {_}
           {(α β : ℕ → ₂) →
            _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → ₂) →
               _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
              n ≤ n')) →
        (p₁ : (ℕ → ₂) → ℕ) →
        Σ {_} {_} {ℕ}
        (λ n →
           Σ {_} {_}
           {(α β : ℕ → ₂) →
            _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p₁ α) (p₁ β)}
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → ₂) →
               _≡[_]_ {₂} α n' β →
               _≡_ {_} {ℕ} (p₁ α) (p₁ β)) →
              n ≤ n')) →
        (t : (ℕ → ₂) → ℕ → ₂) →
        ((m : ℕ) →
         Σ {_} {_} {ℕ}
         (λ n →
            Σ {_} {_}
            {(α β : ℕ → ₂) → _≡[_]_ {₂} α n β → _≡[_]_ {₂} (t α) m (t β)}
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → ₂) → _≡[_]_ {₂} α n' β → _≡[_]_ {₂} (t α) m (t β)) →
               n ≤ n'))) →
        Σ {_} {_} {ℕ}
        (λ n →
           Σ {_} {_}
           {(α β : ℕ → ₂) →
            _≡[_]_ {₂} α n β →
            _≡_ {_} {ℕ} (pr₁ (f (p (t α))) (p₁ α))
            (pr₁ (f (p (t β))) (p₁ β))}
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → ₂) →
               _≡[_]_ {₂} α n' β →
               _≡_ {_} {ℕ} (pr₁ (f (p (t α))) (p₁ α))
               (pr₁ (f (p (t β))) (p₁ β))) →
              n ≤ n')))}
    {λ α →
       (λ a₀ → (λ a₁ → a₁) , (λ p pA → pA)) , (λ p pA q qA t tC → qA)}
    {λ x →
       (λ a₀ → (λ a₁ → a₁) , (λ p pA → pA)) , (λ p pA q qA t tC → qA)}
    (λ r →
       (p : (ℕ → ₂) → ℕ) →
       Σ {_} {_} {ℕ}
       (λ n →
          Σ {_} {_}
          {(α β : ℕ → ₂) →
           _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
          (λ x →
             (n' : ℕ) →
             ((α β : ℕ → ₂) →
              _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
             n ≤ n')) →
       (t : (ℕ → ₂) → ℕ → ₂) →
       ((m : ℕ) →
        Σ {_} {_} {ℕ}
        (λ n →
           Σ {_} {_}
           {(α β : ℕ → ₂) → _≡[_]_ {₂} α n β → _≡[_]_ {₂} (t α) m (t β)}
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → ₂) → _≡[_]_ {₂} α n' β → _≡[_]_ {₂} (t α) m (t β)) →
              n ≤ n'))) →
       (p₁ : (ℕ → ₂) → ℕ) →
       Σ {_} {_} {ℕ}
       (λ n →
          Σ {_} {_}
          {(α β : ℕ → ₂) →
           _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p₁ α) (p₁ β)}
          (λ x →
             (n' : ℕ) →
             ((α β : ℕ → ₂) →
              _≡[_]_ {₂} α n' β →
              _≡_ {_} {ℕ} (p₁ α) (p₁ β)) →
             n ≤ n')) →
       (t₁ : (ℕ → ₂) → ℕ → ₂) →
       ((m : ℕ) →
        Σ {_} {_} {ℕ}
        (λ n →
           Σ {_} {_}
           {(α β : ℕ → ₂) → _≡[_]_ {₂} α n β → _≡[_]_ {₂} (t₁ α) m (t₁ β)}
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → ₂) → _≡[_]_ {₂} α n' β → _≡[_]_ {₂} (t₁ α) m (t₁ β)) →
              n ≤ n'))) →
       Σ {_} {_} {ℕ}
       (λ n →
          Σ {_} {_}
          {(α β : ℕ → ₂) →
           _≡[_]_ {₂} α n β →
           _≡_ {_} {ℕ}
           (pr₁ (pr₁ (r (t (t₁ α))) (p (t₁ α))) (p₁ α))
           (pr₁ (pr₁ (r (t (t₁ β))) (p (t₁ β))) (p₁ β))}
          (λ x →
             (n' : ℕ) →
             ((α β : ℕ → ₂) →
              _≡[_]_ {₂} α n' β →
              _≡_ {_} {ℕ}
              (pr₁ (pr₁ (r (t (t₁ α))) (p (t₁ α))) (p₁ α))
              (pr₁ (pr₁ (r (t (t₁ β))) (p (t₁ β))) (p₁ β))) →
             n ≤ n')))
    (funext {ℕ → ₂}
     {λ _ →
        Σ {_} {_}
        {ℕ →
         Σ {_} {_} {ℕ → ℕ}
         (λ f →
            (p : (ℕ → ₂) → ℕ) →
            Σ {_} {_} {ℕ}
            (λ n →
               Σ {_} {_}
               {(α β : ℕ → ₂) →
                _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
               (λ x →
                  (n' : ℕ) →
                  ((α β : ℕ → ₂) →
                   _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
                  n ≤ n')) →
            Σ {_} {_} {ℕ}
            (λ n →
               Σ {_} {_}
               {(α β : ℕ → ₂) →
                _≡[_]_ {₂} α n β →
                _≡_ {_} {ℕ} (f (p α)) (f (p β))}
               (λ x →
                  (n' : ℕ) →
                  ((α β : ℕ → ₂) →
                   _≡[_]_ {₂} α n' β →
                   _≡_ {_} {ℕ} (f (p α)) (f (p β))) →
                  n ≤ n')))}
        (λ f →
           (p : (ℕ → ₂) → ℕ) →
           Σ {_} {_} {ℕ}
           (λ n →
              Σ {_} {_}
              {(α β : ℕ → ₂) →
               _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p α) (p β)}
              (λ x →
                 (n' : ℕ) →
                 ((α β : ℕ → ₂) →
                  _≡[_]_ {₂} α n' β → _≡_ {_} {ℕ} (p α) (p β)) →
                 n ≤ n')) →
           (p₁ : (ℕ → ₂) → ℕ) →
           Σ {_} {_} {ℕ}
           (λ n →
              Σ {_} {_}
              {(α β : ℕ → ₂) →
               _≡[_]_ {₂} α n β → _≡_ {_} {ℕ} (p₁ α) (p₁ β)}
              (λ x →
                 (n' : ℕ) →
                 ((α β : ℕ → ₂) →
                  _≡[_]_ {₂} α n' β →
                  _≡_ {_} {ℕ} (p₁ α) (p₁ β)) →
                 n ≤ n')) →
           (t : (ℕ → ₂) → ℕ → ₂) →
           ((m : ℕ) →
            Σ {_} {_} {ℕ}
            (λ n →
               Σ {_} {_}
               {(α β : ℕ → ₂) → _≡[_]_ {₂} α n β → _≡[_]_ {₂} (t α) m (t β)}
               (λ x →
                  (n' : ℕ) →
                  ((α β : ℕ → ₂) → _≡[_]_ {₂} α n' β → _≡[_]_ {₂} (t α) m (t β)) →
                  n ≤ n'))) →
           Σ {_} {_} {ℕ}
           (λ n →
              Σ {_} {_}
              {(α β : ℕ → ₂) →
               _≡[_]_ {₂} α n β →
               _≡_ {_} {ℕ} (pr₁ (f (p (t α))) (p₁ α))
               (pr₁ (f (p (t β))) (p₁ β))}
              (λ x →
                 (n' : ℕ) →
                 ((α β : ℕ → ₂) →
                  _≡[_]_ {₂} α n' β →
                  _≡_ {_} {ℕ} (pr₁ (f (p (t α))) (p₁ α))
                  (pr₁ (f (p (t β))) (p₁ β))) →
                 n ≤ n')))}
     {λ x →
        (λ a₀ → (λ a₁ → a₁) , (λ p pA → pA)) , (λ p pA q qA t tC → qA)}
     {λ x →
        (λ a₀ → (λ a₁ → a₁) , (λ p pA → pA)) , (λ p pA q qA t tC → qA)}
     (λ α →
        refl {_} {_}
        {(λ a₀ → (λ a₁ → a₁) , (λ p pA → pA)) , (λ p pA q qA t tC → qA)}))
    (λ p pP t uc q qA t₁ tC → qA) (λ x → (succ (succ zero)))
    (zero , (λ α β e → refl {_} {_} {(succ (succ zero))}) , (λ k prk → ≤-zero {k}))
    (λ α → α)
    (λ k →
       LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
       (λ α → α)
       (LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
        (λ x → x) k)
       ,
       Lemma[LM-modulus] {ℕ → ₂} (λ α → _≡[_]_ {₂} α k)
       (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ α → α)
       (LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
        (λ x → x) k)
       (λ α β el →
          Lemma[<-≡[]] {k} {α} {β}
          (λ i i<k →
             _·_ {_} {₂} {α i} {β i} {β i}
             (_·_ {_} {₂} {α i} {α i} {β i}
              (refl {_} {_} {α i})
              (Lemma[≡[]-<] {k} {α} {β}
               (Lemma[LM-modulus] {ℕ → ₂} (λ α₁ → _≡[_]_ {₂} α₁ k)
                (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ x → x)
                k (λ α₁ β₁ e → e) α β el)
               i i<k))
             (refl {_} {_} {β i})))
       ,
       Lemma[LM-least] {ℕ → ₂} (λ α → _≡[_]_ {₂} α k)
       (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ α → α)
       (LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
        (λ x → x) k)
       (λ α β el →
          Lemma[<-≡[]] {k} {α} {β}
          (λ i i<k →
             _·_ {_} {₂} {α i} {β i} {β i}
             (_·_ {_} {₂} {α i} {α i} {β i}
              (refl {_} {_} {α i})
              (Lemma[≡[]-<] {k} {α} {β}
               (Lemma[LM-modulus] {ℕ → ₂} (λ α₁ → _≡[_]_ {₂} α₁ k)
                (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ x → x)
                k (λ α₁ β₁ e → e) α β el)
               i i<k))
             (refl {_} {_} {β i})))))
   (λ x → (succ (succ zero)))
   (zero , (λ α β e → refl {_} {_} {(succ (succ zero))}) , (λ k prk → ≤-zero {k}))
   (λ α → α)
   (λ k →
      LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
      (λ α → α)
      (LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
       (λ x → x) k)
      ,
      Lemma[LM-modulus] {ℕ → ₂} (λ α → _≡[_]_ {₂} α k)
      (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ α → α)
      (LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
       (λ x → x) k)
      (λ α β el →
         Lemma[<-≡[]] {k} {α} {β}
         (λ i i<k →
            _·_ {_} {₂} {α i} {β i} {β i}
            (_·_ {_} {₂} {α i} {α i} {β i}
             (refl {_} {_} {α i})
             (Lemma[≡[]-<] {k} {α} {β}
              (Lemma[LM-modulus] {ℕ → ₂} (λ α₁ → _≡[_]_ {₂} α₁ k)
               (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ x → x)
               k (λ α₁ β₁ e → e) α β el)
              i i<k))
            (refl {_} {_} {β i})))
      ,
      Lemma[LM-least] {ℕ → ₂} (λ α → _≡[_]_ {₂} α k)
      (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ α → α)
      (LM {ℕ → ₂} (λ α → _≡[_]_ {₂} α k) (Lemma[≡[]-decidable] {k})
       (λ x → x) k)
      (λ α β el →
         Lemma[<-≡[]] {k} {α} {β}
         (λ i i<k →
            _·_ {_} {₂} {α i} {β i} {β i}
            (_·_ {_} {₂} {α i} {α i} {β i}
             (refl {_} {_} {α i})
             (Lemma[≡[]-<] {k} {α} {β}
              (Lemma[LM-modulus] {ℕ → ₂} (λ α₁ → _≡[_]_ {₂} α₁ k)
               (Lemma[≡[]-decidable] {k}) (≡[]-sym {k}) (≡[]-trans {k}) (λ x → x)
               k (λ α₁ β₁ e → e) α β el)
              i i<k))
            (refl {_} {_} {β i})))))))
old-modu-F₂-normal-form = refl


\end{code}
