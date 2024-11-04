Chuangjie Xu, 2012

\begin{code}

module Continuous-combinator where

open import Mini-library
open [_]
open import ConsHeadTail
open import Space
open import Space-exponential
open import Space-product
open import Space-discrete


-- K combinator with its continuity

continuous-k : {A B : Space} →
               Σ \(k : U A → U (B ⇒ A)) →
                   continuous {A} {B ⇒ A} k
continuous-k {A} {B} = (k , continuity-of-k)
 where
  k : U A → U (B ⇒ A)
  k a = (λ b → a) , λ p pa → cond₀ A (λ b → a) (hide (λ b b' → refl))
  continuity-of-k : continuous {A} {B ⇒ A} k
  continuity-of-k p pa q qb t uct = cond₁ A t uct p pa


-- S combinator with its continuity

continuous-s : {A B C : Space} →
               Σ \(s : U(A ⇒ B ⇒ C) → U((A ⇒ B) ⇒ A ⇒ C)) →
                   continuous {A ⇒ B ⇒ C} {(A ⇒ B) ⇒ A ⇒ C} s
continuous-s {A} {B} {C} = (s , continuity-of-s)
 where
  s : U(A ⇒ B ⇒ C) → U((A ⇒ B) ⇒ A ⇒ C)
  s f = (t , ct)
   where
    t : U(A ⇒ B) → U(A ⇒ C)
    t g = (h , ch)
     where
      h : U A → U C
      h a = π₀(π₀ f a)(π₀ g a)
      ch : continuous {A} {C} h
      ch p pa = claim₀ ((π₀ g) ∘ p) claim₁ id Lemma[id-UC]
       where
        claim₀ : (π₀ f) ∘ p ∈ Probe(B ⇒ C)
        claim₀ = π₁ f p pa
        claim₁ : (π₀ g) ∘ p ∈ Probe B
        claim₁ = π₁ g p pa
    ct : continuous {A ⇒ B} {A ⇒ C} t
    ct p pab q qa r ucr = claim₀ (λ α → (π₀ ∘ p)(r α)(q α)) claim₁ id Lemma[id-UC]
     where
      claim₀ : (π₀ f) ∘ q ∈ Probe(B ⇒ C)
      claim₀ = π₁ f q qa
      claim₁ : (λ α → (π₀ ∘ p)(r α)(q α)) ∈ Probe B
      claim₁ = pab q qa r ucr
  continuity-of-s : continuous {A ⇒ B ⇒ C} {(A ⇒ B) ⇒ A ⇒ C} s
  continuity-of-s p pabc q qab t uct r ra u ucu =
      claim₀ (λ α → (π₀ ∘ q)(u α)(r α)) claim₁ id Lemma[id-UC]
   where
    claim₀ : (λ α → (π₀ ∘ p)(t(u α))(r α)) ∈ Probe (B ⇒ C)
    claim₀ = pabc r ra (t ∘ u) (Lemma[∘-UC] t uct u ucu)
    claim₁ : (λ α → (π₀ ∘ q)(u α)(r α)) ∈ Probe B
    claim₁ = qab r ra u ucu


-- Case function with its continuity

continuous-if : {A : Space} →
                Σ \(If : U A → U(A ⇒ ₂Space ⇒ A)) →
                    continuous {A} {A ⇒ ₂Space ⇒ A} If
continuous-if {A} = (If , continuity-of-if)
 where
  If : U A → U(A ⇒ ₂Space ⇒ A)
  If a = (f , cf)
   where
    f : U A → U(₂Space ⇒ A)
    f a' = if a a' , Lemma[discreteness] {₂} {A} (if a a')
    cf : continuous {A} {₂Space ⇒ A} f
    cf p pa q q2 t uct = cond₂ A (λ α → if a (p(t α)) (q α)) (∃-intro n prf)
     where
      n : ℕ
      n = ∃-witness q2
      prf : ∀(s : ₂Fin n) → (λ α → if a (p (t (cons s α))) (q (cons s α))) ∈ Probe A
      prf s = cond₃ A (λ α → if a (p (t (cons s α))) (q (cons s (λ i → ₀))))
                    (λ α → if a (p (t (cons s α))) (q (cons s α)))
                    (lemma (q (cons s (λ i → ₀)))) claim
       where
        ucts : uniformly-continuous-₂ℕ (t ∘ (cons s))
        ucts = Lemma[∘-UC] t uct (cons s) (Lemma[cons-UC] s)
        lemma : ∀(b : ₂) → (λ α → if a (p (t (cons s α))) b) ∈ Probe A
        lemma ₀ = cond₀ A (λ α → a) (hide (λ α β → refl))
        lemma ₁ = cond₁ A (t ∘ (cons s)) ucts p pa
        eq : ∀(α : ₂ℕ) → [ q (cons s (λ i → ₀)) ≡ q (cons s α) ]
        eq α = hide (reveal (∃-elim q2) (cons s (λ i → ₀)) (cons s α)
                            (Lemma[cons-≣_≣] s (λ i → ₀) α))
        claim : [ (∀(α : ₂ℕ) → if a (p (t (cons s α))) (q (cons s (λ i → ₀))) ≡
                               if a (p (t (cons s α))) (q (cons s α))) ]
        claim = hide (λ α → cong (if a (p (t (cons s α)))) (reveal (eq α)))
  continuity-of-if : continuous {A} {A ⇒ ₂Space ⇒ A} If
  continuity-of-if p pa q qa t uct r r2 u ucu = cond₂ A (λ α → if (p(t(u α))) (q(u α)) (r α)) (∃-intro n prf)
   where
    n : ℕ
    n = ∃-witness r2
    prf : ∀(s : ₂Fin n) → (λ α → if (p(t(u(cons s α)))) (q(u(cons s α))) (r(cons s α))) ∈ Probe A
    prf s = cond₃ A (λ α → if (p(t(u(cons s α)))) (q(u(cons s α))) (r(cons s (λ i → ₀))))
                  (λ α → if (p(t(u(cons s α)))) (q(u(cons s α))) (r(cons s α)))
                  (lemma (r (cons s (λ i → ₀)))) claim
     where
      ucus : uniformly-continuous-₂ℕ (u ∘ (cons s))
      ucus = Lemma[∘-UC] u ucu (cons s) (Lemma[cons-UC] s)
      uctus : uniformly-continuous-₂ℕ (t ∘ u ∘ (cons s))
      uctus = Lemma[∘-UC] t uct (u ∘ (cons s)) ucus
      lemma : ∀(b : ₂) → (λ α → if (p(t(u(cons s α)))) (q(u(cons s α))) b) ∈ Probe A
      lemma ₀ = cond₁ A (t ∘ u ∘ (cons s)) uctus p pa
      lemma ₁ = cond₁ A (u ∘ (cons s)) ucus q qa
      eq : ∀(α : ₂ℕ) → [ r (cons s (λ i → ₀)) ≡ r (cons s α) ]
      eq α = hide (reveal (∃-elim r2) (cons s (λ i → ₀)) (cons s α)
                          (Lemma[cons-≣_≣] s (λ i → ₀) α))
      claim : [ (∀(α : ₂ℕ) → if (p(t(u(cons s α)))) (q(u(cons s α))) (r(cons s (λ i → ₀))) ≡
                             if (p(t(u(cons s α)))) (q(u(cons s α))) (r(cons s α))) ]
      claim = hide (λ α → cong (if (p(t(u(cons s α)))) (q(u(cons s α)))) (reveal (eq α)))


-- Successor with its continuity

continuous-succ : Σ \(s : ℕ → ℕ) → continuous {ℕSpace} {ℕSpace} s
continuous-succ = succ , Lemma[discreteness] {ℕ} {ℕSpace} succ


-- Rec function with its continuity

continuous-rec : {A : Space} →
                 Σ \(r : U(A ⇒ A) → U(A ⇒ ℕSpace ⇒ A)) →
                     continuous {A ⇒ A} {A ⇒ ℕSpace ⇒ A} r
continuous-rec {A} = (r , continuity-of-rec)
 where
  r : U(A ⇒ A) → U(A ⇒ ℕSpace ⇒ A)
  r f = (g , cg)
   where
    g : U A → U(ℕSpace ⇒ A)
    g a = rec (π₀ f) a , Lemma[discreteness] {ℕ} {A} (rec (π₀ f) a)
    cg : continuous {A} {ℕSpace ⇒ A} g
    cg p pa q qn t uct = cond₂ A (λ α → rec (π₀ f) (p(t α)) (q α)) (∃-intro n prf)
     where
      n : ℕ
      n = ∃-witness qn
      prf : ∀(s : ₂Fin n) → (λ α → rec (π₀ f) (p(t(cons s α))) (q(cons s α))) ∈ Probe A
      prf s = cond₃ A (λ α → rec (π₀ f) (p(t(cons s α))) (q(cons s (λ i → ₀))))
                      (λ α → rec (π₀ f) (p(t(cons s α))) (q(cons s α)))
                      (lemma (q(cons s (λ i → ₀)))) claim
       where
        ucts : uniformly-continuous-₂ℕ (t ∘ (cons s))
        ucts = Lemma[∘-UC] t uct (cons s) (Lemma[cons-UC] s)
        lemma : ∀(k : ℕ) → (λ α → rec (π₀ f) (p(t(cons s α))) k) ∈ Probe A
        lemma 0        = cond₁ A (t ∘ (cons s)) ucts p pa
        lemma (succ k) = cond₃ A (λ α → π₀ f (rec (π₀ f) (p(t(cons s α))) k))
                               (λ α → rec (π₀ f) (p(t(cons s α))) (succ k))
                               (π₁ f (λ α → rec (π₀ f) (p(t(cons s α))) k) (lemma k))
                               (hide (λ α → refl))
        eq : ∀(α : ₂ℕ) → [ q (cons s (λ i → ₀)) ≡ q (cons s α) ]
        eq α = hide (reveal (∃-elim qn) (cons s (λ i → ₀)) (cons s α)
                            (Lemma[cons-≣_≣] s (λ i → ₀) α))
        claim : [ (∀(α : ₂ℕ) → rec (π₀ f) (p(t(cons s α))) (q(cons s (λ i → ₀))) ≡
                               rec (π₀ f) (p(t(cons s α))) (q(cons s α))) ]
        claim = hide (λ α → cong (rec (π₀ f) (p(t(cons s α)))) (reveal (eq α)))
  continuity-of-rec : continuous {A ⇒ A} {A ⇒ ℕSpace ⇒ A} r
  continuity-of-rec p paa q qa t uct u un v ucv =
               cond₂ A (λ α → rec (π₀(p(t(v α)))) (q(v α)) (u α)) (∃-intro n prf)
   where
    n : ℕ
    n = ∃-witness un
    prf : ∀(s : ₂Fin n) → (λ α → rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) (u(cons s α))) ∈ Probe A
    prf s = cond₃ A (λ α → rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) (u(cons s (λ i → ₀))))
                  (λ α → rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) (u(cons s α)))
                  (lemma (u(cons s (λ i → ₀)))) claim
     where
      ucvs : uniformly-continuous-₂ℕ (v ∘ (cons s))
      ucvs = Lemma[∘-UC] v ucv (cons s) (Lemma[cons-UC] s)
      uctvs : uniformly-continuous-₂ℕ (t ∘ v ∘ (cons s))
      uctvs = Lemma[∘-UC] t uct (v ∘ (cons s)) ucvs
      lemma : ∀(k : ℕ) → (λ α → rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) k) ∈ Probe A
      lemma 0        = cond₁ A (v ∘ (cons s)) ucvs q qa
      lemma (succ k) = paa (λ α → rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) k) (lemma k)
                           (t ∘ v ∘ (cons s)) uctvs
      eq : ∀(α : ₂ℕ) → [ u(cons s (λ i → ₀)) ≡ u(cons s α) ]
      eq α = hide (reveal (∃-elim un) (cons s (λ i → ₀)) (cons s α)
                          (Lemma[cons-≣_≣] s (λ i → ₀) α))
      claim : [ (∀(α : ₂ℕ) →
                  rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) (u(cons s (λ i → ₀))) ≡
                  rec (π₀(p(t(v(cons s α))))) (q(v(cons s α))) (u(cons s α))) ]
      claim = hide (λ α → cong (rec (π₀(p(t(v(cons s α))))) (q(v(cons s α)))) (reveal (eq α)))


-- Unit function with its continuity

continuous-unit : {A : Space} →
                  Σ \(u : U A → ⒈) → continuous {A} {⒈Space} u
continuous-unit = unit , (λ p _ → ⋆)


-- Projection functions with their continuity

continuous-π₀ : {A B : Space} →
                Σ \(p : U (A ⊗ B) → U A) → continuous {A ⊗ B} {A} p
continuous-π₀ {A} {B} = π₀ , λ p pr → ∧-elim₀ pr

continuous-π₁ : {A B : Space} →
                Σ \(p : U (A ⊗ B) → U B) → continuous {A ⊗ B} {B} p
continuous-π₁ {A} {B} = π₁ , λ p pr → ∧-elim₁ pr
 


\end{code}