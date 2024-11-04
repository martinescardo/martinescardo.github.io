Chuangjie Xu, 2012

\begin{code}

module Least-moduli-of-uniform-continuity where

open import Mini-library
open import Uniform-continuity
open import ConsHeadTail
open import Setoid


Lemma[₂Fin-decidability] : (P : (n : ℕ) → ₂Fin n → Set) →
     (∀(n : ℕ) → ∀(s : ₂Fin n) → decidable (P n s)) →
     ∀(n : ℕ) → decidable (∀(s : ₂Fin n) → P n s)
Lemma[₂Fin-decidability] P f 0 = cases claim₀ claim₁ (f 0 ⟨⟩)
 where
  claim₀ : P 0 ⟨⟩ → ∀(s : ₂Fin 0) → P 0 s
  claim₀ p ⟨⟩ = p
  claim₁ : ¬ (P 0 ⟨⟩) → ¬ (∀(s : ₂Fin 0) → P 0 s)
  claim₁ q g = q (g ⟨⟩)
Lemma[₂Fin-decidability] P f (succ n) = cases claim₀ claim₁ IH
 where
  Q : (m : ℕ) → ₂Fin m → Set
  Q m s = P (succ m) (₀ ∷ s) ∧ P (succ m) (₁ ∷ s)
  claim : ∀(m : ℕ) → ∀(s : ₂Fin m) → decidable (Q m s)
  claim m s = case sclaim₀ sclaim₁ (f (succ m) (₀ ∷ s))
   where
    sclaim₀ : P (succ m) (₀ ∷ s) → decidable (Q m s)
    sclaim₀ p0s = cases ssclaim₀ ssclaim₁ (f (succ m) (₁ ∷ s))
     where
      ssclaim₀ : P (succ m) (₁ ∷ s) → Q m s
      ssclaim₀ p1s = ∧-intro p0s p1s
      ssclaim₁ : ¬ (P (succ m) (₁ ∷ s)) → ¬ (Q m s)
      ssclaim₁ np1s nq = np1s (∧-elim₁ nq)
    sclaim₁ : ¬ (P (succ m) (₀ ∷ s)) → decidable (Q m s)
    sclaim₁ np0s = in₁ (λ nq → np0s (∧-elim₀ nq))
  claim₀ : (∀(s : ₂Fin n) → P (succ n) (₀ ∷ s) ∧ P (succ n) (₁ ∷ s)) →
            ∀(s : ₂Fin (succ n)) → P (succ n) s
  claim₀ g (₀ ∷ s) = ∧-elim₀ (g s)
  claim₀ g (₁ ∷ s) = ∧-elim₁ (g s)
  claim₁ : ¬ (∀(s : ₂Fin n) → P (succ n) (₀ ∷ s) ∧ P (succ n) (₁ ∷ s)) →
            ¬ (∀(s : ₂Fin (succ n)) → P (succ n) s)
  claim₁ h g = h (λ s → g (₀ ∷ s) , g (₁ ∷ s))
  IH : decidable (∀(s : ₂Fin n) → P (succ n) (₀ ∷ s) ∧ P (succ n) (₁ ∷ s))
  IH = Lemma[₂Fin-decidability] Q claim n


Lemma[decidable-0̄-1̄] : (p : ₂ℕ → ℕ) → (m : ℕ) →
         decidable (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄))
Lemma[decidable-0̄-1̄] p m = Lemma[₂Fin-decidability] P claim m
 where
  P : (m : ℕ) → ₂Fin m → Set
  P m s = p (cons s 0̄) ≡ p (cons s 1̄)
  claim : ∀(m : ℕ) → ∀(s : ₂Fin m) → decidable (P m s)
  claim m s = ℕ-discrete (p (cons s 0̄)) (p (cons s 1̄))


LM : (₂ℕ → ℕ) → ℕ → ℕ
LM p 0        = 0
LM p (succ m) = case f₀ f₁ (Lemma[decidable-0̄-1̄] p m)
 where
  f₀ : (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) → ℕ
  f₀ _ = LM p m
  f₁ : ¬ (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) → ℕ
  f₁ _ = succ m


Lemma[LM]₀ : (p : ₂ℕ → ℕ) → (m : ℕ) →
             (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) →
             LM p (succ m) ≡ LM p m
Lemma[LM]₀ p m h = equality-cases (Lemma[decidable-0̄-1̄] p m) claim₀ claim₁
 where
  claim₀ : ∀ h → Lemma[decidable-0̄-1̄] p m ≡ in₀ h → LM p (succ m) ≡ LM p m
  claim₀ h r = cong (case _ _) r
  claim₁ : ∀ f → Lemma[decidable-0̄-1̄] p m ≡ in₁ f → LM p (succ m) ≡ LM p m
  claim₁ f = ∅-elim(f h) 

Lemma[LM]₁ : (p : ₂ℕ → ℕ) → (m : ℕ) →
             ¬ (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) →
             LM p (succ m) ≡ succ m
Lemma[LM]₁ p m f = equality-cases (Lemma[decidable-0̄-1̄] p m) claim₀ claim₁
 where
  claim₀ : ∀ h → Lemma[decidable-0̄-1̄] p m ≡ in₀ h → LM p (succ m) ≡ succ m
  claim₀ h = ∅-elim (f h)
  claim₁ : ∀ f → Lemma[decidable-0̄-1̄] p m ≡ in₁ f → LM p (succ m) ≡ succ m
  claim₁ f r = cong (case _ _) r 


Lemma[succ-0̄-1̄] : (p : ₂ℕ → ℕ) → (n : ℕ) →
        (∀(α β : ₂ℕ) → α ≣ succ n ≣ β → p α ≡ p β) →
        (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) →
         ∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β
Lemma[succ-0̄-1̄] p n pr g α β awn = trans eqα (sym eqβ)
 where
  s : ₂Fin n
  s = take n α
  eq : p (cons s 0̄) ≡ p (cons s 1̄)
  eq = g s
  eq0̄ : ∀{k : ℕ} → ∀(t : ₂Fin k) → cons t 0̄ k ≡ ₀
  eq0̄ ⟨⟩ = refl
  eq0̄ (b ∷ s) = eq0̄ s
  eq1̄ : ∀{k : ℕ} → ∀(t : ₂Fin k) → cons t 1̄ k ≡ ₁
  eq1̄ ⟨⟩ = refl
  eq1̄ (b ∷ s) = eq1̄ s
  subclaim₀ : α ≣ succ n ≣ cons s 0̄ → p α ≡ p (cons s 0̄)
  subclaim₀ = pr α (cons s 0̄)
  subclaim₁ : α ≣ succ n ≣ cons s 1̄ → p α ≡ p (cons s 0̄)
  subclaim₁ aw' = trans (pr α (cons s 1̄) aw') (sym eq)
  subclaim₂ : (α ≣ succ n ≣ cons s 0̄) ∨ (α ≣ succ n ≣ cons s 1̄)
  subclaim₂ = cases sclaim₀ sclaim₁ (₂-discrete (α n))
   where
    sclaim₀ : α n ≡ ₀ → α ≣ succ n ≣ cons s 0̄
    sclaim₀ αn₀ = Lemma[≣_≣-cons] n α (cons s 0̄)
                    (Lemma[cons-take-≣_≣] n α 0̄) (trans αn₀ (sym (eq0̄ s)))
    sclaim₁ : α n ≡ ₁ → α ≣ succ n ≣ cons s 1̄
    sclaim₁ αn₁ = Lemma[≣_≣-cons] n α (cons s 1̄)
                    (Lemma[cons-take-≣_≣] n α 1̄) (trans αn₁ (sym (eq1̄ s)))
  eqα : p α ≡ p (cons s 0̄)
  eqα = case subclaim₀ subclaim₁ subclaim₂
  subclaim₃ : β ≣ succ n ≣ cons s 0̄ → p β ≡ p (cons s 0̄)
  subclaim₃ = pr β (cons s 0̄)
  subclaim₄ : β ≣ succ n ≣ cons s 1̄ → p β ≡ p (cons s 0̄)
  subclaim₄ aw' = trans (pr β (cons s 1̄) aw') (sym eq)
  subclaim₅ : (β ≣ succ n ≣ cons s 0̄) ∨ (β ≣ succ n ≣ cons s 1̄)
  subclaim₅ = subst {₂Fin n} {λ s → (β ≣ succ n ≣ cons s 0̄) ∨ (β ≣ succ n ≣ cons s 1̄)}
                    (sym (Lemma[≣_≣-take] n α β awn)) sclaim₂
   where
    s' : ₂Fin n
    s' = take n β
    sclaim₀ : β n ≡ ₀ → β ≣ succ n ≣ cons s' 0̄
    sclaim₀ βn₀ = Lemma[≣_≣-cons] n β (cons s' 0̄)
                    (Lemma[cons-take-≣_≣] n β 0̄) (trans βn₀ (sym (eq0̄ s')))
    sclaim₁ : β n ≡ ₁ → β ≣ succ n ≣ cons s' 1̄
    sclaim₁ βn₁ = Lemma[≣_≣-cons] n β (cons s' 1̄)
                    (Lemma[cons-take-≣_≣] n β 1̄) (trans βn₁ (sym (eq1̄ s')))
    sclaim₂ : (β ≣ succ n ≣ cons s' 0̄) ∨ (β ≣ succ n ≣ cons s' 1̄)
    sclaim₂ = cases sclaim₀ sclaim₁ (₂-discrete (β n))
  eqβ : p β ≡ p (cons s 0̄)
  eqβ = case subclaim₃ subclaim₄ subclaim₅


Lemma[LM-modulus] : ∀(p : ₂ℕ → ℕ) →
      (n : ℕ) → (∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β) →
      ∀(α β : ₂ℕ) → α ≣ LM p n ≣ β → p α ≡ p β
Lemma[LM-modulus] p 0        pr α β aw = pr α β aw
Lemma[LM-modulus] p (succ n) pr α β aw = case claim₀ claim₁ (Lemma[₂Fin-decidability] P claim n)
 where
  P : (m : ℕ) → ₂Fin m → Set
  P m s = p (cons s 0̄) ≡ p (cons s 1̄)
  claim : ∀(m : ℕ) → ∀(s : ₂Fin m) → decidable (P m s)
  claim m s = ℕ-discrete (p (cons s 0̄)) (p (cons s 1̄))
  claim₀ : (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) → p α ≡ p β
  claim₀ g = Lemma[LM-modulus] p n pr' α β aw'
   where
    fact : LM p (succ n) ≡ LM p n
    fact = Lemma[LM]₀ p n g
    aw' : α ≣ LM p n ≣ β
    aw' = subst {ℕ} {λ k → α ≣ k ≣ β} fact aw
    pr' : ∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β
    pr' = Lemma[succ-0̄-1̄] p n pr g
  claim₁ : ¬ (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) → p α ≡ p β
  claim₁ h = pr α β aw'
   where
    fact : LM p (succ n) ≡ succ n
    fact = Lemma[LM]₁ p n h
    aw' : α ≣ succ n ≣ β
    aw' = subst {ℕ} {λ k → α ≣ k ≣ β} fact aw


Lemma[LM-E-map] : ∀(p q : ₂ℕ → ℕ) → (∀(α : ₂ℕ) → p α ≡ q α) →
                   ∀(n : ℕ) → LM p n ≡ LM q n
Lemma[LM-E-map] p q epq 0        = refl
Lemma[LM-E-map] p q epq (succ n) = case claim₀ claim₁ (Lemma[decidable-0̄-1̄] p n)
 where
  claim₀ : (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) → LM p (succ n) ≡ LM q (succ n)
  claim₀ hp = trans (trans sclaim₀ (Lemma[LM-E-map] p q epq n)) (sym (sclaim₁))
   where
    hq : ∀(s : ₂Fin n) → q (cons s 0̄) ≡ q (cons s 1̄)
    hq s = trans (trans (sym (epq (cons s 0̄))) (hp s)) (epq (cons s 1̄))
    sclaim₀ : LM p (succ n) ≡ LM p n
    sclaim₀ = Lemma[LM]₀ p n hp
    sclaim₁ : LM q (succ n) ≡ LM q n
    sclaim₁ = Lemma[LM]₀ q n hq
  claim₁ : ¬ (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) → LM p (succ n) ≡ LM q (succ n)
  claim₁ fp = trans sclaim₀ (sym sclaim₁)
   where
    fq : ¬ (∀(s : ₂Fin n) → q (cons s 0̄) ≡ q (cons s 1̄))
    fq f = fp (λ s → trans (trans (epq (cons s 0̄)) (f s)) (sym (epq (cons s 1̄))))
    sclaim₀ : LM p (succ n) ≡ succ n
    sclaim₀ = Lemma[LM]₁ p n fp
    sclaim₁ : LM q (succ n) ≡ succ n
    sclaim₁ = Lemma[LM]₁ q n fq


Lemma[least] : (p : ₂ℕ → ℕ) →
               (n : ℕ) → (∀(α β : ₂ℕ) → α ≣ succ n ≣ β → p α ≡ p β) →
               ¬ (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) →
               (m : ℕ) → (∀(α β : ₂ℕ) → α ≣ succ m ≣ β → p α ≡ p β) →
               ¬ (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) →
               n ≡ m
Lemma[least] p n un nn m um nm = equality-cases (ℕ-discrete n m) claim₀ claim₁
 where
  claim₀ : ∀(h : n ≡ m) → ℕ-discrete n m ≡ in₀ h → n ≡ m
  claim₀ h _ = h
  claim₁ : ∀(f : ¬ (n ≡ m)) → ℕ-discrete n m ≡ in₁ f → n ≡ m
  claim₁ f _ = case sclaim₀ sclaim₁ (Lemma[a≠b→a<b∨b<a] n m f)
   where
    sclaim₀ : n < m → n ≡ m
    sclaim₀ r = ∅-elim (nm ssclaim₁)
     where
      ssclaim₀ : ∀(α β : ₂ℕ) → α ≣ m ≣ β → p α ≡ p β
      ssclaim₀ α β aw = un α β (λ i t → aw i (Lemma[a≤b≤c→a≤c] t r))
      ssclaim₁ : ∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)
      ssclaim₁ s = ssclaim₀ (cons s 0̄) (cons s 1̄) (Lemma[cons-≣_≣] s 0̄ 1̄)
    sclaim₁ : m < n → n ≡ m
    sclaim₁ r = ∅-elim (nn ssclaim₁)
     where
      ssclaim₀ : ∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β
      ssclaim₀ α β aw = um α β (λ i t → aw i (Lemma[a≤b≤c→a≤c] t r))
      ssclaim₁ : ∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)
      ssclaim₁ s = ssclaim₀ (cons s 0̄) (cons s 1̄) (Lemma[cons-≣_≣] s 0̄ 1̄)


Lemma[LM-least] : ∀(p : ₂ℕ → ℕ) →
        (n : ℕ) → (∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β) →
        (m : ℕ) → (∀(α β : ₂ℕ) → α ≣ m ≣ β → p α ≡ p β) →
        LM p n ≡ LM p m
Lemma[LM-least] p 0 prn 0 prm = refl
Lemma[LM-least] p 0 prn (succ m) prm = trans (Lemma[LM-least] p 0 prn m prm') (sym claim₁)
 where
  claim₀ : ∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)
  claim₀ s = prn (cons s 0̄) (cons s 1̄) (λ i → λ ())
  claim₁ : LM p (succ m) ≡ LM p m
  claim₁ = Lemma[LM]₀ p m claim₀
  prm' : ∀(α β : ₂ℕ) → α ≣ m ≣ β → p α ≡ p β
  prm' α β aw = prn α β (λ i → λ ())
Lemma[LM-least] p (succ n) prn 0 prm = trans claim₁ (Lemma[LM-least] p n prn' 0 prm)
 where
  claim₀ : ∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)
  claim₀ s = prm (cons s 0̄) (cons s 1̄) (λ i → λ ())
  claim₁ : LM p (succ n) ≡ LM p n
  claim₁ = Lemma[LM]₀ p n claim₀
  prn' : ∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β
  prn' α β aw = prm α β (λ i → λ ())
Lemma[LM-least] p (succ n) prn (succ m) prm = case claim₀ claim₁ (Lemma[decidable-0̄-1̄] p n)
 where
  claim₀ : (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) → LM p (succ n) ≡ LM p (succ m)
  claim₀ hn = trans eq₀ eq₁
   where
    eq₀ : LM p (succ n) ≡ LM p n
    eq₀ = Lemma[LM]₀ p n hn
    prn' : ∀(α β : ₂ℕ) → α ≣ n ≣ β → p α ≡ p β
    prn' = Lemma[succ-0̄-1̄] p n prn hn
    eq₁ : LM p n ≡ LM p (succ m)
    eq₁ = Lemma[LM-least] p n prn' (succ m) prm
  claim₁ : ¬ (∀(s : ₂Fin n) → p (cons s 0̄) ≡ p (cons s 1̄)) → LM p (succ n) ≡ LM p (succ m)
  claim₁ fn = case sclaim₀ sclaim₁ (Lemma[decidable-0̄-1̄] p m)
   where
    eq₀ : LM p (succ n) ≡ succ n
    eq₀ = Lemma[LM]₁ p n fn
    sclaim₀ : (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) → LM p (succ n) ≡ LM p (succ m)
    sclaim₀ hm = trans eq₂ (sym eq₁)
     where
      eq₁ : LM p (succ m) ≡ LM p m
      eq₁ = Lemma[LM]₀ p m hm
      prm' : ∀(α β : ₂ℕ) → α ≣ m ≣ β → p α ≡ p β
      prm' = Lemma[succ-0̄-1̄] p m prm hm
      eq₂ : LM p (succ n) ≡ LM p m
      eq₂ = Lemma[LM-least] p (succ n) prn m prm'
    sclaim₁ : ¬ (∀(s : ₂Fin m) → p (cons s 0̄) ≡ p (cons s 1̄)) → LM p (succ n) ≡ LM p (succ m)
    sclaim₁ fm = trans (trans eq₀ eq₂) (sym eq₁)
     where
      eq₁ : LM p (succ m) ≡ succ m
      eq₁ = Lemma[LM]₁ p m fm
      eq₂ : succ n ≡ succ m
      eq₂ = cong {ℕ} {ℕ} succ (Lemma[least] p n prn fn m prm fm)

\end{code}
