Chuangjie Xu, 2012

\begin{code}

module Continuous-combinator where

open import Mini-library hiding (if ; rec) renaming (case to Case)
open import ConsHeadTail
open import Uniform-continuity
open import Setoid
open import Space
open import Space-exponential
open import Space-product
open import Space-coproduct
open import Space-discrete


-- K combinator with its continuity

continuous-k : {X Y : Space} →
               Σ \(E-k : E-map (U X) (U (Y ⇒ X))) → continuous {X} {Y ⇒ X} E-k
continuous-k {X} {Y} = E-k , cts
 where
  _~_ : Ũ (U X) → Ũ (U X) → Set
  _~_ = E (U X)
  _≋_ : Ũ (U (Y ⇒ X)) → Ũ (U (Y ⇒ X)) → Set
  _≋_ = E (U (Y ⇒ X))
  E-k : E-map (U X) (U (Y ⇒ X))
  E-k = k , ek
   where
    k : Ũ (U X) → Ũ (U (Y ⇒ X))
    k x = f , λ q qQ → cond₀ X p cp
     where
      f : E-map (U Y) (U X)
      f = (λ y → x) , (λ y y' e → Refl (U X) x)
      p : E-map-₂ℕ (U X)
      p = (λ α → x) , (λ α β e → Refl (U X) x)
      cp : constant {E₂ℕ} {U X} p
      cp α β = Refl (U X) x
    ek : ∀(x x' : Ũ (U X)) → x ~ x' → k x ≋ k x'
    ek x x' e y = e
  cts : continuous {X} {Y ⇒ X} E-k
  cts p pP q qQ t uc = goal -- by the presheaf condition
   where
    map₀ : E-map-₂ℕ (U X)
    map₀ = ⟨ U X ⟩ p ◎ t
    map₁ : E-map-₂ℕ (U X)
    map₁ = exp Y X (⟨ U X ∣ U (Y ⇒ X) ⟩ E-k ◎ p) t q
    claim₀ : ∀(α : ₂ℕ) → π₀ map₀ α ~ π₀ map₁ α
    claim₀ α = Refl (U X) (π₀ p (π₀ t α))
    claim₁ : map₀ ∈ Probe X
    claim₁ = cond₁ X t uc p pP
    goal : map₁ ∈ Probe X
    goal = cond₃ X map₀ map₁ claim₀ claim₁


-- S combinator with its continuity

continuous-s : {X Y Z : Space} →
               Σ \(E-s : E-map (U (X ⇒ Y ⇒ Z)) (U ((X ⇒ Y) ⇒ X ⇒ Z))) →
                   continuous {X ⇒ Y ⇒ Z} {(X ⇒ Y) ⇒ X ⇒ Z} E-s
continuous-s {X} {Y} {Z} = (s , es) , cts
 where
  s : Ũ (U (X ⇒ Y ⇒ Z)) → Ũ (U ((X ⇒ Y) ⇒ X ⇒ Z))
  s ((f , ef) , ctf) = (s₀ , es₀) , cts₀
   where
    s₀ : Ũ (U (X ⇒ Y)) → Ũ (U (X ⇒ Z))
    s₀ ((g , eg) , ctg) = (s₁ , es₁) , cts₁
     where
      s₁ : Ũ (U X) → Ũ (U Z)
      s₁ x = π₀ (π₀ (f x)) (g x)
      es₁ : ∀(x x' : Ũ (U X)) → E (U X) x x' → E (U Z) (s₁ x) (s₁ x')
      es₁ x x' exx = Trans (U Z) (π₀ (π₀ (f x)) (g x))
                                (π₀ (π₀ (f x')) (g x))
                                (π₀ (π₀ (f x')) (g x'))
                                claim₀ claim₁
       where
        claim₀ : E (U Z) (π₀ (π₀ (f x)) (g x)) (π₀ (π₀ (f x')) (g x))
        claim₀ = ef x x' exx (g x)
        claim₁ : E (U Z) (π₀ (π₀ (f x')) (g x)) (π₀ (π₀ (f x')) (g x'))
        claim₁ = π₁ (π₀ (f x')) (g x) (g x') (eg x x' exx)
      cts₁ : continuous {X} {Z} (s₁ , es₁)
      cts₁ p pX = goal -- by the continuity of f
       where
        q : E-map-₂ℕ (U Y)
        q = ⟨ U X ∣ U Y ⟩ (g , eg) ◎ p
        claim₀ : q ∈ Probe Y
        claim₀ = ctg p pX
        map₀ : E-map-₂ℕ (U Z)
        map₀ = exp Y Z (⟨ U X ∣ U (Y ⇒ Z) ⟩ (f , ef) ◎ p) (E-id {E₂ℕ}) q
        map₁ : E-map-₂ℕ (U Z)
        map₁ = ⟨ U X ∣ U Z ⟩ (s₁ , es₁) ◎ p
        claim₁ : ∀(α : ₂ℕ) → E (U Z) (π₀ map₀ α) (π₀ map₁ α)
        claim₁ α = Refl (U Z) (π₀ (π₀ (f (π₀ p α))) (g (π₀ p α)))
        claim₂ : map₀ ∈ Probe Z
        claim₂ = ctf p pX q claim₀ (E-id {E₂ℕ}) Lemma[id-UC]
        goal : map₁ ∈ Probe Z
        goal = cond₃ Z map₀ map₁ claim₁ claim₂
    es₀ : ∀(g g' : Ũ (U (X ⇒ Y))) → E (U (X ⇒ Y)) g g' → E (U (X ⇒ Z)) (s₀ g) (s₀ g')
    es₀ g g' egg x = π₁ (π₀ (f x)) (π₀ (π₀ g) x) (π₀ (π₀ g') x) (egg x)
                     -- by the extensionality of (f x)
    cts₀ : continuous {X ⇒ Y} {X ⇒ Z} (s₀ , es₀)
    cts₀ p pXY q qX t uc = goal -- by the continuity of f
     where
      r : E-map-₂ℕ (U Y)
      r = exp X Y p t q
      claim₀ : r ∈ Probe Y
      claim₀ = pXY q qX t uc
      map₀ : E-map-₂ℕ (U Z)
      map₀ = exp Y Z (⟨ U X ∣ U (Y ⇒ Z) ⟩ (f , ef) ◎ q) (E-id {E₂ℕ}) r
      map₁ : E-map-₂ℕ (U Z)
      map₁ = exp X Z (⟨ U (X ⇒ Y) ∣ U (X ⇒ Z) ⟩ (s₀ , es₀) ◎ p) t q
      claim₁ : ∀(α : ₂ℕ) → E (U Z) (π₀ map₀ α) (π₀ map₁ α)
      claim₁ α = Refl (U Z) (π₀ (π₀ (f (π₀ q α))) (π₀ (π₀ (π₀ p (π₀ t α))) (π₀ q α)))
      claim₂ : map₀ ∈ Probe Z
      claim₂ = ctf q qX r claim₀ (E-id {E₂ℕ}) Lemma[id-UC]
      goal : map₁ ∈ Probe Z
      goal = cond₃ Z map₀ map₁ claim₁ claim₂
  es : ∀(f f' : Ũ (U (X ⇒ Y ⇒ Z))) → E (U (X ⇒ Y ⇒ Z)) f f' →
        E (U ((X ⇒ Y) ⇒ X ⇒ Z)) (s f) (s f')
  es f f' eff g x = eff x (π₀ (π₀ g) x)
  cts : continuous {X ⇒ Y ⇒ Z} {(X ⇒ Y) ⇒ X ⇒ Z} (s , es)
  cts p pXYZ q qXY t uct r rX u ucu = goal
   where
    claim₀ : exp X Y q u r ∈ Probe Y
    claim₀ = qXY r rX u ucu
    claim₁ : exp X (Y ⇒ Z) p (t ◎ u) r ∈ Probe (Y ⇒ Z)
    claim₁ = pXYZ r rX (t ◎ u) (Lemma[◎-UC] t uct u ucu)
    map₀ : E-map-₂ℕ (U Z)
    map₀ = exp Y Z (exp X (Y ⇒ Z) p (t ◎ u) r) (E-id {E₂ℕ}) (exp X Y q u r)
    claim₂ : map₀ ∈ Probe Z
    claim₂ = claim₁ (exp X Y q u r) claim₀ (E-id {E₂ℕ}) Lemma[id-UC]
    sp : E-map-₂ℕ (U ((X ⇒ Y) ⇒ X ⇒ Z))
    sp = ⟨ U (X ⇒ Y ⇒ Z) ∣ U ((X ⇒ Y) ⇒ X ⇒ Z) ⟩ (s , es) ◎ p
    map₁ : E-map-₂ℕ (U Z)
    map₁ = exp X Z (exp (X ⇒ Y) (X ⇒ Z) sp t q) u r
    claim₃ : ∀(α : ₂ℕ) → E (U Z) (π₀ map₀ α) (π₀ map₁ α)
    claim₃ α = Refl (U Z) (π₀ (π₀ (π₀ (π₀ (π₀ p (π₀ t (π₀ u α)))) (π₀ r α)))
                           (π₀ (π₀ (π₀ q (π₀ u α))) (π₀ r α)))
    goal : map₁ ∈ Probe Z
    goal = cond₃ Z map₀ map₁ claim₃ claim₂


-- Case function with its continuity

continuous-if : {X : Space} →
                Σ \(E-if : E-map (U X) (U (X ⇒ ₂Space ⇒ X))) →
                    continuous {X} {X ⇒ ₂Space ⇒ X} E-if
continuous-if {X} = (if , eif) , cts
 where
  if : Ũ (U X) → Ũ (U (X ⇒ ₂Space ⇒ X))
  if x = (if-x , eif-x) , ctsif-x
   where
    if-x : Ũ (U X) → Ũ (U (₂Space ⇒ X))
    if-x x' = (if-x-x' , eif-x-x') , ctsif-x-x'
     where
      if-x-x' : ₂ → Ũ (U X)
      if-x-x' ₀ = x
      if-x-x' ₁ = x'
      eif-x-x' : ∀(b b' : ₂) → b ≡ b' → E (U X) (if-x-x' b) (if-x-x' b')
      eif-x-x' b .b refl = Refl (U X) (if-x-x' b)
      ctsif-x-x' : continuous {₂Space} {X} (if-x-x' , eif-x-x')
      ctsif-x-x' = Lemma[discreteness] {E₂} {X} (if-x-x' , eif-x-x')
    eif-x : ∀(a a' : Ũ (U X)) → E (U X) a a' → E (U (₂Space ⇒ X)) (if-x a) (if-x a')
    eif-x a a' eaa ₀ = Refl (U X) x
    eif-x a a' eaa ₁ = eaa
    ctsif-x : continuous {X} {₂Space ⇒ X} (if-x , eif-x)
    ctsif-x p pX q q2 t uc = cond₂ X ifptq (n , prf)
     where
      ifptq : E-map-₂ℕ (U X)
      ifptq = exp ₂Space X (⟨ U X ∣ U (₂Space ⇒ X) ⟩ (if-x , eif-x ) ◎ p) t q
      n : ℕ
      n = ∃-witness q2
      prf : ∀(s : ₂Fin n) → ⟨ U X ⟩ ifptq ◎ (E-cons s) ∈ Probe X
      prf s = cond₃ X (map (π₀ q (cons s 0̄))) (⟨ U X ⟩ ifptq ◎ (E-cons s)) claim₁ claim₃
       where
        map : ₂ → E-map-₂ℕ (U X)
        map b = f , ef
         where
          f : ₂ℕ → Ũ (U X)
          f α = π₀ (π₀ (if-x (π₀ p (π₀ t (cons s α))))) b
          ef : ∀(α β : ₂ℕ) → α ≣ β → E (U X) (f α) (f β)
          ef α β e = c₃ b -- by the extensionality of if-x, p, t and cons
           where
            c₀ : cons s α ≣ cons s β
            c₀ = Lemma[cons-E-map] s α β e
            c₁ : π₀ t (cons s α) ≣ π₀ t (cons s β)
            c₁ = π₁ t (cons s α) (cons s β) c₀
            c₂ : E (U X) (π₀ p (π₀ t (cons s α))) (π₀ p (π₀ t (cons s β)))
            c₂ = π₁ p (π₀ t (cons s α)) (π₀ t (cons s β)) c₁
            c₃ : E (U (₂Space ⇒ X)) (if-x (π₀ p (π₀ t (cons s α))))
                                    (if-x (π₀ p (π₀ t (cons s β))))
            c₃ = eif-x (π₀ p (π₀ t (cons s α))) (π₀ p (π₀ t (cons s β))) c₂
        claim₀ : ∀(α : ₂ℕ) → π₀ q (cons s 0̄) ≡ π₀ q (cons s α)
        claim₀ α = ∃-elim q2 (cons s 0̄) (cons s α) (Lemma[cons-≣_≣] s 0̄ α)
        claim₁ : ∀(α : ₂ℕ) → E (U X) (π₀ (map (π₀ q (cons s 0̄))) α)
                                     (π₀ (⟨ U X ⟩ ifptq ◎ (E-cons s)) α)
        claim₁ α = π₁ (π₀ (if-x (π₀ p (π₀ t (cons s α))))) (π₀ q (cons s 0̄))
                                                           (π₀ q (cons s α)) (claim₀ α)
        claim₂ : ∀(b : ₂) → map b ∈ Probe X
        claim₂ ₀ = cond₀ X ((λ α → x) , (λ α β e → Refl (U X) x)) (λ α β → Refl (U X) x)
                -- map ₀ = λ α → x
        claim₂ ₁ = cond₁ X (t ◎ (E-cons s)) (Lemma[◎-UC] t uc (E-cons s) (Lemma[E-cons-UC] s)) p pX
                -- map ₁ = p ∘ t ∘ (cons s)
        claim₃ : map (π₀ q (cons s 0̄)) ∈ Probe X
        claim₃ = claim₂ (π₀ q (cons s 0̄))
  eif : ∀(x x' : Ũ (U X)) → E (U X) x x' → E (U (X ⇒ ₂Space ⇒ X)) (if x) (if x')
  eif x x' exx a ₀ = exx
  eif x x' exx a ₁ = Refl (U X) a
  cts : continuous {X} {X ⇒ ₂Space ⇒ X} (if , eif)
  cts p pX q qX t uct r r2 u ucu = cond₂ X ifptqur (n , prf)
   where
    ifptqur : E-map-₂ℕ (U X)
    ifptqur = exp ₂Space X (exp X (₂Space ⇒ X) (⟨ U X ∣ U (X ⇒ ₂Space ⇒ X) ⟩ (if , eif) ◎ p) t q) u r
    n : ℕ
    n = ∃-witness r2
    prf : ∀(s : ₂Fin n) → ⟨ U X ⟩ ifptqur ◎ (E-cons s) ∈ Probe X
    prf s = cond₃ X (map (π₀ r (cons s 0̄))) (⟨ U X ⟩ ifptqur ◎ (E-cons s)) claim₁ claim₃
     where
      map : ₂ → E-map-₂ℕ (U X)
      map b = f , ef
       where
        f : ₂ℕ → Ũ (U X)
        f α = π₀ (π₀ (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))) b
        ef : ∀(α β : ₂ℕ) → α ≣ β → E (U X) (f α) (f β)
        ef α β e = c₈ b -- by the extensionality of if, p, q, t, u and cons
         where
          c₀ : cons s α ≣ cons s β
          c₀ = Lemma[cons-E-map] s α β e
          c₁ : π₀ u (cons s α) ≣ π₀ u (cons s β)
          c₁ = π₁ u (cons s α) (cons s β) c₀
          c₂ : π₀ t (π₀ u (cons s α)) ≣ π₀ t (π₀ u (cons s β))
          c₂ = π₁ t (π₀ u (cons s α)) (π₀ u (cons s β)) c₁
          c₃ : E (U X) (π₀ p (π₀ t (π₀ u (cons s α))))
                       (π₀ p (π₀ t (π₀ u (cons s β))))
          c₃ = π₁ p (π₀ t (π₀ u (cons s α))) (π₀ t (π₀ u (cons s β))) c₂
          c₄ : E (U (X ⇒ ₂Space ⇒ X)) (if (π₀ p (π₀ t (π₀ u (cons s α)))))
                                      (if (π₀ p (π₀ t (π₀ u (cons s β)))))
          c₄ = eif (π₀ p (π₀ t (π₀ u (cons s α)))) (π₀ p (π₀ t (π₀ u (cons s β)))) c₃
          c₅ : E (U X) (π₀ q (π₀ u (cons s α))) (π₀ q (π₀ u (cons s β)))
          c₅ = π₁ q (π₀ u (cons s α)) (π₀ u (cons s β)) c₁
          c₆ : E (U (₂Space ⇒ X)) (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))
                                  (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α))))
          c₆ = c₄ (π₀ q (π₀ u (cons s α)))
          c₇ : E (U (₂Space ⇒ X)) (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α))))
                                  (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s β))))
          c₇ = π₁ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α)))
                                                            (π₀ q (π₀ u (cons s β))) c₅
          c₈ : E (U (₂Space ⇒ X)) (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))
                                  (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s β))))
          c₈ = Trans (U (₂Space ⇒ X)) (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))
                                      (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α))))
                                      (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s β))))
                                      c₆ c₇
      claim₀ : ∀(α : ₂ℕ) → π₀ r (cons s 0̄) ≡ π₀ r (cons s α)
      claim₀ α = ∃-elim r2 (cons s 0̄) (cons s α) (Lemma[cons-≣_≣] s 0̄ α)
      claim₁ : ∀(α : ₂ℕ) → E (U X) (π₀ (map (π₀ r (cons s 0̄))) α)
                                   (π₀ (⟨ U X ⟩ ifptqur ◎ (E-cons s)) α)
      claim₁ α = π₁ (π₀ (π₀ (π₀ (if (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α)))))
                    (π₀ r (cons s 0̄)) (π₀ r (cons s α)) (claim₀ α)
      ucus : uniformly-continuous-₂ℕ (u ◎ (E-cons s))
      ucus = Lemma[◎-UC] u ucu (E-cons s) (Lemma[E-cons-UC] s)
      uctus : uniformly-continuous-₂ℕ (t ◎ (u ◎ (E-cons s)))
      uctus = Lemma[◎-UC] t uct (u ◎ (E-cons s)) ucus
      claim₂ : ∀(b : ₂) → map b ∈ Probe X
      claim₂ ₀ = cond₃ X map' (map ₀) c₀ c₁
       where
        map' : E-map-₂ℕ (U X)
        map' = ⟨ U X ⟩ p ◎ (t ◎ (u ◎ (E-cons s)))
        c₀ : ∀(α : ₂ℕ) → E (U X) (π₀ map' α) (π₀ (map ₀) α)
        c₀ α = Refl (U X) (π₀ p (π₀ t (π₀ u (cons s α))))
        c₁ : map' ∈ Probe X
        c₁ = cond₁ X (t ◎ (u ◎ (E-cons s))) uctus p pX
      claim₂ ₁ = cond₃ X map' (map ₁) c₀ c₁
       where
        map' : E-map-₂ℕ (U X)
        map' = ⟨ U X ⟩ q ◎ (u ◎ (E-cons s))
        c₀ : ∀(α : ₂ℕ) → E (U X) (π₀ map' α) (π₀ (map ₁) α)
        c₀ α = Refl (U X) (π₀ q (π₀ u (cons s α)))
        c₁ : map' ∈ Probe X
        c₁ = cond₁ X (u ◎ (E-cons s)) ucus q qX
      claim₃ : map (π₀ r (cons s 0̄)) ∈ Probe X
      claim₃ = claim₂ (π₀ r (cons s 0̄))


-- Successor with its continuity

continuous-succ : Σ \(E-succ : E-map Eℕ Eℕ) → continuous {ℕSpace} {ℕSpace} E-succ
continuous-succ = E-succ , Lemma[discreteness] {Eℕ} {ℕSpace} E-succ


-- Rec function with its continuity

continuous-rec : {X : Space} →
                 Σ \(E-rec : E-map (U (X ⇒ X)) (U (X ⇒ ℕSpace ⇒ X))) →
                     continuous {X ⇒ X} {X ⇒ ℕSpace ⇒ X} E-rec
continuous-rec {X} = (rec , erec) , cts
 where
  rec : Ũ (U (X ⇒ X)) → Ũ (U (X ⇒ ℕSpace ⇒ X))
  rec ((f , ef) , ctsf) = (rec-f , erec-f) , ctsrec-f
   where
    rec-f : Ũ (U X) → Ũ (U (ℕSpace ⇒ X))
    rec-f x = (rec-f-x , erec-f-x) , ctsrec-f-x
     where
      rec-f-x : ℕ → Ũ (U X)
      rec-f-x 0        = x
      rec-f-x (succ n) = f (rec-f-x n)
      erec-f-x : ∀(n n' : ℕ) → n ≡ n' → E (U X) (rec-f-x n) (rec-f-x n')
      erec-f-x n .n refl = Refl (U X) (rec-f-x n)
      ctsrec-f-x : continuous {ℕSpace} {X} (rec-f-x , erec-f-x)
      ctsrec-f-x = Lemma[discreteness] {Eℕ} {X} (rec-f-x , erec-f-x)
    erec-f : ∀(x x' : Ũ (U X)) → E (U X) x x' → E (U (ℕSpace ⇒ X)) (rec-f x) (rec-f x')
    erec-f x x' exx 0        = exx
    erec-f x x' exx (succ n) = ef (π₀ (π₀ (rec-f x)) n)
                                  (π₀ (π₀ (rec-f x')) n) (erec-f x x' exx n)
    ctsrec-f : continuous {X} {ℕSpace ⇒ X} (rec-f , erec-f)
    ctsrec-f p pX q qN t uct = cond₂ X recptq (n , prf)
     where
      recptq : E-map-₂ℕ (U X)
      recptq = exp ℕSpace X (⟨ U X ∣ U (ℕSpace ⇒ X) ⟩ (rec-f , erec-f) ◎ p) t q
      n : ℕ
      n = ∃-witness qN
      prf : ∀(s : ₂Fin n) → ⟨ U X ⟩ recptq ◎ (E-cons s) ∈ Probe X
      prf s = cond₃ X (map (π₀ q (cons s 0̄))) (⟨ U X ⟩ recptq ◎ (E-cons s)) claim₁ claim₃
       where
        map : ℕ → E-map-₂ℕ (U X)
        map n = g , eg
         where
          g : ₂ℕ → Ũ (U X)
          g α = π₀ (π₀ (rec-f (π₀ p (π₀ t (cons s α))))) n
          eg : ∀(α β : ₂ℕ) → α ≣ β → E (U X) (g α) (g β)
          eg α β e = c₃ n
           where
            c₀ : cons s α ≣ cons s β
            c₀ = Lemma[cons-E-map] s α β e
            c₁ : π₀ t (cons s α) ≣ π₀ t (cons s β)
            c₁ = π₁ t (cons s α) (cons s β) c₀
            c₂ : E (U X) (π₀ p (π₀ t (cons s α))) (π₀ p (π₀ t (cons s β)))
            c₂ = π₁ p (π₀ t (cons s α)) (π₀ t (cons s β)) c₁
            c₃ : E (U (ℕSpace ⇒ X)) (rec-f (π₀ p (π₀ t (cons s α))))
                                    (rec-f (π₀ p (π₀ t (cons s β))))
            c₃ = erec-f (π₀ p (π₀ t (cons s α))) (π₀ p (π₀ t (cons s β))) c₂
        claim₀ : ∀(α : ₂ℕ) → π₀ q (cons s 0̄) ≡ π₀ q (cons s α)
        claim₀ α = ∃-elim qN (cons s 0̄) (cons s α) (Lemma[cons-≣_≣] s 0̄ α)
        claim₁ : ∀(α : ₂ℕ) → E (U X) (π₀ (map (π₀ q (cons s 0̄))) α)
                                     (π₀ (⟨ U X ⟩ recptq ◎ (E-cons s)) α)
        claim₁ α = π₁ (π₀ (rec-f (π₀ p (π₀ t (cons s α))))) (π₀ q (cons s 0̄))
                                                            (π₀ q (cons s α)) (claim₀ α)
        ucts : uniformly-continuous-₂ℕ (t ◎ (E-cons s))
        ucts = Lemma[◎-UC] t uct (E-cons s) (Lemma[E-cons-UC] s)
        claim₂ : ∀(n : ℕ) → map n ∈ Probe X
        claim₂ 0        = cond₁ X (t ◎ (E-cons s)) ucts p pX
        claim₂ (succ n) = cond₃ X map' (map (succ n)) c₀ c₁
         where
          IH : map n ∈ Probe X
          IH = claim₂ n
          map' : E-map-₂ℕ (U X)
          map' = ⟨ U X ∣ U X ⟩ (f , ef) ◎ (map n)
          c₀ : ∀(α : ₂ℕ) → E (U X) (π₀ map' α) (π₀ (map (succ n)) α)
          c₀ α = Refl (U X) (f (π₀ (map n) α))
          c₁ : map' ∈ Probe X
          c₁ = ctsf (map n) IH
        claim₃ : map (π₀ q (cons s 0̄)) ∈ Probe X
        claim₃ = claim₂ (π₀ q (cons s 0̄))
  erec : ∀(f f' : Ũ (U (X ⇒ X))) → E (U (X ⇒ X)) f f' →
          E (U (X ⇒ ℕSpace ⇒ X)) (rec f) (rec f')
  erec f f' eff x 0        = Refl (U X) x
  erec f f' eff x (succ n) = Trans (U X) (π₀ (π₀ f) (π₀ (π₀ (π₀ (π₀ (rec f)) x)) n))
                                         (π₀ (π₀ f) (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n))
                                         (π₀ (π₀ f') (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n))
                                         claim₀ claim₁
   where
    IH : E (U X) (π₀ (π₀ (π₀ (π₀ (rec f)) x)) n)
                 (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n)
    IH = erec f f' eff x n
    claim₀ : E (U X) (π₀ (π₀ f) (π₀ (π₀ (π₀ (π₀ (rec f)) x)) n))
                     (π₀ (π₀ f) (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n))
    claim₀ = π₁ (π₀ f) (π₀ (π₀ (π₀ (π₀ (rec f)) x)) n)
                       (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n) IH
    claim₁ : E (U X) (π₀ (π₀ f) (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n))
                     (π₀ (π₀ f') (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n))
    claim₁ = eff (π₀ (π₀ (π₀ (π₀ (rec f')) x)) n)
  cts : continuous {X ⇒ X} {X ⇒ ℕSpace ⇒ X} (rec , erec)
  cts p pXX q qX t uct r rN u ucu = cond₂ X recptqur (n , prf)
   where
    recptq : E-map-₂ℕ (U (ℕSpace ⇒ X))
    recptq = exp X (ℕSpace ⇒ X) (⟨ U (X ⇒ X) ∣ U (X ⇒ ℕSpace ⇒ X) ⟩ (rec , erec) ◎ p) t q
    recptqur : E-map-₂ℕ (U X)
    recptqur = exp ℕSpace X recptq u r
    n : ℕ
    n = ∃-witness rN
    prf : ∀(s : ₂Fin n) → ⟨ U X ⟩ recptqur ◎ (E-cons s) ∈ Probe X
    prf s = cond₃ X (map (π₀ r (cons s 0̄))) (⟨ U X ⟩ recptqur ◎ (E-cons s)) claim₁ claim₃
     where
      map : ℕ → E-map-₂ℕ (U X)
      map n = g , eg
       where
        g : ₂ℕ → Ũ (U X)
        g α = π₀ (π₀ (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))) n
        eg : ∀(α β : ₂ℕ) → α ≣ β → E (U X) (g α) (g β)
        eg α β e = c₈ n
         where
          c₀ : cons s α ≣ cons s β
          c₀ = Lemma[cons-E-map] s α β e
          c₁ : π₀ u (cons s α) ≣ π₀ u (cons s β)
          c₁ = π₁ u (cons s α) (cons s β) c₀
          c₂ : π₀ t (π₀ u (cons s α)) ≣ π₀ t (π₀ u (cons s β))
          c₂ = π₁ t (π₀ u (cons s α)) (π₀ u (cons s β)) c₁
          c₃ : E (U (X ⇒ X)) (π₀ p (π₀ t (π₀ u (cons s α))))
                             (π₀ p (π₀ t (π₀ u (cons s β))))
          c₃ = π₁ p (π₀ t (π₀ u (cons s α))) (π₀ t (π₀ u (cons s β))) c₂
          c₄ : E (U (X ⇒ ℕSpace ⇒ X)) (rec (π₀ p (π₀ t (π₀ u (cons s α)))))
                                      (rec (π₀ p (π₀ t (π₀ u (cons s β)))))
          c₄ = erec (π₀ p (π₀ t (π₀ u (cons s α)))) (π₀ p (π₀ t (π₀ u (cons s β)))) c₃
          c₅ : E (U X) (π₀ q (π₀ u (cons s α))) (π₀ q (π₀ u (cons s β)))
          c₅ = π₁ q (π₀ u (cons s α)) (π₀ u (cons s β)) c₁
          c₆ : E (U (ℕSpace ⇒ X)) (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))
                                  (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α))))
          c₆ = c₄ (π₀ q (π₀ u (cons s α)))
          c₇ : E (U (ℕSpace ⇒ X)) (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α))))
                                  (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s β))))
          c₇ = π₁ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α)))
                                                             (π₀ q (π₀ u (cons s β))) c₅
          c₈ : E (U (ℕSpace ⇒ X)) (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))
                                  (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s β))))
          c₈ = Trans (U (ℕSpace ⇒ X)) (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α))))
                                      (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s α))))
                                      (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s β)))))) (π₀ q (π₀ u (cons s β))))
                                      c₆ c₇
      claim₀ : ∀(α : ₂ℕ) → π₀ r (cons s 0̄) ≡ π₀ r (cons s α)
      claim₀ α = ∃-elim rN (cons s 0̄) (cons s α) (Lemma[cons-≣_≣] s 0̄ α)
      claim₁ : ∀(α : ₂ℕ) → E (U X) (π₀ (map (π₀ r (cons s 0̄))) α)
                                   (π₀ (⟨ U X ⟩ recptqur ◎ (E-cons s)) α)
      claim₁ α = π₁ (π₀ (π₀ (π₀ (rec (π₀ p (π₀ t (π₀ u (cons s α)))))) (π₀ q (π₀ u (cons s α)))))
                    (π₀ r (cons s 0̄)) (π₀ r (cons s α)) (claim₀ α)
      ucus : uniformly-continuous-₂ℕ (u ◎ (E-cons s))
      ucus = Lemma[◎-UC] u ucu (E-cons s) (Lemma[E-cons-UC] s)
      uctus : uniformly-continuous-₂ℕ (t ◎ (u ◎ (E-cons s)))
      uctus = Lemma[◎-UC] t uct (u ◎ (E-cons s)) ucus
      claim₂ : ∀(n : ℕ) → map n ∈ Probe X
      claim₂ 0 = cond₃ X map' (map 0) c₀ c₁
       where
        map' : E-map-₂ℕ (U X)
        map' = ⟨ U X ⟩ q ◎ (u ◎ (E-cons s))
        c₀ : ∀(α : ₂ℕ) → E (U X) (π₀ map' α) (π₀ (map 0) α)
        c₀ α = Refl (U X) (π₀ q (π₀ u (cons s α)))
        c₁ : map' ∈ Probe X
        c₁ = cond₁ X (u ◎ (E-cons s)) ucus q qX
      claim₂ (succ n) = cond₃ X map' (map (succ n)) c₀ c₁
       where
        map' : E-map-₂ℕ (U X)
        map' = exp X X p (t ◎ (u ◎ (E-cons s))) (map n)
        c₀ : ∀(α : ₂ℕ) → E (U X) (π₀ map' α) (π₀ (map (succ n)) α)
        c₀ α = Refl (U X) (π₀ (π₀ (π₀ p (π₀ t (π₀ u (cons s α))))) (π₀ (map n) α))
        c₁ : map' ∈ Probe X
        c₁ = pXX (map n) (claim₂ n) (t ◎ (u ◎ (E-cons s))) uctus
      claim₃ : map (π₀ r (cons s 0̄)) ∈ Probe X
      claim₃ = claim₂ (π₀ r (cons s 0̄))



-- Unit function with its continuity

continuous-unit : {X : Space} →
                  Σ \(u : E-map (U X) E⒈) → continuous {X} {⒈Space} u
continuous-unit {X} = E-unit {U X} , (λ p _ → ⋆)


-- Projection functions with their continuity

continuous-π₀ : {X Y : Space} →
                Σ \(E-π₀ : E-map (U (X ⊗ Y)) (U X)) → continuous {X ⊗ Y} {X} E-π₀
continuous-π₀ {X} {Y} = E-π₀ {U X} {U Y} , λ r rR → ∧-elim₀ rR

continuous-π₁ : {X Y : Space} →
                Σ \(E-π₁ : E-map (U (X ⊗ Y)) (U Y)) → continuous {X ⊗ Y} {Y} E-π₁
continuous-π₁ {X} {Y} = E-π₁ {U X} {U Y} , λ r rR → ∧-elim₁ rR
 

-- Injection functions with their continuity

continuous-in₀ : {X Y : Space} →
                 Σ \(i : E-map (U X) (U (X ⊕ Y))) → continuous {X} {X ⊕ Y} i
continuous-in₀ {X} {Y} = ein₀ , cts
 where
  _≋_ = E (U (X ⊕ Y))
  ein₀ : E-map (U X) (U (X ⊕ Y))
  ein₀ = E-in₀ {U X} {U Y}
  cts : ∀(p : E-map-₂ℕ (U X)) → p ∈ Probe X → ⟨ U X ∣ U (X ⊕ Y) ⟩ ein₀ ◎ p ∈ Probe (X ⊕ Y)
  cts p pP = 0 , prf
   where
    in₀p : E-map-₂ℕ (U (X ⊕ Y))
    in₀p = ⟨ U X ∣ U (X ⊕ Y) ⟩ ein₀ ◎ p
    prf : ∀(s : ₂Fin 0) →
            (∃ \(p' : E-map-₂ℕ (U X)) →
                (p' ∈ Probe X) ∧ (∀(α : ₂ℕ) → π₀ in₀p (cons s α) ≋ in₀ (π₀ p' α)))
          ∨ (∃ \(q : E-map-₂ℕ (U Y)) →
                (q ∈ Probe Y) ∧ (∀(α : ₂ℕ) → π₀ in₀p (cons s α) ≋ in₁ (π₀ q α)))
    prf ⟨⟩ = in₀ (p , pP , λ α → Refl (U X) (π₀ p α))

continuous-in₁ : {X Y : Space} →
                 Σ \(i : E-map (U Y) (U (X ⊕ Y))) → continuous {Y} {X ⊕ Y} i
continuous-in₁ {X} {Y} = ein₁ , cts
 where
  _≋_ = E (U (X ⊕ Y))
  ein₁ : E-map (U Y) (U (X ⊕ Y))
  ein₁ = E-in₁ {U X} {U Y}
  cts : ∀(q : E-map-₂ℕ (U Y)) → q ∈ Probe Y → ⟨ U Y ∣ U (X ⊕ Y) ⟩ ein₁ ◎ q ∈ Probe (X ⊕ Y)
  cts q qQ = 0 , prf
   where
    in₁q : E-map-₂ℕ (U (X ⊕ Y))
    in₁q = ⟨ U Y ∣ U (X ⊕ Y) ⟩ ein₁ ◎ q
    prf : ∀(s : ₂Fin 0) →
            (∃ \(p : E-map-₂ℕ (U X)) →
                (p ∈ Probe X) ∧ (∀(α : ₂ℕ) → π₀ in₁q (cons s α) ≋ in₀ (π₀ p α)))
          ∨ (∃ \(q' : E-map-₂ℕ (U Y)) →
                (q' ∈ Probe Y) ∧ (∀(α : ₂ℕ) → π₀ in₁q (cons s α) ≋ in₁ (π₀ q' α)))
    prf ⟨⟩ = in₁ (q , qQ , λ α → Refl (U Y) (π₀ q α))


-- Case function with its continuity

continuous-case : {X Y Z : Space} →
                  Σ \(E-case : E-map (U (X ⇒ Z)) (U ((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z))) →
                      continuous {X ⇒ Z} {(Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z} E-case
continuous-case {X} {Y} {Z} = (case , ecase) , cts
 where
  _~_ = E (U X)
  _≈_ = E (U Y)
  _≋_ = E (U (X ⊕ Y))
  _≅_ = E (U Z)
  case : Ũ (U (X ⇒ Z)) → Ũ (U ((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z))
  case ((f₀ , ef₀) , ctsf₀) = (case-f₀ , ecase-f₀) , ctscase-f₀
   where
    case-f₀ : Ũ (U (Y ⇒ Z)) → Ũ (U ((X ⊕ Y) ⇒ Z))
    case-f₀ ((f₁ , ef₁) , ctsf₁) = (case-f₀-f₁ , ecase-f₀-f₁) , ctscase-f₀-f₁
     where
      case-f₀-f₁ : Ũ (U (X ⊕ Y)) → Ũ (U Z)
      case-f₀-f₁ (in₀ x) = f₀ x
      case-f₀-f₁ (in₁ y) = f₁ y
      ecase-f₀-f₁ : ∀(c c' : Ũ (U (X ⊕ Y))) → c ≋ c' →
                     case-f₀-f₁ c ≅ case-f₀-f₁ c'
      ecase-f₀-f₁ (in₀ x) (in₀ x') exx = ef₀ x x' exx
      ecase-f₀-f₁ (in₀ x) (in₁ y') ()
      ecase-f₀-f₁ (in₁ y) (in₀ x') ()
      ecase-f₀-f₁ (in₁ y) (in₁ y') eyy = ef₁ y y' eyy
      ctscase-f₀-f₁ : continuous {X ⊕ Y} {Z} (case-f₀-f₁ , ecase-f₀-f₁)
      ctscase-f₀-f₁ r rXY = cond₂ Z caser (n , prf)
       where
        caser : E-map-₂ℕ (U Z)
        caser = ⟨ U(X ⊕ Y) ∣ U Z ⟩ (case-f₀-f₁ , ecase-f₀-f₁) ◎ r
        n : ℕ
        n = ∃-witness rXY
        prf : ∀(s : ₂Fin n) → ⟨ U Z ⟩ caser ◎ (E-cons s) ∈ Probe Z
        prf s = Case claim₀ claim₁ (∃-elim rXY s)
         where
          claim₀ : (∃ \(p : E-map-₂ℕ (U X)) →
                       (p ∈ Probe X) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ p α))) →
                   ⟨ U Z ⟩ caser ◎ (E-cons s) ∈ Probe Z
          claim₀ (p , pX , pr) = cond₃ Z fp (⟨ U Z ⟩ caser ◎ (E-cons s)) claim fpZ
           where
            fp : E-map-₂ℕ (U Z)
            fp = (f₀ ∘ (π₀ p)) , (λ α β e → ef₀ (π₀ p α) (π₀ p β) (π₁ p α β e))
            fpZ : fp ∈ Probe Z
            fpZ = ctsf₀ p pX
            claim : ∀(α : ₂ℕ) → π₀ fp α ≅ π₀ (⟨ U Z ⟩ caser ◎ (E-cons s)) α
            claim α = Sym (U Z) (π₀ (⟨ U Z ⟩ caser ◎ (E-cons s)) α) (π₀ fp α)
                                (ecase-f₀-f₁ (π₀ r (cons s α)) (in₀ (π₀ p α)) (pr α))
          claim₁ : (∃ \(q : E-map-₂ℕ (U Y)) →
                       (q ∈ Probe Y) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ q α))) →
                   ⟨ U Z ⟩ caser ◎ (E-cons s) ∈ Probe Z
          claim₁ (q , qY , pr) = cond₃ Z fq (⟨ U Z ⟩ caser ◎ (E-cons s)) claim fqZ
           where
            fq : E-map-₂ℕ (U Z)
            fq = (f₁ ∘ (π₀ q)) , (λ α β e → ef₁ (π₀ q α) (π₀ q β) (π₁ q α β e))
            fqZ : fq ∈ Probe Z
            fqZ = ctsf₁ q qY
            claim : ∀(α : ₂ℕ) → π₀ fq α ≅ π₀ (⟨ U Z ⟩ caser ◎ (E-cons s)) α
            claim α = Sym (U Z) (π₀ (⟨ U Z ⟩ caser ◎ (E-cons s)) α) (π₀ fq α)
                                (ecase-f₀-f₁ (π₀ r (cons s α)) (in₁ (π₀ q α)) (pr α))
    ecase-f₀ : ∀(f₁ f₁' : Ũ (U (Y ⇒ Z))) → E (U (Y ⇒ Z)) f₁ f₁' →
                E (U ((X ⊕ Y) ⇒ Z)) (case-f₀ f₁) (case-f₀ f₁')
    ecase-f₀ f₁ f₁' eff (in₀ x) = Refl (U Z) (f₀ x)
    ecase-f₀ f₁ f₁' eff (in₁ y) = eff y
    ctscase-f₀ : continuous {Y ⇒ Z} {(X ⊕ Y) ⇒ Z} (case-f₀ , ecase-f₀)
    ctscase-f₀ p pYZ q qXY t uct = cond₂ Z caseptq (n , prf)
     where
      caseptq : E-map-₂ℕ (U Z)
      caseptq = exp (X ⊕ Y) Z (⟨ U(Y ⇒ Z) ∣ U((X ⊕ Y) ⇒ Z) ⟩ (case-f₀ , ecase-f₀) ◎ p) t q
      n : ℕ
      n = ∃-witness qXY
      prf : ∀(s : ₂Fin n) → ⟨ U Z ⟩ caseptq ◎ (E-cons s) ∈ Probe Z
      prf s = Case claim₀ claim₁ (∃-elim qXY s)
       where
        claim₀ : (∃ \(pp : E-map-₂ℕ (U X)) →
                     (pp ∈ Probe X) ∧ (∀(α : ₂ℕ) → π₀ q (cons s α) ≋ in₀ (π₀ pp α))) →
                 ⟨ U Z ⟩ caseptq ◎ (E-cons s) ∈ Probe Z
        claim₀ (pp , ppX , pr) = cond₃ Z fpp (⟨ U Z ⟩ caseptq ◎ (E-cons s)) claim fppZ
         where
          fpp : E-map-₂ℕ (U Z)
          fpp = (f₀ ∘ (π₀ pp)) , (λ α β e → ef₀ (π₀ pp α) (π₀ pp β) (π₁ pp α β e))
          fppZ : fpp ∈ Probe Z
          fppZ = ctsf₀ pp ppX
          claim : ∀(α : ₂ℕ) → π₀ fpp α ≅ π₀ (⟨ U Z ⟩ caseptq ◎ (E-cons s)) α
          claim α = Sym (U Z) (π₀ (⟨ U Z ⟩ caseptq ◎ (E-cons s)) α) (π₀ fpp α)
                              (π₁ (π₀ (case-f₀ (π₀ p (π₀ t (cons s α)))))
                                  (π₀ q (cons s α)) (in₀ (π₀ pp α)) (pr α))
        claim₁ : (∃ \(qq : E-map-₂ℕ (U Y)) →
                     (qq ∈ Probe Y) ∧ (∀(α : ₂ℕ) → π₀ q (cons s α) ≋ in₁ (π₀ qq α))) →
                 ⟨ U Z ⟩ caseptq ◎ (E-cons s) ∈ Probe Z
        claim₁ (qq , qqY , pr) = cond₃ Z ptsqq (⟨ U Z ⟩ caseptq ◎ (E-cons s)) claim ptsqqZ
         where
          ptsqq : E-map-₂ℕ (U Z)
          ptsqq = exp Y Z p (t ◎ (E-cons s)) qq
          ptsqqZ : ptsqq ∈ Probe Z
          ptsqqZ = pYZ qq qqY (t ◎ (E-cons s))
                              (Lemma[◎-UC] t uct (E-cons s) (Lemma[E-cons-UC] s))
          claim : ∀(α : ₂ℕ) → π₀ ptsqq α ≅ π₀ (⟨ U Z ⟩ caseptq ◎ (E-cons s)) α
          claim α = Sym (U Z) (π₀ (⟨ U Z ⟩ caseptq ◎ (E-cons s)) α) (π₀ ptsqq α)
                              (π₁ (π₀ (case-f₀ (π₀ p (π₀ t (cons s α)))))
                                  (π₀ q (cons s α)) (in₁ (π₀ qq α)) (pr α))
  ecase : ∀(f₀ f₀' : Ũ (U (X ⇒ Z))) → E (U (X ⇒ Z)) f₀ f₀' →
           E (U ((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z)) (case f₀) (case f₀')
  ecase f₀ f₀' eff f₁ (in₀ x) = eff x
  ecase f₀ f₀' eff f₁ (in₁ y) = Refl (U Z) (π₀ (π₀ f₁) y)
  cts : continuous {X ⇒ Z} {(Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z} (case , ecase)
  cts p pXZ q qYZ t uct r rXY u ucu = cond₂ Z caseptqur (n , prf)
   where
    casep : E-map-₂ℕ (U((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z))
    casep = ⟨ U(X ⇒ Z) ∣ U((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z) ⟩ (case , ecase) ◎ p
    caseptqur : E-map-₂ℕ (U Z)
    caseptqur = exp (X ⊕ Y) Z (exp (Y ⇒ Z) ((X ⊕ Y) ⇒ Z) casep t q) u r
    n : ℕ
    n = ∃-witness rXY
    prf : ∀(s : ₂Fin n) → ⟨ U Z ⟩ caseptqur ◎ (E-cons s) ∈ Probe Z
    prf s = Case claim₀ claim₁ (∃-elim rXY s)
     where
      ucus : uniformly-continuous-₂ℕ (u ◎ (E-cons s))
      ucus = Lemma[◎-UC] u ucu (E-cons s) (Lemma[E-cons-UC] s)
      ptus : ₂ℕ → Ũ (U (X ⇒ Z))
      ptus α = π₀ p (π₀ t (π₀ u (cons s α)))
      qus : ₂ℕ → Ũ (U (Y ⇒ Z))
      qus α = π₀ q (π₀ u (cons s α))
      claim₀ : (∃ \(pp : E-map-₂ℕ (U X)) →
                   (pp ∈ Probe X) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₀ (π₀ pp α))) →
               ⟨ U Z ⟩ caseptqur ◎ (E-cons s) ∈ Probe Z
      claim₀ (pp , ppX , pr) = cond₃ Z ptuspp (⟨ U Z ⟩ caseptqur ◎ (E-cons s)) claim ptusppZ
       where
        ptuspp : E-map-₂ℕ (U Z)
        ptuspp = exp X Z p (t ◎ (u ◎ (E-cons s))) pp
        ptusppZ : ptuspp ∈ Probe Z
        ptusppZ = pXZ pp ppX (t ◎ (u ◎ (E-cons s)))
                             (Lemma[◎-UC] t uct (u ◎ (E-cons s)) ucus)
        claim : ∀(α : ₂ℕ) → π₀ ptuspp α ≅ π₀ (⟨ U Z ⟩ caseptqur ◎ (E-cons s)) α
        claim α = Sym (U Z) (π₀ (⟨ U Z ⟩ caseptqur ◎ (E-cons s)) α) (π₀ ptuspp α)
                            (π₁ (π₀ (π₀ (π₀ (case (ptus α))) (qus α)))
                                (π₀ r (cons s α)) (in₀ (π₀ pp α)) (pr α))
      claim₁ : (∃ \(qq : E-map-₂ℕ (U Y)) →
                   (qq ∈ Probe Y) ∧ (∀(α : ₂ℕ) → π₀ r (cons s α) ≋ in₁ (π₀ qq α))) →
               ⟨ U Z ⟩ caseptqur ◎ (E-cons s) ∈ Probe Z
      claim₁ (qq , qqY , pr) = cond₃ Z qusqq (⟨ U Z ⟩ caseptqur ◎ (E-cons s)) claim qusqqZ
       where
        qusqq : E-map-₂ℕ (U Z)
        qusqq = exp Y Z q (u ◎ (E-cons s)) qq
        qusqqZ : qusqq ∈ Probe Z
        qusqqZ = qYZ qq qqY (u ◎ (E-cons s)) ucus
        claim : ∀(α : ₂ℕ) → π₀ qusqq α ≅ π₀ (⟨ U Z ⟩ caseptqur ◎ (E-cons s)) α
        claim α = Sym (U Z) (π₀ (⟨ U Z ⟩ caseptqur ◎ (E-cons s)) α) (π₀ qusqq α)
                            (π₁ (π₀ (π₀ (π₀ (case (ptus α))) (qus α)))
                                (π₀ r (cons s α)) (in₁ (π₀ qq α)) (pr α))

\end{code}