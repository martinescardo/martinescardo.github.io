-- Chuangjie Xu & Martin Escardo, 7th March 2014

module TT-perhaps-eating-itself-without-comments where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)

-- Syntax of a type theory with "syntactic transport" rather than judgemental equality:

data Cxt   : Level               → Set
data Subst : {i j : Level}       → Cxt i → Cxt j → Set
data Type  : {i : Level} → Level → Cxt i → Set
data Term  : {i j : Level}       → (Γ : Cxt i) → Type j Γ → Set

data Cxt where
  ε   : {i : Level} → Cxt i
  _·_ : {i j : Level} (Γ : Cxt i) → Type j Γ → Cxt(i ⊔ j)

data Type where
  _[_]  : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} → Type k Γ → Subst Δ Γ → Type k Δ
  Sigma : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → Type k (Γ · A) → Type (j ⊔ k) Γ
  Pi    : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → Type k (Γ · A) → Type (j ⊔ k) Γ
  U     : {i : Level} {Γ : Cxt i} (j : Level) → Type (lsuc j) Γ
  El    : {i j : Level} {Γ : Cxt i} → Term Γ (U j) → Type j Γ

data Subst where
  I     : {i : Level} {Γ : Cxt i} → Subst Γ Γ
  _◦_   : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} → Subst Δ Γ → Subst Ξ Δ → Subst Ξ Γ
  p     : {i j : Level} {Γ : Cxt i} {A : Type j Γ} → Subst (Γ · A) Γ
  ₍_,_₎ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ}
          (σ : Subst Δ Γ) → Term Δ (A [ σ ]) → Subst Δ (Γ · A)

-- "macros", defined after the definition of Terms, but used in the definition of terms:

_⌜_⌝ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} → 
       Type k (Γ · A) → Term Γ A → Type k Γ

_⌞_⌟ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
       Term (Γ · A) B → (u : Term Γ A) → Term Γ (B ⌜ u ⌝)

_⌈_⌉ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} →
       Type l (Γ · A) → (σ : Subst Δ Γ) → Type l (Δ · (A [ σ ]))

_⌊_⌋ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)} →
       Term (Γ · A) B → (σ : Subst Δ Γ) → Term (Δ · (A [ σ ])) (B ⌈ σ ⌉)

data Term where
  _⟨_⟩  : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} →
          Term Γ A → (σ : Subst Δ Γ) → Term Δ (A [ σ ])

  _,_   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          (u : Term Γ A) → Term Γ (B ⌜ u ⌝) → Term Γ (Sigma A B)

  Pr₁   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          Term Γ (Sigma A B) → Term Γ A

  Pr₂   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          (w : Term Γ (Sigma A B)) → Term Γ (B ⌜ Pr₁ w ⌝) 

  Lam   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          Term (Γ · A) B → Term Γ (Pi A B)

  App   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          Term Γ (Pi A B) → (u : Term Γ A) → Term Γ (B ⌜ u ⌝)

  q     : {i j : Level} {Γ : Cxt i} {A : Type j Γ} → 
          Term (Γ · A) (A [ p ])

  ∣_∣    : {i j : Level} {Γ : Cxt i} → 
          Type j Γ → Term Γ (U j)

-- Syntactic transports:

  T₀    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} {A : Type l Γ}
          {σ : Subst Δ Γ} {δ : Subst Ξ Δ} →
          Term Ξ (A [ σ ] [ δ ]) → Term Ξ (A [ σ ◦ δ ])

  T₁    : {i j : Level} {Γ : Cxt i} {A : Type j Γ} →
          Term Γ A → Term Γ (A [ I ]) 

  T₂    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
          {u : Term Γ A} {σ : Subst Δ Γ} →
          Term Δ (B ⌜ u ⌝ [ σ ]) → Term Δ (B ⌈ σ ⌉ ⌜ u ⟨ σ ⟩ ⌝)

  T₃    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
          {σ : Subst Δ Γ} →
          Term Δ ((Pi A B) [ σ ]) → Term Δ (Pi (A [ σ ]) (B ⌈ σ ⌉))

  T₄    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
          {σ : Subst Δ Γ} →
          Term Δ ((Sigma A B) [ σ ]) → Term Δ (Sigma (A [ σ ]) (B ⌈ σ ⌉))

-- Backward versions:

  T⁰    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} {A : Type l Γ}
          {σ : Subst Δ Γ} {δ : Subst Ξ Δ} → 
          Term Ξ (A [ σ ◦ δ ]) → Term Ξ (A [ σ ] [ δ ]) 

  T¹    : {i j : Level} {Γ : Cxt i} {A : Type j Γ} →
          Term Γ (A [ I ]) → Term Γ A

  T²    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
          {u : Term Γ A} {σ : Subst Δ Γ} →
          Term Δ (B ⌈ σ ⌉ ⌜ u ⟨ σ ⟩ ⌝) → Term Δ (B ⌜ u ⌝ [ σ ])

  T³    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
          {σ : Subst Δ Γ} →
          Term Δ (Pi (A [ σ ]) (B ⌈ σ ⌉)) → Term Δ ((Pi A B) [ σ ])

  T⁴    : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
          {σ : Subst Δ Γ} →
          Term Δ (Sigma (A [ σ ]) (B ⌈ σ ⌉)) → Term Δ ((Sigma A B) [ σ ]) 

-- The definition of the macros:

B ⌜ u ⌝ = B [ ₍ I , T₁ u ₎ ]
u ⌞ v ⌟ = u ⟨ ₍ I , T₁ v ₎ ⟩
B ⌈ σ ⌉ = B [ ₍ σ ◦ p , T₀ q ₎ ]
u ⌊ σ ⌋ = u ⟨ ₍ σ ◦ p , T₀ q ₎ ⟩ 

-- Our "library":

data [] {i : Level} : Set i where
 ⋆ : [] 

record Σ {i j : Level}{A : Set i}(B : A → Set j) : Set(i ⊔ j) where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

-- The standard interpretation of our type theory:

cxt⟦_⟧   : {i : Level}                              → Cxt i     → Set i
subst⟦_⟧ : {i j : Level} {Δ : Cxt i} {Γ : Cxt j}    → Subst Δ Γ → cxt⟦ Δ ⟧ → cxt⟦ Γ ⟧
type⟦_⟧  : {i j : Level} {Γ : Cxt i}                → Type j Γ  → cxt⟦ Γ ⟧ → Set j
term⟦_⟧  : {i j : Level} {Γ : Cxt i} {A : Type j Γ} → Term Γ A  → (γ : cxt⟦ Γ ⟧) → type⟦ A ⟧ γ 

cxt⟦ ε ⟧           = []
cxt⟦ Γ · A ⟧       = Σ \(γ : cxt⟦ Γ ⟧) → type⟦ A ⟧ γ

type⟦ A [ σ ] ⟧    = λ γ → type⟦ A ⟧(subst⟦ σ ⟧ γ)
type⟦ Sigma A B ⟧  = λ γ → Σ \(u : type⟦ A ⟧ γ) → type⟦ B ⟧(γ , u)
type⟦ Pi A B ⟧     = λ γ → (u : type⟦ A ⟧ γ) → type⟦ B ⟧(γ , u)
type⟦ U i ⟧        = λ γ → Set i
type⟦ El u ⟧       = term⟦ u ⟧

subst⟦ I ⟧         = λ γ → γ
subst⟦ σ ◦ τ ⟧     = λ γ → subst⟦ σ ⟧(subst⟦ τ ⟧ γ)
subst⟦ p ⟧         = pr₁
subst⟦ ₍ σ , u ₎ ⟧ = λ γ → (subst⟦ σ ⟧ γ , term⟦ u ⟧ γ)

term⟦ u ⟨ σ ⟩ ⟧    = λ γ → term⟦ u ⟧ (subst⟦ σ ⟧ γ)
term⟦ q ⟧          = pr₂
term⟦ T₀ u ⟧       = term⟦ u ⟧
term⟦ T₁ t ⟧       = term⟦ t ⟧
term⟦ T₂ v ⟧       = term⟦ v ⟧
term⟦ T₃ u ⟧       = term⟦ u ⟧
term⟦ T₄ t ⟧       = term⟦ t ⟧
term⟦ u , v ⟧      = λ γ → (term⟦ u ⟧ γ , term⟦ v ⟧ γ)
term⟦ Pr₁ w ⟧      = λ γ → pr₁(term⟦ w ⟧ γ)
term⟦ Pr₂ w ⟧      = λ γ → pr₂(term⟦ w ⟧ γ)
term⟦ Lam u ⟧      = λ γ v → term⟦ u ⟧(γ , v)
term⟦ App u v ⟧    = λ γ → term⟦ u ⟧ γ (term⟦ v ⟧ γ)
term⟦ ∣ A ∣ ⟧       = type⟦ A ⟧
term⟦ T⁰ u ⟧       = term⟦ u ⟧
term⟦ T¹ t ⟧       = term⟦ t ⟧
term⟦ T² v ⟧       = term⟦ v ⟧
term⟦ T³ u ⟧       = term⟦ u ⟧
term⟦ T⁴ t ⟧       = term⟦ t ⟧

-- Equations:

data _≡_ {i : Level}{A : Set i} : A → A → Set i where
 refl : {a : A} → a ≡ a

eq₀ : {i j : Level} {Δ : Cxt i} {Γ : Cxt j} {σ : Subst Δ Γ} 
    → subst⟦ I ◦ σ ⟧ ≡ subst⟦ σ ◦ I ⟧
      -------------------------------
eq₀ = refl

eq₁ : {i j : Level} {Δ : Cxt i} {Γ : Cxt j} {σ : Subst Δ Γ} 
    → subst⟦ σ ◦ I ⟧ ≡ subst⟦ σ ⟧
      ---------------------------
eq₁ = refl

eq₂ : {i₀ i₁ i₂ i₃ : Level} {Γ₀ : Cxt i₀} {Γ₁ : Cxt i₁} {Γ₂ : Cxt i₂} {Γ₃ : Cxt i₃} 
      {ν : Subst Γ₀ Γ₁} {δ : Subst Γ₁ Γ₂} {σ : Subst Γ₂ Γ₃}
    → subst⟦ (σ ◦ δ) ◦ ν ⟧ ≡ subst⟦ σ ◦ (δ ◦ ν) ⟧
      -------------------------------------------
eq₂ = refl

eq₃ : {i j : Level} {Γ : Cxt i} {A : Type j Γ}
    → type⟦ A [ I ] ⟧ ≡ type⟦ A ⟧
      ---------------------------
eq₃ = refl

eq₄ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k}
      {τ : Subst Ξ Δ} {σ : Subst Δ Γ} {A : Type l Γ}
    → type⟦ A [ σ ] [ τ ] ⟧ ≡ type⟦ A [ σ ◦ τ ] ⟧
      -------------------------------------------
eq₄ = refl

eq₅ :  {i j : Level} {Γ : Cxt i} {A : Type j Γ} {u : Term Γ A} 
    → term⟦ u ⟨ I ⟩ ⟧ ≡ term⟦ u ⟧ 
      ---------------------------
eq₅ = refl

eq₆ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k}
      {τ : Subst Ξ Δ} {σ : Subst Δ Γ} {A : Type l Γ} {u : Term Γ A}
    → term⟦ u ⟨ σ ⟩ ⟨ τ ⟩ ⟧ ≡ term⟦ u ⟨ σ ◦ τ ⟩ ⟧ 
      -------------------------------------------
eq₆ = refl

Eq₇ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} {A : Type l Γ}
      {σ : Subst Δ Γ} {u : Term Δ (A [ σ ])} {δ : Subst Ξ Δ}
    → subst⟦ ₍ σ , u ₎ ◦ δ ⟧ ≡ subst⟦ ₍ σ ◦ δ , T₀ (u ⟨ δ ⟩) ₎ ⟧ 
      ----------------------------------------------------------
Eq₇ = refl

eq₈ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ}
      {σ : Subst Δ Γ} {u : Term Δ (A [ σ ])}
    → subst⟦ p ◦ ₍ σ , u ₎ ⟧ ≡ subst⟦ σ ⟧
      -----------------------------------
eq₈ = refl

eq₉ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ}
      {σ : Subst Δ Γ} {u : Term Δ (A [ σ ])}
    → term⟦ q ⟨ ₍ σ , u ₎ ⟩ ⟧ ≡ term⟦ u ⟧
      -----------------------------------
eq₉ = refl

Eq₁₀ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)} →
       {w : Term Γ (Pi A B)} {u : Term Γ A} {σ : Subst Δ Γ}
     → term⟦ (App w u) ⟨ σ ⟩ ⟧ ≡ term⟦ App (T₃ (w ⟨ σ ⟩)) (u ⟨ σ ⟩) ⟧
       --------------------------------------------------------------
Eq₁₀ = refl

Eq₁₁ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
       {v : Term (Γ · A) B} {σ : Subst Δ Γ}
     → term⟦ (Lam v) ⟨ σ ⟩ ⟧ ≡ term⟦ Lam (v ⌊ σ ⌋) ⟧
       ---------------------------------------------
Eq₁₁ = refl

Eq₁₂ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)}
       {w : Term Γ (Pi A B)}
     → term⟦ Lam (App (T₃ (w ⟨ p ⟩)) q) ⟧ ≡ term⟦ w ⟧
       ----------------------------------------------
Eq₁₂ = refl

eq₁₃ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)}
       {u : Term (Γ · A) B} {v : Term Γ A}
     → term⟦ App (Lam u) v ⟧ ≡ term⟦ u ⌞ v ⌟ ⟧
       ---------------------------------------
eq₁₃ = refl

Eq₁₄ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
       {σ : Subst Δ Γ}
     → type⟦ (Pi A B) [ σ ] ⟧ ≡ type⟦ Pi (A [ σ ]) (B ⌈ σ ⌉) ⟧
       -------------------------------------------------------
Eq₁₄ = refl

Eq₁₅ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
       {σ : Subst Δ Γ}
     → type⟦ (Sigma A B) [ σ ] ⟧ ≡ type⟦ Sigma (A [ σ ]) (B ⌈ σ ⌉) ⟧
       -------------------------------------------------------------
Eq₁₅ = refl

Eq₁₆ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
       {u : Term Γ A} {v : Term Γ (B ⌜ u ⌝)} {σ : Subst Δ Γ}
     → term⟦ (u , v) ⟨ σ ⟩ ⟧ ≡ term⟦ (u ⟨ σ ⟩ , T₂(v ⟨ σ ⟩)) ⟧
       -------------------------------------------------------
Eq₁₆ = refl

eq₁₇ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)}
       {u : Term Γ A} {v : Term Γ (B ⌜ u ⌝)}
     → term⟦ Pr₁ (u , v) ⟧ ≡ term⟦ u ⟧
       --------------------------------
eq₁₇ = refl

eq₁₈ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)}
       {u : Term Γ A} {v : Term Γ (B ⌜ u ⌝)}
     → term⟦ Pr₂ (u , v) ⟧ ≡ term⟦ v ⟧
       --------------------------------
eq₁₈ = refl

Eq₁₉ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
       {t : Term Γ (Sigma A B)} {σ : Subst Δ Γ}
     → term⟦ (Pr₁ t) ⟨ σ ⟩ ⟧ ≡ term⟦ Pr₁ (T₄ (t ⟨ σ ⟩)) ⟧
       -------------------------------------------------
Eq₁₉ = refl

Eq₂₀ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)}
       {t : Term Γ (Sigma A B)} {σ : Subst Δ Γ}
     → term⟦ (Pr₂ t) ⟨ σ ⟩ ⟧ ≡ term⟦ Pr₂ (T₄ (t ⟨ σ ⟩)) ⟧
       --------------------------------------------------
Eq₂₀ = refl

eq₂₁ : {i j : Level} {Γ : Cxt i} {A : Type j Γ}
     → subst⟦ ₍ p {i} {j} {Γ} {A} , q {i} {j} {Γ} {A} ₎ ⟧ ≡ subst⟦ I {j ⊔ i} {Γ · A} ⟧
       -------------------------------------------------------------------------------
eq₂₁ = refl

eq₂₂ : {i j : Level} {Γ : Cxt i} {A : Type j Γ}
     → type⟦ El ∣ A ∣ ⟧ ≡ type⟦ A ⟧
       --------------------------
eq₂₂ = refl

eq₂₃ : {i j : Level} {Γ : Cxt i} {u : Term Γ (U j)} 
     → term⟦ ∣ El u ∣ ⟧ ≡ term⟦ u ⟧
       --------------------------
eq₂₃ = refl
