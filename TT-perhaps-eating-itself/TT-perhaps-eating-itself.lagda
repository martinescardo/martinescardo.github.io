Chuangjie Xu & Martin Escardo, 7th March 2014

Type theory eating itself?
--------------------------

This is based on Coquand's presentation of the syntax of type theory
and its semantics in set theory using families (pdf version sent to
the HoTT list 20 Feb 2014).

We also incorporate a treatment of a tower of universes by Coquand,
Escardo & Spitters (2013 at IAS), using "Type n" judgements with
corresponding universes U n, interpreted as Set n, where Set n is the
nth Grothendieck universe.

Some differences:

 (0) We use type theory for the semantics, rather than set theory, and
     hence type theoretic universes.

 (1) We don't have judgemental equality in our type theory.
     But the required equations hold in the model, *judgementally*. 

     We instead have syntactic "transport" functions "T" presented as
     term constructors.

     Conjecture: this theory has the same expressivity as the theory
     with judgemental equality.

 (2) We modify the treatment of universes so that our syntax can be
     directly interpreted in Agda (which in particular lacks
     cumulativity).

     We use Agda's universe levels, which should be regarded as
     natural numbers in the meta-language (outside Agda), ranged over
     by i,j,k. Definitions with levels should be regarded as
     schematic, even though Agda does allow quantification over
     levels. So if a definition has a level i as a parameter, it
     should be considered as countably many definitions, with
     i=0,1,2,..., of which only finitely many levels are invoked in
     each use.

Also, although we have El and |-| in the syntax, they are identity
functions in the semantics, so that we have universes à la Russell
(because Agda's Set-universes are à la Russell).

This file typechecks in Agda version 2.3.3.
http://www.cs.bham.ac.uk/~mhe/TT-perhaps-eating-itself/TT-perhaps-eating-itself.lagda

\begin{code}

module TT-perhaps-eating-itself where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_)
open import Preliminaries

\end{code}

Syntax. This follows closely Coquand's approach, with the differences
discussed above.

We have, as usual, contexts, substitutions, types and terms:

\begin{code}

data Cxt   : Level               → Set
data Subst : {i j : Level}       → Cxt i → Cxt j → Set
data Type  : {i : Level} → Level → Cxt i → Set
data Term  : {i j : Level}       → (Γ : Cxt i) → Type j Γ → Set

\end{code}

These are mutually recursively defined below.

For contexts, we have:

  ε      the empty context,
  Γ·A    the extension of the context Γ with the type A.

\begin{code}

data Cxt where
  ε   : {i : Level} → Cxt i
  _·_ : {i j : Level} (Γ : Cxt i) → Type j Γ → Cxt(i ⊔ j)

\end{code}

For types, we have:

  A[σ]        the application of the substitution σ to the type A,
  Sigma, Pi   dependent sum and product,
  U j         the jth universe, in any context of level i, which has type j+1,
  El u        the type corresponding to the term u:U.

\begin{code}

data Type where
  _[_]  : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} → Type k Γ → Subst Δ Γ → Type k Δ
  Sigma : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → Type k (Γ · A) → Type (j ⊔ k) Γ
  Pi    : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → Type k (Γ · A) → Type (j ⊔ k) Γ
  U     : {i : Level} {Γ : Cxt i} (j : Level) → Type (lsuc j) Γ
  El    : {i j : Level} {Γ : Cxt i} → Term Γ (U j) → Type j Γ

\end{code}

For substitutions, we have
  
  I       the identity,
  σ◦τ     the composition of the substitutions σ and τ,
  p       the (first-)projection substitution,
  ₍σ,u₎   extension.

\begin{code}

data Subst where
  I     : {i : Level} {Γ : Cxt i} → Subst Γ Γ
  _◦_   : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {Ξ : Cxt k} → Subst Δ Γ → Subst Ξ Δ → Subst Ξ Γ
  p     : {i j : Level} {Γ : Cxt i} {A : Type j Γ} → Subst (Γ · A) Γ
  ₍_,_₎ : {i j k : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ}
          (σ : Subst Δ Γ) → Term Δ (A [ σ ]) → Subst Δ (Γ · A)

\end{code}

The following functions are "macros", used for clarity. Technically,
they are mutually recursively defined together with contexts, types,
terms, substitutions. We could have simply expanded their definitions
below, at the expense of making the definitions of term constructors
more unreadable (and this is what our first version of the definition
was).

They are the substitutions

  B ⌜ u ⌝ := B [ ₍ I , u ₎ ],
  v ⌞ u ⌟ := v ⟨ ₍ I , u ₎ ⟩, 
  B ⌈ σ ⌉ := B [ ₍ σ ◦ p , q ₎ ], 
  u ⌊ σ ⌋ := u ⟨ ₍ σ ◦ p , q ₎ ⟩.

However, because we don't have judgemental equality in our theory, we
need to apply syntactic transport functions at appropriate places:

  B ⌜ u ⌝ := B [ ₍ I , T₁ u ₎ ],
  v ⌞ u ⌟ := v ⟨ ₍ I , T₁ u ₎ ⟩, 
  B ⌈ σ ⌉ := B [ ₍ σ ◦ p , T₀ q ₎ ], 
  u ⌊ σ ⌋ := u ⟨ ₍ σ ◦ p , T₀ q ₎ ⟩.

We are not able to define these functions at this point, because T₀
and T₁ haven't been defined (they are term constructors below). We
just declare their type, so that the definition of terms can use it:

\begin{code}

_⌜_⌝ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} → 
       Type k (Γ · A) → Term Γ A → Type k Γ

_⌞_⌟ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
       Term (Γ · A) B → (u : Term Γ A) → Term Γ (B ⌜ u ⌝)

_⌈_⌉ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} →
       Type l (Γ · A) → (σ : Subst Δ Γ) → Type l (Δ · (A [ σ ]))

_⌊_⌋ : {i j k l : Level} {Γ : Cxt i} {Δ : Cxt j} {A : Type k Γ} {B : Type l (Γ · A)} →
       Term (Γ · A) B → (σ : Subst Δ Γ) → Term (Δ · (A [ σ ])) (B ⌈ σ ⌉)

\end{code}

For terms, we have

  u⟨σ⟩        substitution,
  u,v         the dependent pairing of two terms,
  Pr₁, Pr₂    the two term-level projections 
  Lam u       the lambda abstraction (= currying) of a term u,
  App u v     the application of a term to another,
  q           the (second) context projection,
  |A|         the conversion of a type A into a term of type U,
  T_ u        various "syntactical transports" of a term u,
              replacing corresponding judgmental equalities.

\begin{code}

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

\end{code}

Here is our definitions of the macros:

\begin{code}

B ⌜ u ⌝ = B [ ₍ I , T₁ u ₎ ]
u ⌞ v ⌟ = u ⟨ ₍ I , T₁ v ₎ ⟩
B ⌈ σ ⌉ = B [ ₍ σ ◦ p , T₀ q ₎ ]
u ⌊ σ ⌋ = u ⟨ ₍ σ ◦ p , T₀ q ₎ ⟩ 

\end{code}

Now the standard interpretation of type theory in type theory, defined
by (structural) mutual recursion, of course, with context,
substitution, type and term interpretation functions:

  A context is interpreted as a "set".
  A substitution is interpreted as a function from contexts to contexts.
  A type is interpreted as a function from contexts to sets.
  A term is interpreted as a dependent function from contexts to types.

\begin{code}

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

\end{code}

The funny order in the patterns in the definition of the
interpretation of terms comes from Agda's whim (if we reorder them
according to our taste, the file fails to typecheck).

All the required equations hold definitionally in the semantics.

The equations below labelled "eq" don't rely on the "transport" term
constructors T₀-T₄, but the ones labelled "Eq" do (either explicitly
or implicitly via the "macros" defined above).

\begin{code}

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


eq₂₁ : {i j : Level} {Γ : Cxt i} {A : Type j Γ} →
     let p' = p {i} {j} {Γ} {A}
         q' = q {i} {j} {Γ} {A}
         I' = I {j ⊔ i} {Γ · A}

     in subst⟦ ₍ p' , q' ₎ ⟧ ≡ subst⟦ I' ⟧
       -----------------------------------
eq₂₁ = refl


eq₂₂ : {i j : Level} {Γ : Cxt i} {A : Type j Γ}

     → type⟦ El ∣ A ∣ ⟧ ≡ type⟦ A ⟧
       --------------------------
eq₂₂ = refl


eq₂₃ : {i j : Level} {Γ : Cxt i} {u : Term Γ (U j)} 

     → term⟦ ∣ El u ∣ ⟧ ≡ term⟦ u ⟧
       --------------------------
eq₂₃ = refl

\end{code}

To do: 

  Now, once the terms, types, substitutions and contexts have been
  defined and interpreted, define congruences on them, and prove that
  the interpretation transforms congruence into *definitional*
  equality, as in the above equations.  We believe we can see that
  this is the case.

  Next, define the presheaf interpretation. (We believe that all the
  equations that currently hold definitionally will only hold
  propositionally.)
