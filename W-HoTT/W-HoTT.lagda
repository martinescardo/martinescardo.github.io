Martin Escardo, 5 Feb 2014.

Regarding a HoTT list discussion initiated by Marc Bezem and Andrej
Bauer (subject " Bootstrapping W-types (and thereby TT) #626"), with
some interaction by Mike Shulman.

Type checked in Agda 2.3.3.

\begin{code}

{-# OPTIONS --without-K #-}

module W-HoTT where

U = Set

data W (A : U) (B : A → U) : U where
 sup : (a : A) → (B a → W A B) → W A B

data Σ {A : U} (B : A → U) : U where
 _,_ : (a : A) → B a → Σ {A} B

_×_ : U → U → U
A × B = Σ \(a : A) → B

data ∅ : U where

∅-rec : {A : U} → ∅ → A
∅-rec ()

¬ : U → U
¬ A = A → ∅

¬¬ : U → U
¬¬ A = ¬(¬ A)

\end{code}

The first version I proposed in the mailing list:

\begin{code}

W-in : {A : U} {B : A → U}  → (Σ \(a : A) → ¬(B a)) → W A B 
W-in (a , u) = sup a (λ b → ∅-rec(u b))

W-out : {A : U} {B : A → U} → W A B → ¬((a : A) → B a)
W-out {A} {B} (sup a f) = ε
 where
  IH : B a → ¬((a : A) → B a)
  IH b = W-out(f b)
  ε : ¬((a : A) → B a)
  ε φ = IH (φ a) φ

\end{code}

By analogy with the definition of cartesian products using Σ, we
define a binary w-product, and then show that A w B is logically
equivalent to A × (¬ B).

\begin{code}

_w_ : U → U → U
A w B = W A (λ a → B)

w-in : {A B : U} → A × (¬ B) → A w B
w-in = W-in

w-out : {A B : U} → A w B → A × (¬ B)
w-out {A} {B} (sup a f) = a , (λ b → W-out (f b) (λ a → b))

\end{code}

The above two functions are actually quasi-inverses of each other, and
so we have a homotopy equivalence (exercise).

A stronger version of W-out is:

\begin{code}

W-out' : {A : U} {B : A → U} → W A B → ¬((a : A) → ¬¬(B a))
W-out' {A} {B} (sup a f) = ε
 where
  IH : B a → ¬((a : A) → ¬¬(B a))
  IH b = W-out'(f b)
  IH' : ¬¬(B a) → ¬((a : A) → ¬¬(B a))
  IH' φ f = φ (λ b → IH b f)
  ε : ¬((a : A) → ¬¬(B a))
  ε φ = IH' (φ a) φ

\end{code}

Equivalently:

\begin{code}

W-out'' : {A : U} {B : A → U} → W A B → ¬¬(Σ \(a : A) → ¬(B a))
W-out'' {A} {B} (sup a f) = ε
 where
  IH : B a → ¬¬(Σ \(a : A) → ¬(B a))
  IH b = W-out''(f b)
  IH' : ¬¬(B a) → ¬¬(Σ \(a : A) → ¬(B a))
  IH' φ f = φ (λ b → IH b f)
  ε : ¬¬(Σ \(a : A) → ¬(B a))
  ε γ = IH' (λ u → γ(a , u)) γ

\end{code}

The above doesn't use the initiality of ∅, and hence ∅ can be replaced
by any type R, with the same proof.

We define a WΣ quantifier to express this concisely:

\begin{code}

WΣ : (A : U) (B : A → U) (R : U) → U
WΣ A B R = ((Σ \(a : A) → B a → R) → R) → R

RW-out : {A : U} {B : A → U} → W A B → ({R : U} → WΣ A B R)
RW-out {A} {B} (sup a f) {R} = ε
 where
  IH : B a → WΣ A B R
  IH b = RW-out(f b)
  IH' : ((B a → R) → R) → WΣ A B R 
  IH' φ f = φ (λ b → IH b f)
  ε : WΣ A B R
  ε γ = IH' (λ u → γ(a , u)) γ

RW-in : {A : U} {B : A → U} → ({R : U} → WΣ A B R) → W A B 
RW-in {A} {B} r = r φ
 where
  φ : Σ (λ a → B a → W A B) → W A B
  φ (a , u) = sup a u

\end{code}

But ({R : U} → WΣ A B R) is the impredicative encoding of W A B!

Added 7 Feb 2014.

\begin{code}

data _+_ (A B : U) : U where
 inl : A → A + B
 inr : B → A + B

decidable : U → U
decidable A = A + ¬ A

DW-out : {A : U} {B : A → U} → ((a : A) → decidable(B a))
       → W A B → Σ \(a : A) → ¬(B a)
DW-out {A} {B} d (sup a f) = φ(d a)
 where
  IH : B a → Σ \(a : A) → ¬(B a)
  IH b = DW-out d (f b)
  φ : B a + ¬(B a) → Σ \(a : A) → ¬(B a)
  φ (inl b) = IH b
  φ (inr u) = a , u

\end{code}

Added 8 Feb 2014.

I am deliberately not using universe polymorphism.

The following generalizes w-out (with lower case) above and a result
by Shulman (see below).

\begin{code}

U₁ = Set₁

data _≡₁_ : U → U → U₁ where
 refl₁ : {X : U} → X ≡₁ X

transport₁ : (P : U → U) → {X Y : U} → X ≡₁ Y → P X → P Y
transport₁ P refl₁ p = p

constant₁ : (A : U) (B : A → U) → U₁
constant₁ A B = (a a' : A) → B a ≡₁ B a'

cw-out : {A : U} {B : A → U} → constant₁ A B
       → W A B → Σ \(a : A) → ¬(B a)
cw-out {A} {B} κ (sup a₀ f) = a₀ , u 
 where
  IH : B a₀ → Σ \(a : A) → ¬(B a)
  IH b = cw-out κ (f b)
  u : ¬(B a₀)
  u b₀ = φ ih b₀
   where
    ih : Σ \(a : A) → ¬(B a)
    ih = IH b₀
    φ : (Σ \(a : A) → ¬(B a)) → ¬(B a₀)
    φ (a , b) = transport₁ (¬) (κ a a₀) b

\end{code}

As a corollary, we get the following result first established by Mike
Shulman, and advertised in the mailing list.

\begin{code}

data _≡_ {A : U} : A → A → U where
 refl : {a : A} → a ≡ a

ap₀₁ : {A : U} {B : A → U} {a a' : A} → a ≡ a' → B a ≡₁ B a'
ap₀₁ {A} {B} refl = refl₁

isProp : U → U
isProp X = (x y : X) → x ≡ y

shulman-w-out : {A : U} {B : A → U} → isProp A 
             → W A B → Σ \(a : A) → ¬(B a)
shulman-w-out {A} {B} p = cw-out κ
 where
  κ : constant₁ A B
  κ a a' = ap₀₁ (p a a')

\end{code}
