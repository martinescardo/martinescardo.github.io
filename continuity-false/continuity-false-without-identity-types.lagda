Martin Escardo 2015.

If all functions (ℕ → ℕ) → ℕ are continuous then 0=1.

Based on the version of 27 Nov 2013
http://www.cs.bham.ac.uk/~mhe/continuity-false/continuity-false.html

In this version we don't use identity types, but we use a universe
instead, in order to define equality on ℕ. This is the only equality
type we consider, and we name it ≡.

Standard preliminaries:

\begin{code}

{-# OPTIONS --without-K #-}

U = Set

data Σ {X : U} (Y : X → U) : U where
 _,_ : (x : X)(y : Y x) → Σ {X} Y

_×_ : U → U → U
X × Y = Σ \(x : X) → Y

π₀ : {X : U} {Y : X → U} → (Σ \(x : X) → Y x) → X
π₀(x , y) = x

π₁ : {X : U} {Y : X → U} (t : Σ \(x : X) → Y x) → Y(π₀ t)
π₁(x , y) = y

data ∅ : U where

∅-rec : {X : U} → ∅ → X
∅-rec ()

data 𝟙 : U where
 * : 𝟙 

𝟙-rec : {X : U} → X → 𝟙 → X
𝟙-rec x * = x

data ℕ : U where 
 zero : ℕ              
 succ : ℕ → ℕ       

\end{code}

We define equality on ℕ by induction and show that it satisfies the
defining properties of the identity type Id ℕ.

\begin{code}

{-# BUILTIN NATURAL ℕ #-}
infix 3 _≡_

_≡_ : ℕ → ℕ → U
0        ≡ 0        = 𝟙 
(succ m) ≡ 0        = ∅ 
0        ≡ (succ n) = ∅ 
(succ m) ≡ (succ n) = m ≡ n 

refl : ∀ n → n ≡ n
refl 0 = *
refl (succ n) = refl n

≡-ind : (A : (m n : ℕ) → m ≡ n → U)
      → (∀ n → A n n (refl n)) →  ∀ m n p → A m n p
-- ≡-ind A r 0 0 p = 𝟙-rec (r 0) p -- doesn't type check.
≡-ind A r 0 0 * = r 0
≡-ind A r (succ m) 0 p = ∅-rec p
≡-ind A r 0 (succ n) p = ∅-rec p 
≡-ind A r (succ m) (succ n) p = ≡-ind (λ m n → A (succ m) (succ n)) (λ n → r(succ n)) m n p

-- We only use ≡-ind to define ≡-rec:

≡-rec : (A : ℕ → ℕ → U) → (∀ n → A n n) →  ∀ m n → m ≡ n → A m n
≡-rec A = ≡-ind (λ m n _ → A m n)

-- We only use ≡-rec to define transport:

transport : (A : ℕ → U) → {x y : ℕ} → x ≡ y → A x → A y
transport A {x} {y} = ≡-rec (λ x y → A x → A y) (λ _ a → a) x y

-- From transport we prove all properties of equality we need here:

sym : ∀{x y} → x ≡ y → y ≡ x
sym {x} {y} p = transport (λ z → z ≡ x) {x} {y} p (refl x)

euclidean : ∀{a b c} → b ≡ c → b ≡ a → c ≡ a
euclidean {a} {b} {c} = transport (λ d → d ≡ a) {b} {c}

trans : ∀{x y z} → x ≡ y → y ≡ z → x ≡ z
trans {x} {y} {z} p = euclidean {z} {y} (sym {x} p)

ap : ∀(f : ℕ → ℕ) → ∀{x y} → x ≡ y → f x ≡ f y
ap f {x} {y} p = transport (λ z → f x ≡ f z) {x} {y} p (refl(f x))

\end{code}

The Baire space of infinite sequences of natural numbers, ranged over
by α and β:

\begin{code}

Baire : U
Baire = ℕ → ℕ

head : {X : ℕ → U} → ((i : ℕ) → X i) → X 0
head α = α 0

tail : {X : ℕ → U} → ((i : ℕ) → X i) → ((i : ℕ) → X(succ i))
tail α = λ i → α(succ i)

_≡[_]_ : Baire → ℕ → Baire → U
α ≡[ zero ] β = 𝟙
α ≡[ succ n ] β = (head α ≡ head β) × (tail α ≡[ n ] tail β)

-- The sequence consisting of n zeros followed by infinitely many k's
-- is written "n zeros-and-then k":

_zeros-and-then_ : ℕ → ℕ → Baire
( 0       zeros-and-then k)  i       = k
((succ n) zeros-and-then k)  0       = 0
((succ n) zeros-and-then k) (succ i) = (n zeros-and-then k) i

zeros-and-then-spec₀ : ∀ n k → (n zeros-and-then k) n ≡ k
zeros-and-then-spec₀  0       k = refl k 
zeros-and-then-spec₀ (succ n) k = zeros-and-then-spec₀ n k

-- The sequence consisting of infinitely many zeros:

O : Baire
O = λ i → 0

zeros-and-then-spec₁ : ∀ n k → O ≡[ n ] (n zeros-and-then k)
zeros-and-then-spec₁ zero k = *
zeros-and-then-spec₁ (succ n) k = * , (zeros-and-then-spec₁ n k)

\end{code}

We now come to the subject of this file. We define the Curry-Howard
interpretation of a Brouwerian continuity principle, and show that not
all functions are continuous. Notice that, by definition, 0≡1 is ∅.

\begin{code}

continuous : (Baire → ℕ) → U
continuous f = ∀ α → Σ \n → ∀ β → α ≡[ n ] β → f α ≡ f β

theorem : (∀(f : Baire → ℕ) → continuous f) → 0 ≡ 1
theorem continuity = zero-is-one
 where
  -- The modulus-of-continuity functional at the point O : Baire:
  M : (Baire → ℕ) → ℕ 
  M f = π₀(continuity f O)

  continuity₀ : ∀ f β → O ≡[ M f ] β → f O ≡ f β
  continuity₀ f = π₁(continuity f O)

  -- Any number is a modulus of continuity of a constant function. Our
  -- hypothetical modulus-of-continuity functional chooses m:
  m : ℕ
  m = M(λ α → 0)

  -- To get the desired contradiction, we define a non-continuous
  -- function using M (twice):
  f : Baire → ℕ
  f β = M(λ α → β(α m))

  -- With definitional/judgemental equality, we have
  --
  --    f O = M(λ α → O(α m)) = M(λ α → 0) = m, 
  -- 
  -- because O(α m) = 0. Agda performs this conversion silently:
  crucial-observation : f O ≡ m
  crucial-observation = refl(f O)
  -- In a system based on combinators S and K rather than the
  -- λ-calculus, this conversion is not available. Often HA^ω is taken
  -- in combinatory form, in which case one needs some form of
  -- extensionality to conclude that f O = m.

  -- The following crucial fact silently uses the above observation,
  -- without the need to invoke its proof refl(f O), because the
  -- equality f O = m is judgemental:
  crucial-fact : ∀ β → O ≡[ M f ] β → m ≡ f β
  crucial-fact = continuity₀ f 

  lemma₀ : M f ≡ 0 → 0 ≡ 1
  lemma₀ p = zero-is-one
   where
    c₀ : ∀ β → O ≡[ M f ] β
    c₀ β = transport (λ n → O ≡[ n ] β) (sym {M f} p) (refl 0)  
    c₁ : ∀ β → m ≡ f β
    c₁ β = crucial-fact β (c₀ β)
    c₂ : M(λ α → α m) ≡ m
    c₂ = sym {m} (c₁ (λ i → i))
    c₃ : ∀ α → O ≡[ M(λ α → α m) ] α → 0 ≡ α m
    c₃ = continuity₀ (λ α → α m) 
    c₄ : ∀ α → O ≡[ m ] α → 0 ≡ α m
    c₄ = transport (λ n → ∀ α → O ≡[ n ] α → 0 ≡ α m) c₂ c₃  
    α : Baire
    α = m zeros-and-then 1
    α-property₀ : α m ≡ 1
    α-property₀ = zeros-and-then-spec₀ m 1
    α-property₁ : O ≡[ m ] α
    α-property₁ = zeros-and-then-spec₁ m 1
    c₅ : 0 ≡ α m
    c₅ = c₄ α α-property₁ 
    zero-is-one : 0 ≡ 1
    zero-is-one = trans {0} {α m} c₅ α-property₀

  lemma₁ : (Σ \n → M f ≡ succ n) → 0 ≡ 1
  lemma₁ (n , p) = zero-is-one
   where
    β : Baire
    β = (M f) zeros-and-then 1
    β-property₀ : β(M f) ≡ 1
    β-property₀ = zeros-and-then-spec₀ (M f) 1
    β-property₁ : O ≡[ M f ] β
    β-property₁ = zeros-and-then-spec₁ (M f) 1
    c₀ : f β ≡ m
    c₀ = sym {m} (crucial-fact β β-property₁)
    c₁ : ∀ α → O ≡[ f β ] α → β 0 ≡ β(α m) 
    c₁ α = continuity₀ (λ α → β(α m)) α
    c₂ : ∀ α → O ≡[ m ] α → β 0 ≡ β(α m) 
    c₂ = transport (λ n → ∀ α → O ≡[ n ] α → β 0 ≡ β(α m)) c₀ c₁ 
    α : Baire
    α = m zeros-and-then (M f)
    α-property₀ : α m ≡ M f
    α-property₀ = zeros-and-then-spec₀ m (M f)
    α-property₁ : O ≡[ m ] α
    α-property₁ = zeros-and-then-spec₁ m (M f)
    c₃ : β 0 ≡ β(α m)
    c₃ = c₂ α α-property₁
    c₅ : β(α m) ≡ β(M f)
    c₅ = ap β α-property₀
    c₆ : β (α m) ≡ 1
    c₆ = trans {β(α m)} c₅ β-property₀
    c₄ : β 0 ≡ 1
    c₄ = trans {β 0} c₃ c₆
    c₈ : O ≡[ succ n ] β
    c₈ = transport (λ n → O ≡[ n ] β) p β-property₁
    c₉ : O ≡[ succ n ] β → 0 ≡ β 0
    c₉ e = π₀ e
    c₇ : 0 ≡ β 0
    c₇ = c₉ c₈
    zero-is-one : 0 ≡ 1
    zero-is-one = trans {0} {β 0} c₇ c₄

  lemma : (Σ \n → M f ≡ n) → 0 ≡ 1
  lemma (0      , p) = lemma₀ p
  lemma (succ n , p) = lemma₁(n , p)

  zero-is-one : 0 ≡ 1
  zero-is-one = lemma(M f , refl(M f)) 

\end{code}

The following observation was communicated to me independently by
each of Altenkirch, Coquand and Martin-Lӧf.

A continuous function is extensional in the sense that it assigns the
same value to pointwise equal inputs:

\begin{code}

continuous-functions-are-extensional : 
 ∀(f : Baire → ℕ) → continuous f → ∀ α β → (∀ i → α i ≡ β i) → f α ≡ f β
continuous-functions-are-extensional f f-continuous α β e = g β (h α β e n)
 where
  n : ℕ
  n = π₀(f-continuous α)
  g : ∀ β → α ≡[ n ] β → f α ≡ f β 
  g = π₁(f-continuous α)
  h : ∀ α β → (∀ i → α i ≡ β i) → ∀ n → α ≡[ n ] β
  h α β e zero = *
  h α β e (succ n) = (e zero) , (h (tail α) (tail β) (tail e) n)

\end{code}

So there is some amount of extensionality built-in in the definition
of continuity.

And here is a simplification suggested by an anonymous TLCA'2015
referee, which we incorporated in the TLCA final version of the paper:

  "Considering \beta = 0^(Mf+1) 1^\omega and \alpha = 0^m
   (Mf+1)^\omega, one can avoid the proof case Mf = 0 and use just the
   other one."

\begin{code}

≡[]-lemma : {α β : Baire} (n : ℕ) → α ≡[ succ n ] β → α ≡[ n ] β
≡[]-lemma zero     _       = *
≡[]-lemma (succ n) (p , q) = p , ≡[]-lemma n q

theorem' : (∀(f : Baire → ℕ) → continuous f) → 0 ≡ 1
theorem' continuity = zero-is-one
 where
  M : (Baire → ℕ) → ℕ 
  M f = π₀(continuity f O)
  continuity₀ : ∀ f β → O ≡[ M f ] β → f O ≡ f β
  continuity₀ f = π₁(continuity f O)
  m : ℕ
  m = M(λ α → 0)
  f : Baire → ℕ
  f β = M(λ α → β(α m))
  β : Baire
  β = (succ(M f)) zeros-and-then 1
  β-property₀ : β(succ(M f)) ≡ 1
  β-property₀ = zeros-and-then-spec₀ (succ(M f)) 1
  β-property₁ : O ≡[ succ(M f) ] β
  β-property₁ = zeros-and-then-spec₁ (succ(M f)) 1
  β-property₂ : O ≡[ M f ] β
  β-property₂ = ≡[]-lemma (M f) β-property₁
  c₀ : f β ≡ m
  c₀ = sym {m} (continuity₀ f β β-property₂)
  c₁ : ∀ α → O ≡[ f β ] α → β 0 ≡ β(α m) 
  c₁ = continuity₀ (λ α → β(α m))
  c₂ : ∀ α → O ≡[ m ] α → β 0 ≡ β(α m) 
  c₂ = transport (λ n → ∀ α → O ≡[ n ] α → β 0 ≡ β(α m)) c₀ c₁ 
  α : Baire
  α = m zeros-and-then (succ(M f))
  α-property₀ : α m ≡ succ(M f)
  α-property₀ = zeros-and-then-spec₀ m (succ(M f))
  α-property₁ : O ≡[ m ] α
  α-property₁ = zeros-and-then-spec₁ m (succ(M f))
  c₃ : β 0 ≡ β(α m)
  c₃ = c₂ α α-property₁
  c₄ : β(α m) ≡ β(succ(M f))
  c₄ = ap β {α m} {succ(M f)} α-property₀
  c₅ : β(α m) ≡ 1
  c₅ = trans {β(α m)} c₄ β-property₀
  c₆ : β 0 ≡ 1
  c₆ = trans {β 0} {β (α m)} {1} c₃ c₅
  c₇ : 0 ≡ β 0
  c₇ = π₀ β-property₁
  zero-is-one : 0 ≡ 1
  zero-is-one = trans {0} {β 0} {1} c₇ c₆

\end{code}
