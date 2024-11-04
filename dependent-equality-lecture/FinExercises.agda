{-# OPTIONS --without-K #-}

module FinExercises where

-- Most, if not all, exercises are intended to be not very hard.
-- You have to fill 13 holes.
--
-- The point is to try to understand Fin better.

data _≡_ {X : Set} : X → X → Set where
 refl : {x : X} → x ≡ x

cong : {X Y : Set} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

-- We rename the constructors of the types Fin n for the sake of
-- clarity:

data Fin : ℕ → Set where
 fzero : {n : ℕ} → Fin (succ n)
 fsucc : {n : ℕ} → Fin n → Fin (succ n)

-- The empty set has no elements:

data ∅ : Set where

-- The Maybe type constructor adds one new element to a set X, called
-- Nothing. The old elements are renamed Just x for x : X.

data Maybe (X : Set) : Set where
  Nothing : Maybe X
  Just    : X → Maybe X

-- Example. The set Maybe(Maybe(Maybe(Maybe ∅))) has four distinct
-- elements:

first second third fourth : Maybe(Maybe(Maybe(Maybe ∅)))
first  = {!!}
second = {!!}
third  = {!!}
fourth = {!!}

-- Nothing is like fzero, and Just is like fsucc. We'll make this
-- precise.

-- According to the following definition,
-- Fin' 4 = Maybe(Maybe(Maybe(Maybe ∅))):

Fin' : ℕ → Set
Fin'  zero    = ∅
Fin' (succ n) = Maybe(Fin' n)

f : (n : ℕ) → Fin' n → Fin n
f = {!!}

g : (n : ℕ) → Fin n → Fin' n
g = {!!}

-- The functions f n : Fin n → Fin' n and g n : Fin' n → Fin n form an
-- isomorphism:
fg-id : (n : ℕ) (k : Fin n) → f n (g n k) ≡ k
fg-id = {!!}

gf-id : (n : ℕ) (t : Fin' n) → g n (f n t) ≡ t
gf-id = {!!}

-- Now we give analogues of fzero and fsucc.

fzero' : {n : ℕ} → Fin' (succ n)
fzero' = {!!}

fsucc' : {n : ℕ} → Fin' n → Fin' (succ n)
fsucc' = {!!}

-- For the sake of completeness, we show that the type Maybe(Maybe ∅)
-- (that is, the type Fin' 2) doesn't have any element other than the
-- two elements we know it has.

-- Negation. The "proposition" ¬ X can hold only when X is empty. If
-- it is inhabited, there is no function X → ∅.

¬_ : Set → Set
¬ X = X → ∅

-- It is absurd to suppose that there is an element in Maybe(Maybe ∅)
-- that is distinct from Nothing and from Just Nothing:

claim : (t : Maybe(Maybe ∅)) → ¬(t ≡ Nothing) → ¬(t ≡ Just Nothing) → ∅
claim = {!!}

-- We can formulate this positively, using _+_ to represent "or":

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

pclaim : (t : Maybe(Maybe ∅)) → (t ≡ Nothing) + (t ≡ Just Nothing)
pclaim t = {!!}


-- Of course, fzero and fsucc fzero are elements of the type
-- Fin(succ(succ zero)). We give them new names to check this:

Zero : Fin(succ(succ zero))
Zero = fzero 

One : Fin(succ(succ zero))
One = fsucc fzero

-- But there is no element other than Zero or One in this type:

claim' : (k : Fin(succ(succ zero))) → ¬(k ≡ Zero) → ¬(k ≡ One) → ∅
claim' = {!!}

-- Positively formulated, this becomes:

pclaim' : (k : Fin(succ(succ zero))) → (k ≡ Zero) + (k ≡ One)
pclaim' = {!!}
