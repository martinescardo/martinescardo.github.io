-- Two (very similar) proofs of commutativity of addition in Agda
-- Fredrik Nordvall Forsberg, 18 September 2018

-- Both proofs rely on the same two lemmas. The first proof standard
-- proof does not need associativity proven first as a lemma. The
-- second proof uses the experimental

{-# OPTIONS --rewriting #-}

-- feature of Agda to promote the lemmas to rewrite rules, which
-- results in a proof virtually identical to the standard Minlog
-- proof.

module comm where

----- 0 Basics -------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

{-# BUILTIN  NATURAL ℕ #-}

data _≡_ {X : Set}(x : X) : X -> Set where
  refl : x ≡ x

infix 8 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

cong : {X Y : Set}(f : X -> Y) {x y : X} -> x ≡ y -> f x ≡ f y
cong f refl = refl

trans : {X : Set}{x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl p = p

sym : {X : Set}{x y : X} -> x ≡ y -> y ≡ x
sym refl = refl

_+_ : ℕ -> ℕ -> ℕ
x + zero = x
x + (suc y) = suc (x + y)

----- 1 Standard proof ------------------------------

-- First two lemmas:

comm-0+ : (x : ℕ) -> x ≡ zero + x
comm-0+ zero = refl
comm-0+ (suc x) = cong suc (comm-0+ x)

comm-suc+ : (x y : ℕ) -> suc (x + y) ≡ (suc x) + y
comm-suc+ x zero = refl
comm-suc+ x (suc y) = cong suc (comm-suc+ x y)

-- Then the result, using transitivity of equality to combine the IH
-- with applying the second lemma

comm : (x y : ℕ) -> x + y ≡ y + x
comm x zero = comm-0+ x
comm x (suc y) = trans (cong suc (comm x y)) (comm-suc+ y x)

----- 2 Proof using rewrite rules -------------------

-- The rewrites only fires by replacing the lhs with the rhs, so it
-- turns out that we need to first flip the equations in the lemmas
-- above (this is most likely what associativity as a rewrite rule
-- achieved in the Minlog proof):

comm-0+-sym : (x : ℕ) -> zero + x ≡ x
comm-0+-sym x = sym (comm-0+ x)

comm-suc+-sym : (x y : ℕ) -> (suc x) + y ≡ suc (x + y)
comm-suc+-sym x y = sym (comm-suc+ x y)

-- Then we declare that _≡_ is the relation used for rewriting, and
-- that the flipped lemmas should be used to rewrite automatically.

{-# BUILTIN REWRITE _≡_ #-}

{-# REWRITE comm-0+-sym comm-suc+-sym #-}

-- Now the proof is the same as the Minlog proof:

comm' : (x y : ℕ) -> x + y ≡ y + x
comm' x zero = refl
comm' x (suc y) = cong suc (comm' x y)
