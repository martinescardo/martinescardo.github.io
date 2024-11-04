module ordinals where

{--
    Ordinals in Goedel's system T and in Martin-Loef Type Theory
    ------------------------------------------------------------

    Martin Escardo, 2010, coded in Agda November 2011.

    This is based on work of Coquand, Setzer and Hancock, in particular:

    (i) Coquand, Hancock and Setzer (1997)
    http://www.cse.chalmers.se/~coquand/ordinal.ps

    (ii) Hancock (Russell'08 Proof Theory meets Type Theory, Swansea)
    http://www.cs.swan.ac.uk/~csetzer/russell08/slides/hancock.pdf

    An interesting and powerful idea is their use of "lenses", which
    allows to define rather large ordinals, in particular in the
    presence of dependent types and universes. Another idea is to use
    Church encodings of ordinals.

    Here I do something more modest, without lenses, but still with
    Church encodings. I explicitly define addition, multiplication and
    exponentiation of ordinals, and there may be a small contribution
    here.

    In the Goedel system T fragment of Agda, these arithmetic
    operations cannot be uniformly typed, but they still have neat
    definitions. In particular, because of the non-uniform typing, we
    can only dominate ordinals strictly below ε₀ - this is not a
    limitation of our approach, but rather of system T.

    Using dependent types (products in fact will be enough) and a
    universe, we can get a uniform typing of the arithmetic
    operations, and hence the ordinal ε₀ and much higher indeed. But I
    will content myself with defining ε₀, which is not definable in
    system T, as an illustration of what dependent types and universes
    add in terms of expressivity. But it is easy to get higher using
    what is defined here. If you want to get really high, then you
    should study lenses: http://personal.cis.strath.ac.uk/~ph/

    We proceed in three steps to define addition, multiplication and
    exponentiation, and hence ε₀ and much higher.

    (1): We essentially use Goedel's system T and work with a type 

            O X = X → (X → X) → ((ℕ → X) → X) → X 

         of Church encodings of ordinal trees, where X is a parameter,
         and define the basic arithmetic operations on ordinals with
         the non-uniform types

            add : O X → O X → O X
            mul : O X → O(O X) → O X
            exp : O(O X) → O(O X) → O X

         These types are the best one can do in system T. With this we
         can define ordinals abitrarily close to, and strictly below,
         the ordinal ε₀.

    (2): We use the first universe and dependent products to define

            O' X = Π(n : ℕ) → Oⁿ⁺¹ X 
  
         and hence the arithmetic operations with uniform types

            add', mul', exp' : O' X → O' X → O' X

         from add, mul, exp defined in step (1). With this we can now
         define ε₀, not only in O' X, but also in O X.

         So you can see the type O' X as an auxiliary construction to
         get more in O X.



    (3): We inductively define a (standard) W-type of ordinal trees
    (e.g. studied by Brouwer, by Howard in an extension of system T,
    and mentioned by Martin-Loef in some of his papers), and show how
    to define complex Brouwer ordinal trees *without* using
    (structural) recursion on ordinals trees, using step (2).

    All (primitive) recursions in the development of (1)-(3) are on
    the set ℕ. This is followed by exercises, now using recursion and
    induction on Brouwer ordinal trees.

--}


-- Natural numbers.

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

rec : {X : Set} → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (succ n) = f(rec x f n)


-- Step (1). 
--
-- Church ordinal trees:

O : Set → Set
O X = X → (X → X) → ((ℕ → X) → X) → X

zer : {X : Set} → O X
zer = λ z → λ s → λ l → z

suc : {X : Set} → O X → O X
suc a = λ z → λ s → λ l → s(a z s l)

lim : {X : Set} → (ℕ → O X) → O X
lim as = λ z → λ s → λ l → l(λ i → as i z s l)

O-rec : {X : Set} → X → (X → X) → ((ℕ → X) → X) → (O X → X)
O-rec z s l a = a z s l

-- Notice that by uncurrying, flipping and currying the type of O-rec
-- is isomorphic to {X : Set} → O X → O X, but the above form is more
-- convenient for recursive definitions.

-- In this first step, we have natural definitions but the types are
-- not uniform:

add : {X : Set} → O X → O X → O X
add a b = λ z → λ s → λ l → a (b z s l) s l 

mul : {X : Set} → O X → O(O X) → O X
mul a = O-rec zer (λ r → add r a) lim

exp : {X : Set} → O(O X) → O(O X) → O X
exp a = O-rec (suc zer) (λ r → mul r a) lim

-- Remark: if we had used O-rec to define add, it would instead have
-- the type {X : Set} → O X → O(O X) → O X, and then mul would have
-- the type {X : Set} → O(O X) → O(O X) → O X, with the same
-- definition, but the same definition of exp then cannot be typed
-- using iterations of O. In step (2) we will consider all finite
-- iterations of O to define a type O', and give a uniform type 
-- {X : Set} → O' X → O' X → O' X to add, mul, and exp.

-- We will not use the following:

down : {X : Set} → O(O X) → O X
down = O-rec zer suc lim

-- There is a term up : {X : Set} → O X → O(O X), but no such term has
-- the desired behaviour of being a (left or right) inverse of down. 

-- Before using the first universe, we can dominate any ordinal below ε₀.
--
-- The sequence of finite ordinals first:

finite : {X : Set} → ℕ → O X
finite = rec zer suc

-- Its limit:

ω : {X : Set} → O X
ω = lim finite

-- Now the iterated powers of ω, which can't be defined uniformly
-- without universes or W-types or impredicativity etc.

ω₁ : {X : Set} → O X
ω₁ = exp ω ω

ω₂ : {X : Set} → O X
ω₂ = exp ω ω₁

ω₃ : {X : Set} → O X
ω₃ = exp ω ω₂

-- And so on. Although the definitions look uniform, they are not. In
-- fact, the candidate for the recursion step doesn't have type 
-- O X → O X, but rather:

step :  {X : Set} → O(O X) → O X
step = exp ω

-- If you try to define
--
--   ω-tower : {X : Set} → ℕ → O X
--   ω-tower = rec ω (exp ω) 
--
-- then Agda rightfully complains that this would need X = O X, which
-- is impossible.
--
-- Moreover, e.g. in the definition of ω₃ the use of ω has its type X
-- instantiated to O(O(O(O X))), if I counted properly. Thus, although
-- we always write ω in the definitions of ω₁, ω₂, ω₃, ..., if we are
-- strictly working in system T we need a different definition of ω in
-- each case (with the same raw term but with a different type).


-- Step (2). 
--
-- We now use the first universe to reach ε₀ and beyond.  We
-- build a type O' X of ordinals based on O X. It is the definition of
-- rec₁, used to construct O', that uses the first universe. So we
-- move from higher-type primitive recursion (system T) to even higher
-- primitive recursion using a universe.


rec₁ : Set → (Set → Set) → ℕ → Set
rec₁ X F zero = X
rec₁ X F (succ n) = F(rec₁ X F n)

-- We define O' X = Π (n : ℕ) → Oⁿ⁺¹ X as follows in Agda notation:
O' : Set → Set
O' X = (n : ℕ) → O(rec₁ X O n)

zer' : {X : Set} → O' X
zer' = λ n → zer

suc' : {X : Set} → O' X → O' X
suc' a = λ n → suc(a n)

lim' : {X : Set} → (ℕ → O' X) → O' X
lim' as = λ n → lim(λ i → as i n)

add' : {X : Set} → O' X → O' X → O' X
add' a b = λ n → add (a n) (b n) 

mul' : {X : Set} → O' X → O' X → O' X
mul' a b = λ n → mul (a n) (b(succ n))

exp' : {X : Set} → O' X → O' X → O' X
exp' a b = λ n → exp (a(succ n)) (b(succ n))

ω' : {X : Set} → O' X
ω' = λ n → ω

ω-tower' : {X : Set} → ℕ → O' X
ω-tower' = rec ω' (exp' ω') 

-- The ordinal ε₀ can now be defined in O' X (and hence in O X - see
-- below).

ε₀' : {X : Set} → O' X
ε₀' = lim' ω-tower'

-- Because we now have addition, multiplication, exponentiation and
-- limits in a uniform way, we can of course get much higher than ε₀.
-- For example, ε₁, ε₂, ... can be defined uniformly and hence we can
-- define εω. Then proceeding in the same way we can get εα for α =
-- ε₀, and much higher indeed.


-- Now, using this last step (2), we can project to step (1) and
-- define ε₀ as an element of O X using the following coersion:

O'↦O : {X : Set} → O' X → O X
O'↦O a = a zero

ε₀ : {X : Set} → O X
ε₀ = O'↦O ε₀'


-- Notice that the following doesn't type check:
--
--   O↦O' : {X : Set} → O X → O' X
--   O↦O' a = λ n → a
--
-- But it does type check for some particular a, such as ω in the
-- above definition of ω'.


-- Step (3). 
--
-- Brouwer's ordinal trees. 
--
-- I will use the letters u,v to range over B, and us,vs to range over
-- forests, that is, sequences ℕ → B.

data B : Set where
 Z : B
 S : B → B
 L : (ℕ → B) → B

-- Firstly we can go from O X to B when X=B:

O↦B : O B → B
O↦B u = u Z S L

-- We can now define a very tall ordinal tree without recursion on B:

B-ε₀ : B
B-ε₀ = O↦B ε₀


-- Step (4): But the above is not the end of the story. This step, not
-- mentioned above, is started but not completed. We leave the
-- completion as an exercise at the time of writing.
--
-- We can define the tree B-ε₀ by recursion on B and we should show,
-- in Agda, that this produces the same result as the above
-- recursion-free definition.

B-rec : {X : Set} → X → (X → X) → ((ℕ → X) → X) → B → X
B-rec {X} z s l = h
 where 
  h : B → X
  h Z = z
  h(S u) = s(h u)
  h(L us) = l(λ i → h(us i))

-- By suitable uncurrying, flipping and currying, the type of B-rec is
-- isomorphic to {Set X} → B → O X, but the above form is more
-- convenient for recursive definitions:

B↦O : {X : Set} → B → O X
B↦O u s z l = B-rec s z l u

-- Ordinal tree arithmetic:

B-add : B → B → B
B-add u = B-rec u S L

B-mul : B → B → B
B-mul u = B-rec Z (λ r → B-add r u) L

B-exp : B → B → B
B-exp u = B-rec (S Z) (λ r → B-mul r u) L

B-finite : ℕ → B
B-finite = rec Z S

B-ω : B
B-ω = L B-finite

B-ω-tower : ℕ → B
B-ω-tower = rec B-ω (B-exp B-ω) 

B-ε₀-alternative : B
B-ε₀-alternative = L B-ω-tower

-- We are almost ready to formulate the exercise. We need to define
-- extensional equality on B.

data _≣_ : B → B → Set where
 ≣-Z : Z ≣ Z
 ≣-S : ∀(u v : B) → u ≣ v → S u ≣ S v
 ≣-L : ∀(us vs : ℕ → B) → (∀(i : ℕ) → us i ≣ vs i) → L us ≣ L vs


-- Exercises: 
--
-- Transform the following postulates into theorems, by removing the
-- word "postulate" and adding definitions to the postulated
-- propositions. By writing the exercises as postulates, at least we
-- know that the propositions type-check and hence make sense.

postulate Exercise₀ : B-ε₀ ≣ B-ε₀-alternative

-- Here is a sketch of how this can be approached:

postulate Exercise₁ : ∀(u v : B) → B-add u v ≣ O↦B(add (B↦O u) (B↦O v))

postulate Exercise₂ : ∀(u v : B) → B-mul u v ≣ O↦B(mul (B↦O u) (B↦O v))

postulate Exercise₃ : ∀(u v : B) → B-exp u v ≣ O↦B(exp (B↦O u) (B↦O v))

-- We need more coersions:

B↦O' : {X : Set} → B → O' X
B↦O' u = λ n → B↦O u

O'↦B : O' B → B
O'↦B a =  O↦B(O'↦O a)

postulate Exercise₁' : ∀(u v : B) → B-add u v ≣ O'↦B(add' (B↦O' u) (B↦O' v))

postulate Exercise₂' : ∀(u v : B) → B-mul u v ≣ O'↦B(mul' (B↦O' u) (B↦O' v))

postulate Exercise₃' : ∀(u v : B) → B-exp u v ≣ O'↦B(exp' (B↦O' u) (B↦O' v))

-- And, to solve the above exercises, you will need induction on B
-- (which amounts to "primitive recursion" on B, rather than simple
-- recursion or iteration B-rec on B):

B-induction : {A : B → Set} → 
   A Z → 
  (∀(u : B) → A u → A(S u)) → 
  (∀(us : ℕ → B) → (∀(i : ℕ) → A(us i)) → A(L us)) →
-----------------------------------------------------------
  (∀(u : B) → A u)

B-induction {A} z s l = h
 where 
  h : ∀(u : B) → A u
  h Z = z
  h(S u) = s u (h u)
  h(L us) = l us (λ i → h(us i))
