-- Let's define equality of natural numbers ourselves.

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
m + zero   = m
m + succ n = succ(m + n)

induction : {A : ℕ → Set}
         →  A zero
         → (∀(k : ℕ) → A k → A(succ k))
         → ∀(n : ℕ) → A n 
induction base step zero     = base
induction base step (succ n) = step n (induction base step n)

-- Set with no elements (empty set):
data 𝟘 : Set where
  -- nothing here

from-𝟘 : {X : Set} → 𝟘 → X
from-𝟘 () -- nothing available in 𝟘 to map to X (it would have been
          -- better if Agda allowed us to write an empty set of
          -- equations)

-- Set with one element (unit type):
data 𝟙 : Set where
 ⋆ : 𝟙

infix 3 _≣_

_≣_ : ℕ → ℕ → Set
zero     ≣ zero     = 𝟙 
(succ m) ≣ zero     = 𝟘 
zero     ≣ (succ n) = 𝟘 
(succ m) ≣ (succ n) = m ≣ n 

Reflℕ : ∀ n → n ≣ n
Reflℕ zero     = ⋆
Reflℕ (succ n) = IH
 -- Notice that we needed to inhabit the set ((succ m) ≣ (succ n))
 -- in this case, but we instead inhabited the set (m ≣ n) using IH.
 -- This works because, by definition, ((succ m) ≣ (succ n)) is (m ≣ n).
 where
  IH : n ≣ n
  IH = Reflℕ n

-- We next show that _≣_ is the least reflexive relation on ℕ:

weak-Jℕ : (A : ℕ → ℕ → Set) → (∀ n → A n n) →  ∀ m n → m ≣ n → A m n
weak-Jℕ A φ zero zero ⋆ = φ zero
weak-Jℕ A φ zero (succ n) ()
weak-Jℕ A φ (succ m) zero ()
weak-Jℕ A φ (succ m) (succ n) e = weak-Jℕ A' φ' m n e
 where
  A' : ℕ → ℕ → Set 
  A' m n = A (succ m) (succ n)
  φ' : ∀ n → A' n n
  φ' n = φ(succ n)

-- If you don't like "()" patterns (I don't), you can use the function
-- from-𝟘 (defined above using "()" patterns):

weak-Jℕ' : (A : ℕ → ℕ → Set) → (∀ n → A n n) →  ∀ m n → m ≣ n → A m n
weak-Jℕ' A φ zero     zero ⋆     = φ zero
weak-Jℕ' A φ zero    (succ n) e  = from-𝟘 e
weak-Jℕ' A φ (succ m) zero e     = from-𝟘 e
weak-Jℕ' A φ (succ m) (succ n) e = weak-Jℕ' (λ m n → A(succ m)(succ n))
                                             (λ n → φ(succ n))
                                             m n e

-- There is a stronger, dependent(ly typed) version of weak-Jℕ:

Jℕ : (A : (m n : ℕ) → m ≣ n → Set)

   → (∀ n → A n n (Reflℕ n)) →  ∀ m n → ∀(e : m ≣ n) → A m n e

Jℕ A φ zero     zero ⋆     = φ zero
Jℕ A φ zero    (succ n) ()
Jℕ A φ (succ m) zero ()
Jℕ A φ (succ m) (succ n) e = Jℕ (λ m n → A (succ m) (succ n))
                                 (λ n → φ(succ n))
                                 m n e

-- Of course we could have defined instead the weak version from the
-- strong one:

weak-Jℕ'' : (A : (m n : ℕ) → Set) → (∀ n → A n n) →  ∀ m n → m ≣ n → A m n
weak-Jℕ'' A = Jℕ (λ m n e → A m n) 

-- Jℕ can be regarded as an induction principle for equality on the
-- type ℕ. Several properties of ≣ can be proved using J without
-- reference to the inductive structure of the the type ℕ, and often
-- its weak version suffices.

symℕ : (x y : ℕ) → x ≣ y → y ≣ x
symℕ = weak-Jℕ A φ 
 where
  A : (x y : ℕ) → Set
  A x y = y ≣ x
  φ : (x : ℕ) → x ≣ x
  φ = Reflℕ

transℕ : (x y z : ℕ) → x ≣ y → y ≣ z → x ≣ z
transℕ x y z r s =  transℕ' x y r z s
 where
  transℕ' : (x y : ℕ) → x ≣ y → (z : ℕ) → y ≣ z → x ≣ z
  transℕ' = weak-Jℕ A φ
   where
    A : (x y : ℕ) → Set
    A x y = ∀(z : ℕ) → y ≣ z → x ≣ z
    φ : (x : ℕ) → A x x 
    φ x z s = s

substℕ : (P : ℕ → Set) → (x y : ℕ) → x ≣ y → P x → P y
substℕ P = weak-Jℕ A φ
 where
  A : (x y : ℕ) → Set
  A x y = P x → P y
  φ : (x : ℕ) → A x x 
  φ x p = p

-- Transitivity can be proved using substitution:

sym-transℕ : (x y z : ℕ) → x ≣ y → x ≣ z → y ≣ z
sym-transℕ x y z = rearrange z x y
 where
  rearrange : (z x y : ℕ) → x ≣ y → x ≣ z → y ≣ z
  rearrange z = substℕ (λ x → x ≣ z)

transℕ' : (x y z : ℕ) → x ≣ y → y ≣ z → x ≣ z
transℕ' x y z r s = sym-transℕ y x z (symℕ x y r) s

congℕ→ℕ : (f : ℕ → ℕ) → (x x' : ℕ) → x ≣ x' → f x ≣ f x'
congℕ→ℕ f = weak-Jℕ (λ x x' → f x ≣ f x') (λ x → Reflℕ(f x)) 

-- As another example, we show that addition is commutative:

zero-is-left-neutral : ∀ n → zero + n ≣ n 
zero-is-left-neutral zero = ⋆
zero-is-left-neutral (succ n) = IH  
             -- We need to inhabit the type (zero + succ n ≣ succ n). 
             -- Expanding the definitions,
             --   (zero + succ n ≣ succ n) = 
             --   (succ(zero + n) ≣ succ n) = 
             --   (zero + n ≣ n).
             -- Here "=" is definitional equality, silently applied by Agda.
 where
  IH : zero + n ≣ n
  IH = zero-is-left-neutral n

-- Equivalently:

zero-is-left-neutral' : ∀ n → zero + n ≣ n
zero-is-left-neutral' = induction base step
 where
  base : 𝟙
  base = ⋆
  step : ∀ n → zero + n ≣ n → zero + n ≣ n
  step n e = e

-- This with the following shows that, of course, it is equivalent to
-- define addition by induction on the first argument. The proof is by
-- induction on the second argument, following the definition of _+_.

addition-on-first : ∀ m n → (succ m) + n ≣ succ(m + n)
addition-on-first m zero = Reflℕ m
addition-on-first m (succ n) = IH
 where
  IH : succ m + n ≣ succ(m + n)
  IH = addition-on-first m n

-- Because the situation is symmetric, we can choose any of the two
-- arguments to perform the induction in the following theorem:

addition-commutative : ∀ m n → m + n ≣ n + m
addition-commutative zero n = zero-is-left-neutral n 
addition-commutative (succ m) n = lemma
 where
  IH : m + n ≣ n + m
  IH = addition-commutative m n
  claim : succ(m + n) ≣ succ(n + m)
  claim = congℕ→ℕ succ (m + n) (n + m) IH
  lemma : succ m + n ≣ succ (n + m)
  lemma = transℕ (succ m + n) (succ(m + n)) (succ (n + m)) 
                 (addition-on-first m n) claim


-- The above theorem "Jℕ" motivates Martin-Löf's inductive definition
-- of the identity type for any type X:

data _≡_ {X : Set} : X → X → Set where
 refl : {x : X} → x ≡ x

-- Martin-Löf's notation is the following:

Id : (X : Set) → X → X → Set
Id X x y  =  x ≡ y

Refl : (X : Set) → (x : X) → Id X x x
Refl X x = refl {X} {x}

-- The induction principle is as for equality on ℕ defined earlier:

J : {X : Set} → (A : (x x' : X) → x ≡ x' → Set)

   → (∀(x : X) → A x x refl) →  ∀{x x' : X} → ∀(r : x ≡ x') → A x x' r

J A f {x} refl = f x

-- The propositional "axiom of function extensionality" is

Extensionality : Set₁
Extensionality = 
 ∀(X Y : Set) → ∀(f g : X → Y) → (∀(x : X) → f x ≡ g x) → f ≡ g

-- This is not provable or disprovable.
