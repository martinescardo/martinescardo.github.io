{-# OPTIONS --without-K #-}

module vectors where

data _≡_ {X : Set} : X → X → Set where
 refl : {x : X} → x ≡ x

sym : {A : Set} {a₀ a₁ : A} → a₀ ≡ a₁ → a₁ ≡ a₀
sym refl = refl

trans : {A : Set} {a₀ a₁ a₂ : A} → a₀ ≡ a₁ → a₁ ≡ a₂ → a₀ ≡ a₂
trans refl p = p

cong : {X Y : Set} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + y = y
succ x + y = succ(x + y)

+-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
+-assoc zero     m n = refl
+-assoc (succ l) m n = goal
 where
  IH : (l + m) + n ≡ l + (m + n)
  IH = +-assoc l m n
  goal : succ ((l + m) + n) ≡ succ (l + (m + n))
  goal = cong succ IH

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

_++_ : ∀{X} → List X → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {X} (xs ys zs : List X)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = goal
 where
  IH : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  IH = ++-assoc xs ys zs
  goal : x ∷ ((xs ++ ys) ++ zs)  ≡  x ∷ (xs ++ (ys ++ zs))
  goal = cong (λ ws → x ∷ ws) IH

data Vec (X : Set) : ℕ → Set where
  []  : Vec X zero
  _∷_ : ∀{n} → X → Vec X n → Vec X (succ n)

hd : {X : Set} {n : ℕ} → Vec X (succ n) → X
hd (x ∷ xs) = x

tl : {X : Set} {n : ℕ} → Vec X (succ n) → Vec X n
tl (x ∷ xs) = xs

data Fin : ℕ → Set where
 zero : {n : ℕ} → Fin (succ n)
 succ : {n : ℕ} → Fin n → Fin (succ n)

fetch : ∀ {X} n → Vec X n → Fin n → X
fetch n        (x ∷ xs)  zero    = x
fetch (succ n) (x ∷ xs) (succ i) = fetch n xs i

_+++_ : ∀{X m n} → Vec X m → Vec X n → Vec X (m + n)
[]       +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)

_≡[_]_ : ∀{X m n} → Vec X m → m ≡ n → Vec X n → Set
xs ≡[ refl ] ys   =   xs ≡ ys

cong-cons : ∀{X m n} (x : X) {xs : Vec X m} {ys : Vec X n} (p : m ≡ n)
          → xs ≡[ p ] ys → x ∷ xs  ≡[ cong succ p ]  x ∷ ys
cong-cons _ refl refl = refl 


+++-assoc : ∀{X} l m n (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
         → (xs +++ ys) +++ zs  ≡[ +-assoc l m n ]  xs +++ (ys +++ zs)
+++-assoc zero     m n []       ys zs = refl
+++-assoc (succ l) m n (x ∷ xs) ys zs = goal
 where
  IH : (xs +++ ys) +++ zs  ≡[ +-assoc l m n ]  xs +++ (ys +++ zs)
  IH = +++-assoc l m n xs ys zs
  goal : x ∷ ((xs +++ ys) +++ zs)  ≡[ cong succ (+-assoc l m n) ]
         x ∷ (xs +++ (ys +++ zs))
  goal = cong-cons x (+-assoc l m n) IH

zrn : ∀ n → n + zero ≡ n
zrn zero = refl
zrn (succ n) = cong succ (zrn n)

ern : ∀ {X} n (xs : Vec X n)
   → xs +++ [] ≡[ zrn n ] xs
ern zero [] = refl
ern (succ n) (x ∷ xs) = cong-cons x (zrn n) (ern n xs)

module _ 
  (A : Set)
  (B : A → Set)
 where
  _≡⟦_⟧_ : {a₀ a₁ : A} → B a₀ → a₀ ≡ a₁ → B a₁ → Set
  b₀ ≡⟦ refl ⟧ b₁   =   b₀ ≡ b₁

  congd : (f : (a : A) → B a) {a₀ a₁ : A}
        → (p : a₀ ≡ a₁) → f a₀ ≡⟦ p ⟧ f a₁
  congd f refl = refl

  transport : {a₀ a₁ : A} → a₀ ≡ a₁ → B a₀ → B a₁
  transport refl b₀ = b₀

  exercise-subst-iso₀ : {a₀ a₁ : A} (p : a₀ ≡ a₁) (b₀ : B a₀)
                      → transport (sym p) (transport p b₀)  ≡ b₀
  exercise-subst-iso₀ refl b₀ = refl

  exercise-subst-iso₁ : {a₀ a₁ : A} (p : a₀ ≡ a₁) (b₁ : B a₁) 
                      → transport p (transport (sym p) b₁)  ≡ b₁
  exercise-subst-iso₁ refl b₁ = refl

  _≡'⟦_⟧_ : {a₀ a₁ : A} → B a₀ → a₀ ≡ a₁ → B a₁ → Set
  b₀ ≡'⟦ p ⟧ b₁   =   transport p b₀ ≡ b₁
  
  φ : {a₀ a₁ : A} {b₀ : B a₀} {p : a₀ ≡ a₁} {b₁ : B a₁}
    → b₀ ≡⟦ p ⟧ b₁ → b₀ ≡'⟦ p ⟧ b₁  
  φ {a₀} {.a₀} {b₀} {refl} refl = refl

  ψ : {a₀ a₁ : A} {b₀ : B a₀} {p : a₀ ≡ a₁} {b₁ : B a₁}
    → b₀ ≡'⟦ p ⟧ b₁ → b₀ ≡⟦ p ⟧ b₁  
  ψ {a₀} {.a₀} {b₀} {refl} refl = refl

  φψid : {a₀ a₁ : A} {b₀ : B a₀} {p : a₀ ≡ a₁} {b₁ : B a₁} (q : b₀ ≡'⟦ p ⟧ b₁)
       → φ {a₀} {a₁} {b₀} {p} (ψ q) ≡ q
  φψid {a₀} {.a₀} {b₀} {refl} refl = refl

  ψφid : {a₀ a₁ : A} {b₀ : B a₀} {p : a₀ ≡ a₁} {b₁ : B a₁} (q : b₀ ≡⟦ p ⟧ b₁)
       → ψ(φ q) ≡ q
  ψφid {a₀} {.a₀} {b₀} {refl} refl = refl

_≡'[_]_ : ∀{X m n} → Vec X m → m ≡ n → Vec X n → Set
xs ≡'[ p ] ys   =   _≡'⟦_⟧_ ℕ (Vec _) xs p ys

-- 
cong-cons' : ∀{X m n} (x : X) {xs : Vec X m} {ys : Vec X n} (p : m ≡ n)
          → xs ≡'[ p ] ys → x ∷ xs  ≡'[ cong succ p ]  x ∷ ys
cong-cons' _ refl refl = refl 

+++-assoc' : ∀{X} l m n (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
         → (xs +++ ys) +++ zs  ≡'[ +-assoc l m n ]  xs +++ (ys +++ zs)
+++-assoc' zero     m n []       ys zs = refl
+++-assoc' (succ l) m n (x ∷ xs) ys zs = goal
 where
  IH : (xs +++ ys) +++ zs  ≡'[ +-assoc l m n ]  xs +++ (ys +++ zs)
  IH = +++-assoc' l m n xs ys zs
  goal : x ∷ ((xs +++ ys) +++ zs)  ≡'[ cong succ (+-assoc l m n) ]
         x ∷ (xs +++ (ys +++ zs))
  goal = cong-cons' x (+-assoc l m n) IH


-- Exercise.  We will prove that the two types Vec X n and (Fin n → X)
-- are isomorphic for all X and n. Thus, we can use this function type
-- as a representation for vectors, and we start with this idea.

Vec' : Set → ℕ → Set
Vec' X n = Fin n → X

-- We will xs',ys',zs' etc. for elements of the type Vec' X n,
-- i.e. functions Fin n → X.

-- To get you started, I will first solve an exercise myself: Using
-- this representation for vectors define functions _∶∶'_ , hd', tl'
-- and fetch', corresponding to those of the original definition of
-- Vectors.

_∷'_ : ∀{X n} → X → Vec' X n → Vec' X (succ n)
(x ∷' xs')  zero    = x
(x ∷' xs') (succ n) = xs' n

hd' : {X : Set} {n : ℕ} → Vec' X (succ n) → X
hd' xs' = xs' zero

tl' : {X : Set} {n : ℕ} → Vec' X (succ n) → Vec' X n
tl' xs' = λ i → xs'(succ i)

fetch' : ∀ {X} n → Vec' X n → Fin n → X
fetch' _ xs' = xs'

-- We have a function fetch : ∀ {X n} → Vec X n → Fin n → X, whose
-- type can be rewritten as follows, with the parameter n made
-- explicit for convenience:

forth : ∀ {X} n → Vec X n → Vec' X n
forth = fetch 

-- Exercise. Define a function back in the other direction. (Hint: you
-- will need to do induction on the implicit argument n.)

back : ∀ {X} n → Vec' X n → Vec X n
back (zero)    _  = []
back (succ n) xs' = hd' xs' ∷ back n (tl' xs') 

-- Exercise. Prove that tyhe functions (forth n) and (back n) are
-- mutually inverse, and hence conclude that Vec X n and Vec' n X are
-- isomorphic types.

bfid : ∀ {X} n (xs : Vec X n) → back n (forth n xs) ≡ xs
bfid  zero     []      = refl
bfid (succ n) (x ∷ xs) = cong (λ ws → x ∷ ws) IH
 where
  IH : back n (fetch n xs) ≡ xs
  IH = bfid n xs

-- It will be difficult to prove the other direction, namely that
-- forth n (back n xs') ≡ xs', because this is an equality of two
-- functions of type Fin n → X.

-fbid : ∀ {X} n (xs' : Vec' X n) (i : Fin n) → forth n (back n xs') i ≡ xs' i
-fbid zero xs' ()
-fbid (succ n) xs' zero = refl
-fbid (succ n) xs' (succ i) = IH
 where
  IH : forth n (back n (tl' xs')) i ≡ tl' xs' i
  IH = -fbid n (tl' xs') i

FunExt : Set₁
FunExt = (X Y : Set) (f g : X → Y)
       → ((x : X) → f x ≡ g x) → f ≡ g

-- Function extensionality says that if two functions have equal
-- values then they are equal. This cannot be proved in Agda. But it
-- is consistent, and we will use it as an assumpion.

fbid : FunExt → ∀ {X} n (xs' : Vec' X n) → forth n (back n xs') ≡ xs'
fbid funext {X} n xs' = goal
 where
  f g : Fin n → X
  f = fetch n (back n xs')
  g = xs'
  have-same-values : (x : Fin n) → f x ≡ g x
  have-same-values = -fbid n xs'
  goal : f ≡ g
  goal = funext (Fin n) X f g have-same-values


-- Define vector concatenation using the representation Vec' X n
-- indirectly, by appealing to the isomorphism.

-- Define vector concatenation using the representation Vec' X n
-- directly, without using the isomorphism.

-- Formulate and prove associativity of vector concatenation using a
  -- suitable incarnation of dependent equality.


-- The following dependent version of function extensionality is also consistent:
DepFunExt : Set₁
DepFunExt = (X : Set) (Y : X → Set) (f g : (x : X) → (Y x))
       → ((x : X) → f x ≡ g x) → f ≡ g

-- Another isomorphism. A vector of length n is nothing but a list of
-- length n.

length : {X : Set} → List X → ℕ
length [] = zero
length (x ∷ xs) = succ (length xs)

record Vec'' (X : Set) (n : ℕ) : Set where
  constructor vec
  field
    list : List X
    eql  : length list ≡ n

open Vec'' public

[]'' : ∀{X} → Vec'' X zero
[]'' = vec [] refl

_∷''_ : ∀{X n} → X → Vec'' X n → Vec'' X (succ n)
x ∷'' vec xs refl = vec (x ∷ xs) refl

hd'' : {X : Set} {n : ℕ} → Vec'' X (succ n) → X
hd'' (vec [] ())
hd'' (vec (x ∷ xs) refl) = x 

tl'' : {X : Set} {n : ℕ} → Vec'' X (succ n) → Vec'' X n
tl'' (vec [] ())
tl'' (vec (x ∷ xs) refl) = vec xs refl

forth' : ∀ {X} n → Vec X n → Vec'' X n
forth' zero [] = []''
forth' (succ n) (x ∷ xs) = x ∷'' forth' n xs

back' : ∀ {X} n → Vec'' X n → Vec X n
back' (zero)    _  = []
back' (succ n) xs'' = hd'' xs'' ∷ back' n (tl'' xs'') 

hd''-lemma : ∀ {X n} (x : X) (xs'' : Vec'' X n) → hd'' (x ∷'' xs'') ≡ x
hd''-lemma x (vec xs refl) = refl

tl''-lemma : ∀ {X n} (x : X) (xs'' : Vec'' X n) → tl'' (x ∷'' xs'') ≡ xs''
tl''-lemma x (vec xs refl) = refl


bfid' : ∀ {X} n (xs : Vec X n) → back' n (forth' n xs) ≡ xs
bfid' zero [] = refl
bfid' {X} (succ n) (x ∷ xs) = goal
 where
  IH : back' n (forth' n xs) ≡ xs
  IH = bfid' n xs
  a : x ∷ back' n (forth' n xs) ≡ x ∷ xs
  a = cong (λ ws → x ∷ ws) IH
  lhs : Vec X (succ n)
  lhs = hd'' (x ∷'' forth' n xs) ∷ back' n (tl'' (x ∷'' forth' n xs))
  b : hd'' (x ∷'' forth' n xs) ∷ back' n (forth' n xs) ≡ x ∷ back' n (forth' n xs)
  b = cong (λ y → y ∷ back' n (forth' n xs)) (hd''-lemma x (forth' n xs))
  c : lhs ≡ hd'' (x ∷'' forth' n xs) ∷ back' n (forth' n xs)
  c = cong (λ y → hd'' (x ∷'' forth' n xs) ∷ back' n y)(tl''-lemma x (forth' n xs))
  goal : lhs ≡ x ∷ xs
  goal = trans c (trans b a)

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

succ-injective : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-injective = cong pred

fbid' : ∀ {X} n (xs'' : Vec'' X n) → forth' n (back' n xs'') ≡ xs''
fbid' zero (vec [] refl) = refl
fbid' zero (vec (x ∷ xs) ())
fbid' (succ n) (vec [] ())
fbid' {X} (succ n) (vec (x ∷ xs) (refl {.(succ n)})) = {!goal!}
 where
  IH : forth' n (back' n (vec xs refl)) ≡ vec xs refl
  IH = fbid' n (vec xs refl)
  f : Vec'' X (length xs) → Vec'' X (succ (length xs))
  f xs'' = x ∷'' xs''
  goal : (x ∷'' forth' n (back' n (vec xs refl)))
      ≡ vec (x ∷ xs) refl
  goal = cong f IH

-- failed attempts:
-forth' : ∀ {X} n → Vec X n → Vec'' X n
-forth' zero [] = []''
-forth' (succ n) (x ∷ xs) = vec (x ∷ list IH) (cong succ (eql IH))
 where
   IH : Vec'' _ n
   IH = -forth' n xs

{- -forth' : ∀ {X} n → Vec X n → Vec'' X n
-forth' zero [] = vec [] refl
-forth' (succ n) (x ∷ xs) = vec (x ∷ list (forth' n xs)) (cong succ (eql (forth' n xs))) -}

+back' : ∀ {X} n → Vec'' X n → Vec X n
+back' zero (vec [] refl) = []
+back' zero (vec (x ∷ xs) ())
+back' (succ n) (vec [] ())
+back' (succ .(length xs)) (vec (x ∷ xs) refl) = x ∷ +back' (length xs) (vec xs refl)

+bfid' : ∀ {X} n (xs : Vec X n) → back' n (forth' n xs) ≡ xs
+bfid' zero [] = refl
+bfid' (succ n) (x ∷ xs) = {!!}
 where
  IH : back' n (forth' n xs) ≡ xs
  IH = +bfid' n xs
  IH' : x ∷ back' n (forth' n xs) ≡ x ∷ xs
  IH' = cong (λ ws → x ∷ ws) IH

  goal : back' (succ n) (vec (x ∷ list (forth' n xs)) (cong succ (eql (forth' n xs))))
      ≡ x ∷ xs
  goal = {!IH'!}

-back' : ∀ {X} n → Vec'' X n → Vec X n
-back' zero (vec [] e) = []
-back' (succ n) (vec [] ())
-back' zero (vec (x ∷ xs) ())
-back' (succ n) (vec (x ∷ xs) e) = x ∷ -back' n (vec xs (succ-injective e))

-bfid' : ∀ {X} n (xs : Vec X n) → -back' n (forth' n xs) ≡ xs
-bfid' zero [] = refl
-bfid' (succ n) (x ∷ xs) = {!!}
 where
   IH : -back' n (forth' n xs) ≡ xs
   IH = -bfid' n xs
   goal : {!!}
   goal = {!!}



infixr 5 _≡_
infixr 5 _≡[_]_
infixr 5 _≡'[_]_
infixl 6 _+_
infixl 6 _++_
infixl 6 _+++_
infixr 7 _∷_
