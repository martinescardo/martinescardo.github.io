Chuangjie Xu, 2012

\begin{code}

module Mini-library where


-- identity functions

id : {X : Set} → X → X
id x = x


-- Function composition

infixl 30 _∘_ 

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)


-- Subset relation

Subset : Set → Set₁
Subset X = X → Set

_∈_ : {X : Set} → X → Subset X → Set
x ∈ A = A x


-- Universe polymorphic sigma type

postulate
 Level : Set
 zer   : Level
 suc   : Level → Level
 max   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zer   #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  max   #-}


infixr 3 _,_

record Σ {i j : Level} {I : Set i} (X : I → Set j) : Set (max i j) where
  constructor _,_
  field
   π₀ : I
   π₁ : X π₀

π₀ : {i j : Level}{X : Set i}{Y : X → Set j} → 
     (Σ \(x : X) → Y x) → X
π₀ (x , y) = x

π₁ : {i j : Level}{X : Set i}{Y : X → Set j} → 
     (pair : Σ \(x : X) → Y x) → Y(π₀ pair)
π₁ (x , y) = y

infixr 20 _×_

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

infixr 20 _∧_

_∧_ : Set → Set → Set
X ∧ Y = Σ \(x : X) → Y

∧-elim₀ : {A₀ A₁ : Set} → A₀ ∧ A₁ → A₀
∧-elim₀ = π₀

∧-elim₁ : {A₀ A₁ : Set} → A₀ ∧ A₁ → A₁
∧-elim₁ = π₁

∧-intro : {A₀ A₁ : Set} → A₀ → A₁ → A₀ ∧ A₁
∧-intro a₀ a₁ = (a₀ , a₁)

∃ : {X : Set} → (A : X → Set) → Set 
∃ = Σ

∃-intro : {X : Set}{A : X → Set} → (x₀ : X) → A x₀ → ∃ \(x : X) → A x
∃-intro x a = (x , a)

∃-witness : {X : Set}{A : X → Set} → (∃ \(x : X) → A x) → X
∃-witness = π₀

∃-elim : {X : Set}{A : X → Set} → (proof : ∃ \(x : X) → A x) → A (∃-witness proof)
∃-elim = π₁


-- Identity type

infix  30 _≡_

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

subst : {X : Set}{Y : X → Set}{x x' : X} → x ≡ x' → Y x → Y x'
subst refl y = y

trans : {X : Set} → {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
trans refl refl = refl

sym : {X : Set} → {x y : X} → x ≡ y → y ≡ x
sym refl = refl

cong : {X Y : Set} → ∀(f : X → Y) → {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

fun-cong : {X Y : Set} → ∀{f g : X → Y} → f ≡ g → ∀(x : X) → f x ≡ g x
fun-cong r x = cong (λ h → h x) r

subst-refl : (A : Set) → (P : A → Set) → (a : A) → (p : P a) →
                 subst {A} {P} refl p ≡ p
subst-refl A P a p = refl

Lemma[subst] : (X : Set) → (P : X → Set) → (Q : (x : X) → P x → Set) →
                (x x' : X) → (eq : x ≡ x') → (p : P x) →
                  Q x p → Q x' (subst {X} {P} eq p)
Lemma[subst] X P Q x .x refl p q = q


-- Empty set

data ∅ : Set where

∅-elim : {A : Set} → ∅ → A
∅-elim = λ ()

¬ : Set → Set
¬ X = X → ∅

infix 30 _≠_
_≠_ : {A : Set} → A → A → Set
A ≠ B = ¬ (A ≡ B)


-- One-point set

data ⒈ : Set where
 ⋆ : ⒈

unit : {X : Set} → X → ⒈
unit x = ⋆

singleton : ∀(x x' : ⒈) → x ≡ x'
singleton ⋆ ⋆ = refl


-- Binary numbers, or booleans, and if-then function:

data ₂ : Set where
 ₀ : ₂
 ₁ : ₂

if : {X : Set} → X → X → ₂ → X
if x x' ₀ = x
if x x' ₁ = x'

-- Natural numbers and some operations on them:
   
data ℕ : Set where 
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-injective : ∀{i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-injective = cong pred

rec : {X : Set} → (X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f(rec f x n)

infixl 30 _+_

_+_ : ℕ → ℕ → ℕ
n + 0 = n
n + (succ m) = succ(n + m)

Lemma[0+m=m] : ∀(m : ℕ) → 0 + m ≡ m
Lemma[0+m=m] 0 = refl
Lemma[0+m=m] (succ m) = cong succ (Lemma[0+m=m] m)

Lemma[n+1+m=n+m+1] : ∀(n m : ℕ) → succ n + m ≡ n + succ m
Lemma[n+1+m=n+m+1] n 0 = refl
Lemma[n+1+m=n+m+1] n (succ m) = cong succ (Lemma[n+1+m=n+m+1] n m)

Lemma[n+m=m+n] : ∀(n m : ℕ) → n + m ≡ m + n
Lemma[n+m=m+n] n 0        = sym (Lemma[0+m=m] n)
Lemma[n+m=m+n] n (succ m) = trans (cong succ (Lemma[n+m=m+n] n m))
                                  (sym (Lemma[n+1+m=n+m+1] m n))


maximum : ℕ → ℕ → ℕ
maximum 0 m = m
maximum n 0 = n
maximum (succ n) (succ m) = succ (maximum n m)


-- Inequality

infix  30 _≤_
infix  30 _<_

data _≤_ : ℕ → ℕ → Set where
 ≤-zero : ∀{n : ℕ} → 0 ≤ n
 ≤-succ : ∀{m n : ℕ} → m ≤ n → succ m ≤ succ n

_<_ : ℕ → ℕ → Set
m < n = succ m ≤ n

Lemma[a≤b≤c→a≤c] : ∀{a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
Lemma[a≤b≤c→a≤c] ≤-zero _ = ≤-zero
Lemma[a≤b≤c→a≤c] (≤-succ r) (≤-succ l) = ≤-succ (Lemma[a≤b≤c→a≤c] r l)

Lemma[a<b≤c→a<c] : ∀{a b c : ℕ} → a < b → b ≤ c → a < c
Lemma[a<b≤c→a<c] = Lemma[a≤b≤c→a≤c]

Lemma[n≤n] : ∀(n : ℕ) → n ≤ n
Lemma[n≤n] 0        = ≤-zero
Lemma[n≤n] (succ n) = ≤-succ (Lemma[n≤n] n)

Lemma[n≤n+1] : ∀(n : ℕ) → n ≤ succ n
Lemma[n≤n+1] 0        = ≤-zero
Lemma[n≤n+1] (succ n) = ≤-succ (Lemma[n≤n+1] n)

Lemma[≤-max] : ∀(n m : ℕ) → (n ≤ maximum n m) ∧ (m ≤ maximum n m)
Lemma[≤-max] 0 0 = ∧-intro ≤-zero ≤-zero
Lemma[≤-max] 0 (succ m) = ∧-intro ≤-zero (≤-succ (∧-elim₁ (Lemma[≤-max] 0 m)))
Lemma[≤-max] (succ n) 0 = ∧-intro (Lemma[n≤n] (succ n)) ≤-zero
Lemma[≤-max] (succ n) (succ m) = ∧-intro (≤-succ (∧-elim₀ (Lemma[≤-max] n m))) (≤-succ (∧-elim₁ (Lemma[≤-max] n m)))

Lemma[a≤b→a+c≤b+c] : ∀(a b c : ℕ) → a ≤ b → a + c ≤ b + c
Lemma[a≤b→a+c≤b+c] a b 0        r = r
Lemma[a≤b→a+c≤b+c] a b (succ c) r = ≤-succ (Lemma[a≤b→a+c≤b+c] a b c r)

Lemma[a<b→a+c<b+c] : ∀(a b c : ℕ) → a < b → a + c < b + c
Lemma[a<b→a+c<b+c] a b c r = subst {ℕ} {λ n → n ≤ b + c} (lemma a c) (Lemma[a≤b→a+c≤b+c] (succ a) b c r)
 where
  lemma : ∀(n m : ℕ) → (succ n) + m ≡ succ (n + m)
  lemma n 0 = refl
  lemma n (succ m) = cong succ (lemma n m)

Lemma[a≤a+b] : ∀(a b : ℕ) → a ≤ a + b
Lemma[a≤a+b] a 0 = Lemma[n≤n] a
Lemma[a≤a+b] a (succ b) = Lemma[a≤b≤c→a≤c] (Lemma[a≤a+b] a b) (lemma (a + b))
 where
  lemma : ∀(c : ℕ) → c ≤ succ c
  lemma 0 = ≤-zero
  lemma (succ c) = ≤-succ (lemma c)

Lemma[b≤a+b] : ∀(a b : ℕ) → b ≤ a + b
Lemma[b≤a+b] a 0 = ≤-zero
Lemma[b≤a+b] a (succ b) = ≤-succ (Lemma[b≤a+b] a b)

Lemma[≤-∃] : ∀(a b : ℕ) → a ≤ b → ∃ \(c : ℕ) → a + c ≡ b
Lemma[≤-∃] 0 b ≤-zero = b , Lemma[0+m=m] b
Lemma[≤-∃] (succ a) 0 ()
Lemma[≤-∃] (succ a) (succ b) (≤-succ r) = c , trans (Lemma[n+1+m=n+m+1] a c) (cong succ eq)
 where
  c : ℕ
  c = π₀ (Lemma[≤-∃] a b r)
  eq : a + c ≡ b
  eq = π₁ (Lemma[≤-∃] a b r)

-- Cantor space

₂ℕ : Set
₂ℕ = ℕ → ₂

0̄ : ₂ℕ
0̄ i = ₀
1̄ : ₂ℕ
1̄ i = ₁


-- Vectors and finite sequences

infixr 50 _∷_

data Vec (X : Set) : ℕ → Set where
 ⟨⟩ : Vec X 0
 _∷_ : {n : ℕ} → X → Vec X n → Vec X (succ n)

head : {X : Set}{n : ℕ} → Vec X (succ n) → X
head (x ∷ _) = x

tail : {X : Set}{n : ℕ} → Vec X (succ n) → Vec X n
tail (_ ∷ xs) = xs

Lemma[Vec-≡] : ∀{n : ℕ}{X : Set} → ∀{v v' : Vec X (succ n)} →
                head v ≡ head v' → tail v ≡ tail v' → v ≡ v'
Lemma[Vec-≡] {n} {X} {x ∷ xs} {.x ∷ .xs} refl refl = refl

₂Fin : ℕ → Set
₂Fin = Vec ₂

⟨₀⟩ : ₂Fin 1
⟨₀⟩ = ₀ ∷ ⟨⟩
⟨₁⟩ : ₂Fin 1
⟨₁⟩ = ₁ ∷ ⟨⟩

take : (m : ℕ) → ₂ℕ → ₂Fin m
take 0 α = ⟨⟩
take (succ n) α = α 0 ∷ take n (α ∘ succ)

drop : (m : ℕ) → ₂ℕ → ₂ℕ
drop 0 α = α
drop (succ m) α = drop m (α ∘ succ)

isomorphism-₂Fin : ∀(X : Set) → ∀(n : ℕ) → (f : ₂Fin (succ n) → X) →
                    ∃ \(g : ₂ → ₂Fin n → X) →
                     ∀(s : ₂Fin (succ n)) → f s ≡ g (head s) (tail s)
isomorphism-₂Fin X n f = ∃-intro g prf
 where
  g : ₂ → ₂Fin n → X
  g b s = f (b ∷ s)
  prf : ∀(s : ₂Fin (succ n)) → f s ≡ g (head s) (tail s)
  prf (b ∷ s) = refl

max-fin : {n : ℕ} → (f : ₂Fin n → ℕ) →
           ∃ \(m : ℕ) → ∀(s : ₂Fin n) → f s ≤ m
max-fin {0} f = ∃-intro (f ⟨⟩) prf
 where
  prf : ∀(s : ₂Fin 0) → f s ≤ f ⟨⟩
  prf ⟨⟩ = Lemma[n≤n] (f ⟨⟩)
max-fin {succ n} f = ∃-intro m prf
 where
  g : ₂ → ₂Fin n → ℕ
  g = ∃-witness (isomorphism-₂Fin ℕ n f)
  m₀ : ℕ
  m₀ = ∃-witness (max-fin (g ₀))
  prf₀ : ∀(s : ₂Fin n) → g ₀ s ≤ m₀
  prf₀ = ∃-elim (max-fin (g ₀))
  m₁ : ℕ
  m₁ = ∃-witness (max-fin (g ₁))
  prf₁ : ∀(s : ₂Fin n) → g ₁ s ≤ m₁
  prf₁ = ∃-elim (max-fin (g ₁))
  m : ℕ
  m = maximum m₀ m₁
  prf : ∀(s : ₂Fin (succ n)) → f s ≤ m
  prf (₀ ∷ s) = Lemma[a≤b≤c→a≤c] (prf₀ s) (∧-elim₀ (Lemma[≤-max] m₀ m₁))
  prf (₁ ∷ s) = Lemma[a≤b≤c→a≤c] (prf₁ s) (∧-elim₁ (Lemma[≤-max] m₀ m₁))


-- disjoint union

infixr 20 _⊎_
infixr 20 _∨_

data _⊎_ (X₀ X₁ : Set) : Set where
  in₀ : X₀ → X₀ ⊎ X₁
  in₁ : X₁ → X₀ ⊎ X₁

_∨_ : Set → Set → Set
_∨_ = _⊎_

case : {X₀ X₁ Y : Set} → (X₀ → Y) → (X₁ → Y) → X₀ ∨ X₁ → Y
case f₀ f₁ (in₀ x₀) = f₀ x₀
case f₀ f₁ (in₁ x₁) = f₁ x₁

equality-cases : {X₀ X₁ : Set} → {A : Set} → 
    ∀(y : X₀ ∨ X₁) → (∀ x₀ → y ≡ in₀ x₀ → A) → (∀ x₁ → y ≡ in₁ x₁ → A) → A
equality-cases (in₀ x₀) f₀ f₁ = f₀ x₀ refl
equality-cases (in₁ x₁) f₀ f₁ = f₁ x₁ refl

cases : {X₀ X₁ Y₀ Y₁ : Set} → (X₀ → Y₀) → (X₁ → Y₁) → X₀ ∨ X₁ → Y₀ ∨ Y₁
cases f₀ f₁ (in₀ x₀) = in₀ (f₀ x₀)
cases f₀ f₁ (in₁ x₁) = in₁ (f₁ x₁)

Lemma[⊎] : {X₀ X₁ : Set} → (x : X₀ ⊎ X₁) →
             (∃ \(x₀ : X₀) → x ≡ in₀ x₀) ∨ (∃ \(x₁ : X₁) → x ≡ in₁ x₁)
Lemma[⊎] (in₀ x₀) = in₀ (x₀ , refl)
Lemma[⊎] (in₁ x₁) = in₁ (x₁ , refl)


decidable : Set → Set
decidable A = A ∨ (¬ A)

ℕ-discrete : ∀(n m : ℕ) → decidable (n ≡ m)
ℕ-discrete 0 0 = in₀ refl
ℕ-discrete 0 (succ m) = in₁ (λ ())
ℕ-discrete (succ n) 0 = in₁ (λ ())
ℕ-discrete (succ n) (succ m) = step (ℕ-discrete n m)
 where 
  step : decidable(n ≡ m) → decidable (succ n ≡ succ m) 
  step (in₀ r) = in₀ (cong succ r)
  step (in₁ f) = in₁ (λ s → f (succ-injective s))

₂-discrete : ∀(b : ₂) → b ≡ ₀ ∨ b ≡ ₁
₂-discrete ₀ = in₀ refl
₂-discrete ₁ = in₁ refl


Lemma[a≠b→a<b∨b<a] : ∀(a b : ℕ) → ¬ (a ≡ b) → a < b ∨ b < a
Lemma[a≠b→a<b∨b<a] 0        0        f = ∅-elim (f refl)
Lemma[a≠b→a<b∨b<a] 0        (succ b) f = in₀ (≤-succ ≤-zero)
Lemma[a≠b→a<b∨b<a] (succ a) 0        f = in₁ (≤-succ ≤-zero)
Lemma[a≠b→a<b∨b<a] (succ a) (succ b) f = cases ≤-succ ≤-succ IH
 where
  f' : ¬ (a ≡ b)
  f' e = f (cong succ e)
  IH : a < b ∨ b < a
  IH = Lemma[a≠b→a<b∨b<a] a b f'

\end{code}
