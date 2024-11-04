\begin{code}

{-# OPTIONS --without-K #-}

module tiny-library where

Type = Set 
U = Type

_∘_ : {X Y : Type} {Z : Y → Type} → ((y : Y) → Z y) → (f : X → Y) → (x : X) → Z(f x)
g ∘ f = λ x → g(f x)

data _+_ (X₀ X₁ : Type) : Type where
 in₀ : X₀ → X₀ + X₁
 in₁ : X₁ → X₀ + X₁

record Σ {I : Type} (X : I → Type) : Type where
  constructor _,_
  field
   π₀ : I
   π₁ : X π₀

open Σ public

_×_ : Type → Type → Type
X × Y = Σ \(x : X) → Y

data ₂ : Type where
 ₀ : ₂
 ₁ : ₂

data _≡_ {X : Type} (x : X) : X → Type where
 refl : x ≡ x



J : {X : Type} → (A : (x x' : X) → x ≡ x' → Type)
   → ((x : X) → A x x refl)
   →  {x x' : X} (r : x ≡ x') → A x x' r
J A f {x} refl = f x

J' : {X : Type} (A : {x y : X} → x ≡ y → Type)
   → ({x : X} → A (refl {X} {x})) → {x y : X} (p : x ≡ y) → A p
J' {X} A φ = J {X} (λ x y p → A {x} {y} p) (λ x → φ {x})

transport : {X : Type} {P : X → Type} {x y : X} → x ≡ y → P x → P y
transport {X} {P} refl p = p

ap : {X Y : Type} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
ap f refl = refl

id : {X : Type} → X → X
id x = x

ap-id-is-id : {X : Set} {x y : X} (p : x ≡ y) → p ≡ ap id p
ap-id-is-id refl = refl

ap-functorial : {X Y Z : Type} (f : X → Y) (g : Y → Z) {x₀ x₁ : X} → (p : x₀ ≡ x₁) 
                → ap g (ap f p) ≡ ap (g ∘ f) p
ap-functorial f g refl = refl

apd : {X : Type} {Y : X → Type} (f : (x : X) → Y x) {x x' : X} (p : x ≡ x') → transport p (f x) ≡ f x'
apd f refl = refl 

undo'-Σ-≡ : {X : Type} {Y : X → Type} (w w' : Σ \(x : X) → Y x) 
     → w ≡ w' → Σ \(p : π₀ w ≡ π₀ w') → transport {X} {Y} p (π₁ w) ≡ π₁ w'
undo'-Σ-≡  w .w refl = refl , refl

undo-Σ-≡ : {X : Type} {Y : X → Type} (x x' : X) (y : Y x) (y' : Y x')
     → (_≡_ {Σ \x → Y x} (x , y) (x' , y')) → Σ \(p : x ≡ x') → transport p y ≡ y'
undo-Σ-≡  x x' y y' = undo'-Σ-≡ ((x , y)) (x' , y')

Σ-≡ : {X : Type} {Y : X → Type} (x x' : X) (y : Y x) (y' : Y x')
     → (p : x ≡ x') → transport p y ≡ y' → _≡_ {Σ \x → Y x} (x , y) (x' , y') 
Σ-≡ .x' x' .y y refl refl = refl

_•_ : {X : Type} → {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
refl • p = p

_⁻¹ : {X : Type} → {x y : X} → x ≡ y → y ≡ x
_⁻¹ refl = refl

sym-is-inverse : {X : Type} {x y : X} (p : x ≡ y) → refl ≡ p ⁻¹ • p
sym-is-inverse refl = refl

refl-is-right-id : {X : Type} {x y : X} (p : x ≡ y) → p ≡ p • refl
refl-is-right-id refl = refl

transport-sym : {X : Type} {x y : X} (p : x ≡ y) → transport {X} {λ x → x ≡ y} (p ⁻¹) refl ≡ p
transport-sym refl = refl

transport-sym' : {X : Type} {x y : X} (p : x ≡ y) → transport {X} {λ y → y ≡ x} p (refl {X} {x}) ≡ p ⁻¹
transport-sym' refl = refl

transport-paths-along-paths : {X Y : Type} {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x) 
                            → transport {X} {λ z → h z ≡ k z} p q ≡ (ap h p)⁻¹ • q • (ap k p)
transport-paths-along-paths refl h k q = refl-is-right-id q

transport-paths-along-paths' : {X : Type} {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x) 
                             → transport {X} {λ z → z ≡ f z} p q ≡ p ⁻¹ • q • (ap f p)
transport-paths-along-paths' {X} {x} p f q = 
 (transport-paths-along-paths p (λ z → z) f q) • (ap (λ pr → pr ⁻¹ • q • (ap f p)) ((ap-id-is-id p)⁻¹))

hprop : Type → Type
hprop X = (x y : X) → x ≡ y

hset : Type → Type
hset X = (x y : X) → hprop(x ≡ y)

contractible : Type → Type
contractible X = Σ \(x : X) → (y : X) → x ≡ y

paths-from : {X : Type} (x : X) → Type
paths-from {X} x = Σ \(y : X) → x ≡ y

end-point : {X : Type} {x : X} → paths-from x → X
end-point = π₀ 

trivial-loop : {X : Type} (x : X) → paths-from x
trivial-loop x = (x , refl)

path-from-trivial-loop : {X : Type} {x x' : X} (r : x ≡ x') → trivial-loop x ≡ (x' , r)
path-from-trivial-loop {X} = J {X} A (λ x → refl)
 where 
  A : (x x' : X) → x ≡ x' → Type
  A x x' r = _≡_ {Σ \(x' : X) → x ≡ x'} (trivial-loop x) (x' , r) 

paths-from-is-contractible : {X : Type} (x₀ : X) → contractible(paths-from x₀)
paths-from-is-contractible x₀ = trivial-loop x₀ , (λ t → path-from-trivial-loop (π₁ t))

contractible-is-hprop : {X : Type} → contractible X → hprop X
contractible-is-hprop (x , f) y z = (f y)⁻¹ • f z

paths-from-is-hprop : {X : Type} (x : X) → hprop(paths-from x)
paths-from-is-hprop x = contractible-is-hprop (paths-from-is-contractible x)

constant : {X Y : Type} → (X → Y) → Type
constant {X} {Y} f = (x y : X) → f x ≡ f y

collapsible : Type → Type
collapsible X = Σ \(f : X → X) → constant f

path-collapsible : Type → Type
path-collapsible X = {x y : X} → collapsible(x ≡ y)

path-collapsible-is-hset : {X : Type} → path-collapsible X → hset X
path-collapsible-is-hset {X} pc _ _ p q = claim₂
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f = π₀ pc
  g : {x y : X} (p q : x ≡ y) → f p ≡ f q
  g = π₁ pc
  claim₀ : {x y : X} (r : x ≡ y) → r ≡ (f refl)⁻¹ • f r
  claim₀ = J' (λ r → r ≡ (f refl)⁻¹ • f r) (sym-is-inverse(f refl))
  claim₁ : (f refl)⁻¹ • f p ≡ (f refl)⁻¹ • f q
  claim₁ = ap (λ h → (f refl)⁻¹ • h) (g p q)
  claim₂ : p ≡ q
  claim₂ = claim₀ p • claim₁ • (claim₀ q)⁻¹

hprop-is-path-collapsible : {X : Type} → hprop X → path-collapsible X
hprop-is-path-collapsible h {x} {y} = ((λ p → h x y) , (λ p q → refl))

hprop-is-hset : {X : Type} → hprop X → hset X
hprop-is-hset h = path-collapsible-is-hset(hprop-is-path-collapsible h)

paths-from-is-hset : {X : Type} (x : X) → hset(paths-from x)
paths-from-is-hset x = hprop-is-hset (paths-from-is-hprop x)

data ∅ : Type where
 -- no cases

∅-rec : {X : Type} → ∅ → X
∅-rec ()

empty : Type → Type
empty X = X → ∅

decidable : Type → Type
decidable X = X + empty X

inhabited-is-collapsible : {X : Type} → X → collapsible X
inhabited-is-collapsible x = ((λ y → x) , λ y y' → refl)

empty-is-collapsible : {X : Type} → empty X → collapsible X
empty-is-collapsible u = ((λ x → x) , (λ x x' → ∅-rec(u x)))

decidable-is-collapsible : {X : Type} → decidable X → collapsible X
decidable-is-collapsible (in₀ x) = inhabited-is-collapsible x
decidable-is-collapsible (in₁ u) = empty-is-collapsible u

discrete : Type → Type
discrete X = {x y : X} → decidable(x ≡ y)

discrete-is-path-collapsible : {X : Type} → discrete X → path-collapsible X
discrete-is-path-collapsible d = decidable-is-collapsible d

discrete-is-hset : {X : Type} → discrete X → hset X
discrete-is-hset d = path-collapsible-is-hset(discrete-is-path-collapsible d)

₂-discrete : discrete ₂
₂-discrete {₀} {₀} = in₀ refl
₂-discrete {₀} {₁} = in₁ (λ ())
₂-discrete {₁} {₀} = in₁ (λ ())
₂-discrete {₁} {₁} = in₀ refl

₂-hset : hset ₂
₂-hset = discrete-is-hset ₂-discrete

infixr 2 _≡_
infixr 1 _+_
infixr 1 _,_
infixl 3 _∘_ 
infixl 3 _•_ 

\end{code}
