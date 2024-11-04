-- Martin Escardo, 3rd August 2015

{-# OPTIONS --without-K #-}

module isprop where

open import preliminaries

-- A proposition is a type with at most one element:

isProp : {i : Level} → Type i → Type i
isProp X = (x y : X) → x ≡ y

-- The two canonical examples:

𝟘-isProp : isProp 𝟘
𝟘-isProp () ()

𝟙-isProp : isProp 𝟙
𝟙-isProp zero zero = refl zero

isSet : {i : Level} → Type i → Type i
isSet X = {x y : X} → isProp(x ≡ y)

constant : {i j : Level} {X : Type i} {Y : Type j} → (f : X → Y) → Type (i ⊔ j)
constant f = ∀ x y → f x ≡ f y

collapsible : {i : Level} → Type i → Type i
collapsible X = Σ \(f : X → X) → constant f

path-collapsible : {i : Level} → Type i → Type i
path-collapsible X = {x y : X} → collapsible(x ≡ y)

isSet-is-path-collapsible : {i : Level} {X : Type i} → isSet X → path-collapsible X
isSet-is-path-collapsible u = (λ p → p) , u 

path-collapsible-isSet : {i : Level} {X : Type i} → path-collapsible X → isSet X
path-collapsible-isSet {i} {X} pc {x} {y} p q = claim₂
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f = pr₁ pc
  g : {x y : X} (p q : x ≡ y) → f p ≡ f q
  g = pr₂ pc
  claim₀ : {x y : X} (r : x ≡ y) → r ≡ trans (sym(f (refl x))) (f r)
  claim₀ (refl x) = sym-is-inverse (f(refl x)) 
  claim₁ : trans (sym (f (refl x))) (f p) ≡ trans (sym(f (refl x))) (f q)
  claim₁ = ap (λ h → trans (sym(f (refl x))) h) (g p q) 
  claim₂ : p ≡ q
  claim₂ = trans (trans (claim₀ p) claim₁) (sym(claim₀ q)) 

prop-is-path-collapsible : {i : Level} {X : Type i} → isProp X → path-collapsible X
prop-is-path-collapsible h {x} {y} = ((λ p → h x y) , (λ p q → refl(h x y)))

prop-is-set : {i : Level} {X : Type i} → isProp X → isSet X
prop-is-set h = path-collapsible-isSet(prop-is-path-collapsible h)

isProp-isProp : {i : Level} {X : Type i} → isProp(isProp X)
isProp-isProp {i} {X} f g = claim₁
 where
  open import funext
  lemma : isSet X
  lemma = prop-is-set f
  claim : (x y : X) → f x y ≡ g x y
  claim x y = lemma (f x y) (g x y)
  claim₀ : (x : X) → f x ≡ g x 
  claim₀ x = funext (claim x)
  claim₁ : f ≡ g
  claim₁  = funext claim₀

isProp-closed-under-Σ : {i j : Level} {X : Type i} {A : X → Type j} 
                    → isProp X → ((x : X) → isProp(A x)) → isProp(Σ A)
isProp-closed-under-Σ {i} {j} {X} {A} isx isa (x , a) (y , b) = Σ-≡ (isx x y) (isa y (transport A (isx x y) a) b)

isProp-exponential-ideal : {i j : Level} {X : Type i} {A : X → Type j} 
                        → ((x : X) → isProp(A x)) → isProp(Π A) 
isProp-exponential-ideal {i} {j} {X} {A} isa = lemma
 where
  open import funext
  lemma : isProp(Π A)
  lemma f g = funext (λ x → isa x (f x) (g x))
