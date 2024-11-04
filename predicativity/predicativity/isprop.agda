-- Martin Escardo, 3rd August 2015

{-# OPTIONS --without-K #-}

module isprop where

open import preliminaries

-- A proposition is a type with at most one element:

isProp : {i : Level} → U i → U i
isProp X = (x y : X) → x ≡ y

-- The two canonical examples:

𝟘-isProp : {i : L} → isProp (𝟘{i})
𝟘-isProp () ()

𝟙-isProp : {i : L} → isProp (𝟙{i})
𝟙-isProp zero zero = refl zero

isSet : {i : L} → U i → U i
isSet X = {x y : X} → isProp(x ≡ y)

constant : {i j : L} {X : U i} {Y : U j} → (f : X → Y) → U (i ⊔ j)
constant f = ∀ x y → f x ≡ f y

collapsible : {i : L} → U i → U i
collapsible X = Σ \(f : X → X) → constant f

path-collapsible : {i : L} → U i → U i
path-collapsible X = {x y : X} → collapsible(x ≡ y)

isSet-is-path-collapsible : {i : L} {X : U i} → isSet X → path-collapsible X
isSet-is-path-collapsible u = (λ p → p) , u 

path-collapsible-isSet : {i : L} {X : U i} → path-collapsible X → isSet X
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

prop-is-path-collapsible : {i : L} {X : U i} → isProp X → path-collapsible X
prop-is-path-collapsible h {x} {y} = ((λ p → h x y) , (λ p q → refl(h x y)))

prop-is-set : {i : L} {X : U i} → isProp X → isSet X
prop-is-set h = path-collapsible-isSet(prop-is-path-collapsible h)

isProp-isProp : {i : L} {X : U i} → isProp(isProp X)
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

isProp-closed-under-Σ : {i j : L} {X : U i} {A : X → U j} 
                    → isProp X → ((x : X) → isProp(A x)) → isProp(Σ A)
isProp-closed-under-Σ {i} {j} {X} {A} isx isa (x , a) (y , b) = Σ-≡ (isx x y) (isa y (transport A (isx x y) a) b)

isProp-exponential-ideal : {i j : L} {X : U i} {A : X → U j} 
                        → ((x : X) → isProp(A x)) → isProp(Π A) 
isProp-exponential-ideal {i} {j} {X} {A} isa = lemma
 where
  open import funext
  lemma : isProp(Π A)
  lemma f g = funext (λ x → isa x (f x) (g x))
