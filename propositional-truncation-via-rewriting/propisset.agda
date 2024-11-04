-- Martin Escardo, 5th August 2015. Modified 9 May to add rewriting to conform with prop.agda.

{-# OPTIONS --without-K #-}

module propisset where

open import preliminaries
open import prop

Prop-isSet : isSet Prp
Prop-isSet = path-collapsible-isSet pc
 where
  A : (p q : Prp) → U₀
  A p q = (p holds → q holds) × (q holds → p holds)
  A-isProp : (p q : Prp) → isProp(A p q)
  A-isProp p q = isProp-closed-under-Σ (isProp-exponential-ideal (λ _ → holdsIsProp q))
                                       (λ _ → isProp-exponential-ideal (λ _ → holdsIsProp p))
  g : (p q : Prp) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : (p holds) ≡ (q holds)
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (sym a)
  h  : (p q : Prp) → A p q → p ≡ q
  h p q (u , v) = propext u v
  f  : (p q : Prp) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Prp) (d e : p ≡ q) → f p q d ≡ f p q e
  constant-f p q d e = ap (h p q) (A-isProp p q (g p q d) (g p q e))
  pc : {p q : Prp} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)
