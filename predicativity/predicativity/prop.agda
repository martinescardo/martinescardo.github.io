-- Martin Escardo, 7th August 2015

{-# OPTIONS --without-K #-}

module prop where

open import preliminaries
open import isprop public

Prp : (i : L) → U(lsuc i)
Prp i = Σ \(P : U i) → isProp P

₍_,_₎ : {i : L} (P : U i) → isProp P → Prp i
₍_,_₎ = _,_

_holds : {i : L} → Prp i → U i
_holds = pr₁

infix 20 _holds

holdsIsProp : {i : L} (p : Prp i) → isProp(p holds)
holdsIsProp = pr₂

Prp-≡ : {i : L} {p q : Prp i} → p holds ≡ q holds → p ≡ q
Prp-≡ {i} {p} {q} e = Σ-≡ e (isProp-isProp (transport isProp e (holdsIsProp p)) (holdsIsProp q))

open import propua

propext : {i : L} {p q : Prp i} → (p holds → q holds) → (q holds → p holds) → p ≡ q
propext {i} {p} {q} f g = Prp-≡ e
 where
  e : p holds ≡ q holds
  e = prop-ua (holdsIsProp p) (holdsIsProp q) f g
