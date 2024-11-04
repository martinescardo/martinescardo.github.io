Martin Escardo, Jun 7 2013.

We use Dan Licata's trick 
http://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/
to implement hpropositional truncation so that the elimination-rule equations hold definitionally.

\begin{code}

{-# OPTIONS --without-K #-}

module hprop-truncation where

open import tiny-library

\end{code}

We implement the hpropositional truncation of ∥ X ∥ as X itself, or
rather its isomorphic copy ∥ X ∥', which is kept private to the
module:

\begin{code}

private 
 data ∥_∥' (X : U) : U where
   ∣_∣' : X → ∥ X ∥'

∥_∥ : U → U
∥_∥ = ∥_∥'

postulate truncation-path : {X : U} → hprop ∥ X ∥

∣_∣ : {X : U} → X → ∥ X ∥
∣_∣ = ∣_∣'

truncation-ind : {X : U} {P : ∥ X ∥ → U} → ((s : ∥ X ∥) → hprop(P s)) → ((x : X) → P ∣ x ∣) 
               → (s : ∥ X ∥) → P s
truncation-ind _ f ∣ x ∣' = f x

truncation-rec : {X P : U} → hprop P → (X → P) → ∥ X ∥ → P
truncation-rec _ f ∣ x ∣' = f x

\end{code}

The crucial point is that the above two elimination rules hold
definitionally. Because of the postulate, we lose canonicity.

