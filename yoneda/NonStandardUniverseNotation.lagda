Martín Escardó, 7th December 2017

We introduce a notation for type universes which is currently
non-standard from the point of view of the common Agda practice, but
which is closer to the standard notation in univalent mathematics and
homotopy type theory.

We have a sequence of non-cumulative universes à la Russell, with
"Universe" the type of universe codes, and with a postfix (almost
invisible, superscript, dot) _̇ decodification function.

In Agda the universes are called Set ℓ, but this terminology/notation
has its origin before HoTT and univalent foundations.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module NonStandardUniverseNotation where

open import Agda.Primitive using (_⊔_) renaming (lzero to U₀ ; lsuc to usuc ; Level to Universe) public

_̇ : (U : Universe) → _
U ̇ = Set U -- This should be the only use of the Agda keyword 'Set' in any HoTT/UF development.

_′ : Universe → Universe
_′ = usuc

infix 0 _̇
infix 99 _′

\end{code}

For example, we write

  fiber : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → Y → U ⊔ V ̇
  fiber f y = Σ \x → f x ≡ y

rather than the usual

  fiber : {ℓ ℓ' : Level} {X : Set ℓ} {Y : Set ℓ'} → (X → Y) → Y → Set(ℓ ⊔ ℓ')
  fiber f y = Σ \x → f x ≡ y

Ideally, we would like to elide the coersions _̇ h and write

  fiber : {U V : Universe} {X : U} {Y : V} → (X → Y) → Y → U ⊔ V
  fiber f y = Σ \x → f x ≡ y

but this would require a change in the Agda type checker to insert the
coersions at the appropriate places.
