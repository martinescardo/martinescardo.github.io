{-

 Martin Escardo, 9 May 2016.

 I wanted an inconsistent function

   resize : {i j : Level} → Set i → Set j

 in Agda such that (resize X) is definitionally equal to X,
 as an alternative to --type-in-type.

 Andreas Abel suggested to use Agda's new option --rewriting,
 with the rewrite rule

   resize-id : {i j : Level} {A : Set i} → resize {i} {j} A ↦ A

 Jesper Cockx added a patch to Agda to allow rewrite rules which
 change type, such as the above.

 Thanks to Andreas and Jesper for their instant help!

 I also needed to add the functions resize-in and resize-out below,
 with corresponding rewriting rules.

 This module should not be used other than by specialized modules that
 know what they are doing.

 In this development it is prop.agda only.

 In the current version of Agda, 2.5.2, direct or indirect users of
 this module will need to use the option --rewriting like this:

-}

{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-}

module resize where

open import Agda.Primitive using (Level ; lzero ; lsuc ; _⊔_) public

postulate
  _↦_ : {i j : Level}{A : Set i}{B : Set j} → A → B → Set (i ⊔ j)

{-# BUILTIN REWRITE _↦_ #-}

postulate
  resize        : {i j : Level} → Set i → Set j
  resize-id     : {i j : Level} {X : Set i} → resize {i} {j} X ↦ X
  resize-in     : {i j : Level} {X : Set i} → X → resize {i} {j} X
  resize-in-id  : {i j : Level} {X : Set i} (x : X) → resize-in {i} {j} {X} x ↦ x
  resize-out    : {i j : Level} {X : Set i} → resize {i} {j} X → X
  resize-out-id : {i j : Level} {X : Set i} (r : resize {i} {j} X) → resize-out {i} {j} {X} r ↦ r

{-# REWRITE resize-id #-}
{-# REWRITE resize-in-id #-}
{-# REWRITE resize-out-id #-}
