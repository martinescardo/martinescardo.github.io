\begin{code}

{-# OPTIONS --cubical #-}

module index where

\end{code}

This is the cubical Agda implementation of the PhD thesis

  A CONTINUOUS COMPUTATIONAL INTERPRETATION OF TYPE THEORIES

defended 1st May 2015, School of Computer Science, University of
Birmingham, UK, by

  Chuangjie XU

supervised by Martín Escardó.

The original version was developed in Agda 2.4.2.2 and is available
for downloading at

  http://cj-xu.github.io/ContinuityType/xu-thesis-agda.zip

This version, 9th November 2017, is ported to cubical Agda, and only
includes one of the five original branches, the one postulating
function extensionality. 

In the original, non-cubical, version of this branch, we had a closed
term of type ℕ (a modulus of uniform continuity of a simple function)
whose normal form was not a numeral but instead a 367-lines long
term. The term is (modu F₂) and its original normal form is named
(old-modu-F₂-normal-form) in the following file.

\begin{code}

import UsingFunext.ModellingUC.ComputationExperiments

\end{code}

This was because function extensionality was postulated as a term
funext. However, in this cubical version, funext is proved, and hence
the original term normalizes to zero (modu-F₂-normal-form).

Porting this to cubical Agda involved:

  1. Using Andrea Vezzosi's cubical library with a new definition of
  the identity type Id, which we rename to ≡ to conform with our
  original development. (Because our original development didn't use
  the standard library, but Vezzozi's one does, we had to slighly
  adapt his development for our needs.)

\begin{code}

open import Id
open import PathPrelude
open import Primitives
open import Sub

\end{code}

  2. Removing all uses of pattern matching on refl, and instead using
  the J induction principle for Id. 

  3. Giving up using built-in NATURALS.

In this version of the development, we only include the chapters of
the thesis that are needed to compute moduli of uniform continuity.

To navigate this set of files, click at module names, keywords or symbols.

Chapter 2 investigates the Curry-Howard formulations of the two
fundamental continuity principles, (Cont) and (UC).  The latter, which
is the one that we are working with in this thesis, is logically
equivalent to the logical formulation.  For this, we need to extend
the type theory with propositional truncation and the axiom of
function extensionality. This is removed from this branch of the
development.

Chapter 3 develops a variation of the topological topos, consisting of sheaves
on a certain uniform-continuity site.  In particular, C-spaces, corresponding to
concrete sheaves, form a (locally) cartesian closed category with a natural
numbers object.  Moreover, there is a fan functional, in the category of
C-spaces, that continuously calculates least moduli of uniform continuity of
maps ₂ℕ → ℕ. Not all of this is included in this version of the development.

\begin{code}

-- § 3.2.1  The uniform-continuity site
import UsingFunext.Space.Coverage

-- § 3.3.1  Concrete sheaves as a variation of quasi-topological spaces
import UsingFunext.Space.Space

-- § 3.3.2  The (local) cartesian closed structure of C-Space
import UsingFunext.Space.CartesianClosedness

-- § 3.3.3  Discrete C-spaces and natural numbers object
import UsingFunext.Space.DiscreteSpace

-- § 3.4  The representable sheaf is the Cantor space
import UsingFunext.Space.YonedaLemma

-- § 3.5  The fan functional in the category of C-spaces
import UsingFunext.Space.Fan

\end{code}

Chapter 4 shows how the Kleene-Kreisel continuous functionals can be
calculated within C-spaces.  When assuming the Brouwerian axiom that
all set-theoretic functions ₂ℕ → ℕ are uniformly continuous, the full
type hierarchy is equivalent to the Kleene--Kreisel continuous
hierarchy within C-spaces. This is not included in this version of the
development.

Chapter 5 employs C-spaces to model Gödel's system T with a
skolemization of (UC), and to realizes (UC) in the intuitionistic
arithmetic HAω of finite types, with the aid of the fan
functional. Not all of this is included in this version of the
development.

\begin{code}

-- § 5.1  A continuous model of Gödel's System T
import UsingFunext.ModellingUC.UCinT

\end{code}

Chapter 6 validates the Curry-Howard interpretation of (UC) in the
locally cartesian closed category of C-spaces using the fan
functional, and demonstrates how C-spaces and sheaves form models of
dependent types, without the coherence problem, via the notion of
category with families (CwF). This is not included in this version of
the development.

Chapter 7 discusses other versions of implementation, in which the
computational content of the development is not destroyed (using
setoids, using computationally irrelevant fields, and other
methods). This is not included in this version of the development.


