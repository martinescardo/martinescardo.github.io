huangjie Xu, 2012

\begin{code}

module CSpace-interpretation-of-T where

open import Mini-library
open import Space
open import Space-exponential
open import Space-discrete
open import Continuous-combinator
open import System-T


space : Ty → Space
space ② = ₂Space
space Ⓝ = ℕSpace
space (A ↣ B) = (space A) ⇒ (space B)


C⟦_⟧ : {A : Ty} → Tm A → U (space A)
C⟦ ⊤ ⟧                = ₁
C⟦ ⊥ ⟧                = ₀
C⟦ If {A} ⟧           = continuous-if {space A}
C⟦ Zero ⟧             = 0
C⟦ Succ ⟧             = continuous-succ
C⟦ Rec {A} ⟧          = continuous-rec {space A}
C⟦ K {A} {B} ⟧        = continuous-k {space A} {space B}
C⟦ S {A} {B} {C} ⟧    = continuous-s {space A} {space B} {space C}
C⟦ t · u ⟧            = π₀ C⟦ t ⟧ C⟦ u ⟧

\end{code}