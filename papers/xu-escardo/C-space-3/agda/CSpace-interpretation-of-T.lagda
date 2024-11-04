Chuangjie Xu, 2012

\begin{code}

module CSpace-interpretation-of-T where

open import Mini-library
open import ConsHeadTail
open import Setoid
open import Space
open import Space-exponential
open import Space-product
open import Space-coproduct
open import Space-discrete
open import Continuous-combinator
open import System-T


space : Ty → Space
space ① = ⒈Space
space ② = ₂Space
space Ⓝ = ℕSpace
space (A ↣ B) = (space A) ⇒ (space B)
space (A ⊠ B) = (space A) ⊗ (space B)
space (A ⊞ B) = (space A) ⊕ (space B)


C⟦_⟧ : {A : Ty} → Tm A → Ū (space A)
C⟦ ✸ ⟧                = ⋆
C⟦ Unit {A} ⟧         = continuous-unit {space A}
C⟦ ⊤ ⟧                = ₁
C⟦ ⊥ ⟧                = ₀
C⟦ If {A} ⟧           = continuous-if {space A}
C⟦ Zero ⟧             = 0
C⟦ Succ ⟧             = continuous-succ
C⟦ Rec {A} ⟧          = continuous-rec {space A}
C⟦ K {A} {B} ⟧        = continuous-k {space A} {space B}
C⟦ S {A} {B} {C} ⟧    = continuous-s {space A} {space B} {space C}
C⟦ t · u ⟧            = π₀ (π₀ C⟦ t ⟧) C⟦ u ⟧
C⟦ t ˣ u ⟧            = (C⟦ t ⟧ , C⟦ u ⟧)
C⟦ Prj₀ {A} {B} ⟧     = continuous-π₀ {space A} {space B}
C⟦ Prj₁ {A} {B} ⟧     = continuous-π₁ {space A} {space B}
C⟦ Inj₀ {A} {B} ⟧     = continuous-in₀ {space A} {space B}
C⟦ Inj₁ {A} {B} ⟧     = continuous-in₁ {space A} {space B}
C⟦ Case {A} {B} {C} ⟧ = continuous-case {space A} {space B} {space C}

\end{code}