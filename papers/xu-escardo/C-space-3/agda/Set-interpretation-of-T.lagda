Chuangjie Xu, 2012

\begin{code}

module Set-interpretation-of-T where

open import Mini-library
open import System-T

set : Ty → Set
set ① = ⒈
set ② = ₂
set Ⓝ = ℕ
set (A ↣ B) = (set A) → (set B)
set (A ⊠ B) = (set A) × (set B)
set (A ⊞ B) = (set A) ⊎ (set B)


⟦_⟧ : {A : Ty} → Tm A → set A
⟦ ✸ ⟧     = ⋆
⟦ Unit ⟧  = unit
⟦ ⊤ ⟧     = ₁
⟦ ⊥ ⟧     = ₀
⟦ If ⟧    = if
⟦ Zero ⟧  = 0
⟦ Succ ⟧  = succ
⟦ Rec ⟧   = rec
⟦ K ⟧     = λ x y → x
⟦ S ⟧     = λ x y z → x z (y z)
⟦ t · u ⟧ = ⟦ t ⟧ ⟦ u ⟧
⟦ t ˣ u ⟧ = (⟦ t ⟧ , ⟦ u ⟧)
⟦ Prj₀ ⟧  = π₀
⟦ Prj₁ ⟧  = π₁
⟦ Inj₀ ⟧  = in₀
⟦ Inj₁ ⟧  = in₁
⟦ Case ⟧  = case


T-definable : {A : Ty} → (x : set A) → Set₁
T-definable {A} x = Σ \(t : Tm A) → ⟦ t ⟧ ≡ x

\end{code}