Chuangjie Xu, 2012

\begin{code}

module Set-interpretation-of-T where

open import Mini-library
open import System-T


set : Ty → Set
set ② = ₂
set Ⓝ = ℕ
set (A ↣ B) = (set A) → (set B)


⟦_⟧ : {A : Ty} → Tm A → set A
⟦ ⊤ ⟧    = ₁
⟦ ⊥ ⟧    = ₀
⟦ If ⟧    = if
⟦ Zero ⟧  = 0
⟦ Succ ⟧  = succ
⟦ Rec ⟧   = rec
⟦ K ⟧     = λ x y → x
⟦ S ⟧     = λ x y z → x z (y z)
⟦ t · u ⟧ = ⟦ t ⟧ ⟦ u ⟧


T-definable : {A : Ty} → (x : set A) → Set₁
T-definable {A} x = Σ \(t : Tm A) → ⟦ t ⟧ ≡ x

\end{code}