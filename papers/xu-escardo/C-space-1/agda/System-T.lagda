Chuangjie Xu, 2012

\begin{code}

module System-T where

open import Mini-library


infixr 3 _↣_


data Ty : Set where
  ② : Ty
  Ⓝ : Ty
  _↣_ : Ty → Ty → Ty


infixl 3 _·_

data Tm : Ty → Set₁ where
  ⊤    : Tm ②
  ⊥    : Tm ②
  If   : {A : Ty} → Tm (A ↣ A ↣ ② ↣ A)
  Zero : Tm Ⓝ
  Succ : Tm (Ⓝ ↣ Ⓝ)
  Rec  : {A : Ty} → Tm ((A ↣ A) ↣ A ↣ Ⓝ ↣ A)
  K    : {A B : Ty} → Tm (A ↣ B ↣ A)
  S    : {A B C : Ty} → Tm ((A ↣ B ↣ C) ↣ (A ↣ B) ↣ A ↣ C)
  _·_  : {A B : Ty} → Tm (A ↣ B) → Tm A → Tm B
  
  
\end{code}