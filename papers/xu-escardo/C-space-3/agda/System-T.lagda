Chuangjie Xu, 2012

\begin{code}

module System-T where

open import Mini-library


infixr 30 _↣_
infixr 30 _⊠_
infixr 30 _⊞_


data Ty : Set where
  ① : Ty
  ② : Ty
  Ⓝ : Ty
  _↣_ : Ty → Ty → Ty
  _⊠_ : Ty → Ty → Ty
  _⊞_ : Ty → Ty → Ty


infixl 3 _·_
infixl 3 _ˣ_


data Tm : Ty → Set₁ where
  ✸    : Tm ①
  Unit : {A : Ty} → Tm (A ↣ ①) 
  ⊤    : Tm ②
  ⊥    : Tm ②
  If   : {A : Ty} → Tm (A ↣ A ↣ ② ↣ A)
  Zero : Tm Ⓝ
  Succ : Tm (Ⓝ ↣ Ⓝ)
  Rec  : {A : Ty} → Tm ((A ↣ A) ↣ A ↣ Ⓝ ↣ A)
  K    : {A B : Ty} → Tm (A ↣ B ↣ A)
  S    : {A B C : Ty} → Tm ((A ↣ B ↣ C) ↣ (A ↣ B) ↣ A ↣ C)
  _·_  : {A B : Ty} → Tm (A ↣ B) → Tm A → Tm B
  _ˣ_  : {A B : Ty} → Tm A → Tm B → Tm (A ⊠ B)
  Prj₀ : {A B : Ty} → Tm ((A ⊠ B) ↣ A)
  Prj₁ : {A B : Ty} → Tm ((A ⊠ B) ↣ B)
  Inj₀ : {A B : Ty} → Tm (A ↣ (A ⊞ B))
  Inj₁ : {A B : Ty} → Tm (B ↣ (A ⊞ B))
  Case : {A B C : Ty} → Tm ((A ↣ C) ↣ (B ↣ C) ↣ (A ⊞ B) ↣ C)

  
\end{code}