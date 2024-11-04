\begin{code} 

module decidable-and-discrete where

open import mini-library

decidable : Set → Set
decidable X = X + (X → ∅)

discrete : Set → Set
discrete X = {x y : X} → decidable(x ≡ y)

₂-discrete : discrete ₂
₂-discrete {₀} {₀} = in₀ refl
₂-discrete {₀} {₁} = in₁(λ())
₂-discrete {₁} {₀} = in₁(λ())
₂-discrete {₁} {₁} = in₀ refl

\end{code}
