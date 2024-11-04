Martin Escardo 2012.

\begin{code}

module Extensionality where


open import Mini-library

postulate 
 extensionality : {X : Set} → {Y : X -> Set} → ∀{f g : (x : X) → Y x} →
                   [ ((∀ x → f x ≡ g x) → f ≡ g) ]

\end{code}
