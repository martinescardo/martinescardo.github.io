module Choice where

open import Logic

AC : {X : Set} {Y : X → Set} {A : (x : X) → Y x → Ω} →

      (∀(x : X) → ∃(\(y : Y x) → A x y))
     → ∃(\(f : ((x : X) → Y x)) → ∀(x : X) → A x (f x))

AC g = ∃-intro (\x → ∃-witness (g x)) (\x → ∃-elim (g x))


