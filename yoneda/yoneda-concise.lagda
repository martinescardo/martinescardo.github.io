Martin Escardo, 10 May 2015. 

This is a laconic version of
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

\begin{code}

{-# OPTIONS --without-K #-}

U = Set

data Id {X : U} : X → X → U where
 refl : (x : X) → Id x x 

_≡_ : {X : U} → X → X → U
x ≡ y = Id x y

infix 1 _≡_ 

Id-rec : {X : U} {x : X} (A : X → U)
      → A x → ({y : X} → x ≡ y → A y) 
Id-rec A a (refl x) = a

yoneda-lemma : {X : U} {x : X} {A : X → U} (η : ({y : X} → x ≡ y → A y)) (y : X) (p : x ≡ y) 
             → Id-rec A (η (refl x)) p ≡ η p
yoneda-lemma η x (refl .x) = refl (η (refl x))

_•_ : {X : U} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p • q = Id-rec (Id _) p q 

Id⁻¹  : {X : U} → X → X → U
Id⁻¹ x y = Id y x

_⁻¹ : {X : U} {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = Id-rec  (Id⁻¹ _) (refl _) p

yoneda-const : {X B : U} {x : X} (η : {y : X} → x ≡ y → B) (y : X) (p : x ≡ y) 
            → η (refl x) ≡ η p 
yoneda-const {X} {B} {x} η y p  = v ⁻¹ • u
 where
   u : Id-rec (λ _ → B) (η (refl x)) p ≡ η p
   u = yoneda-lemma η y p
   v : Id-rec (λ _ → B) (η (refl x)) p ≡ η (refl x)
   v = yoneda-lemma (λ p → η (refl x)) y p

data Σ {X : U} (A : X → U) : U where
 _,_ : (x : X) → A x → Σ \(x : X) → A x

paths-from : {X : U} → X → U
paths-from {X} x = Σ \(y : X) → x ≡ y

singletons-contractible : {X : U} {x : X} (w : paths-from x) → (x , refl x) ≡ w
singletons-contractible {X} {x} (y , p) = yoneda-const η y p
 where
  η : {y : X} → x ≡ y → paths-from x
  η {y} p = (y , p)

J' : (X : U) (x : X) (B' : paths-from x → U)
   → B' (x , refl x) → ∀ w → B' w
J' X x B' b w = Id-rec B' b (singletons-contractible w)

uncurry : {X : U}{x : X} → ((y : X) → x ≡ y → U) → (paths-from x → U)
uncurry B (y , p) = B y p

J : (X : U) (x : X) (B : (y : X) → x ≡ y → U)
   → B x (refl x) → (y : X) (p : x ≡ y) → B y p
J X x B b y p = J' X x (uncurry B) b (y , p)

J-computation : {X : U} {x : X} {B : (y : X) → x ≡ y → U} (b : B x (refl x)) 
             → J X x B b x (refl x) ≡ b
J-computation = refl


infixl 0 _•_

\end{code}
