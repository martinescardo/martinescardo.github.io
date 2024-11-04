Martin Escardo, 8 May 2015. 

This is a follow-up of 
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

You should read that first. 

We use pattern matching on identity types to define J only.  

This time we define Yoneda from J rather than from pattern matching.

I wondered whether if we chase the construction

  J ↦ Yoneda ↦ new-J

we get the same J definitionally. We don't. But we still get that the
new J satisfies its computation rule definitionally.

\begin{code}

{-# OPTIONS --without-K #-}

U = Set
U₁ = Set₁

data Id {X : U} : X → X → U where
 refl : (x : X) → Id x x 

_≡_ : {X : U} → X → X → U
x ≡ y = Id x y

J : (X : U) (x : X) (B : (y : X) → x ≡ y → U)
  → B x (refl x) → (y : X) (p : x ≡ y) → B y p
J X x B b .x (refl .x) = b

PrShf : U → U₁
PrShf X = (X → U)

Nat : {X : U} → PrShf X → PrShf X → U
Nat {X} A B = {x : X} → A x → B x

yoneda-elem : {X : U} {x : X} {A : PrShf X}
            → Nat (Id x) A → A x
yoneda-elem {X} {x} η = η(refl x)

yoneda-nat : {X : U} {x : X} {A : PrShf X} 
           → A x → Nat (Id x) A 
yoneda-nat {X} {x} {A} a {y} = J X x (λ y p → A y) a y

transport : {X : U} (A : X → U) {x y : X}
          → x ≡ y → A x → A y
transport {X} A {x} p a = yoneda-nat {X} {x} {A} a p

yoneda-lemma : {X : U} {x : X} {A : PrShf X} (η : Nat (Id x) A) (y : X) (p : x ≡ y) 
             → transport A p (yoneda-elem η) ≡ η p
yoneda-lemma {X} {x} {A} η = J X x (λ y p → transport A p (yoneda-elem η) ≡ η p) (refl (yoneda-elem η))

_•_ : {X : U} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p • q = transport (Id _) q p 

Id⁻¹  : {X : U} → X → X → U
Id⁻¹ x y = Id y x

_⁻¹ : {X : U} {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport  (Id⁻¹ _) p (refl _)

constPrShf : {X : U} → U → PrShf X 
constPrShf B _ = B

yoneda-const : {X B : U} {x : X} (η : Nat (Id x) (constPrShf B)) (y : X) (p : x ≡ y) 
            → yoneda-elem η ≡ η p 
yoneda-const {X} {B} {x} η y p  = v ⁻¹ • u
 where
   u : transport (constPrShf B) p (yoneda-elem η) ≡ η p
   u = yoneda-lemma η y p
   v : transport (constPrShf B) p (yoneda-elem η) ≡ yoneda-elem η
   v = yoneda-lemma ((λ p → yoneda-elem η)) y p

\end{code}

This time we work with an alternative definition of Σ that has better
definitional "eta" properties. However, this still doesn't help to get
new-J definitionally equal to our starting J.

\begin{code} 

record Σ {X : U} (A : X → U) : U where
  constructor _,_
  field
   π₀ : X
   π₁ : A π₀

open Σ public

paths-from : {X : U} → X → U
paths-from {X} x = Σ \(y : X) → x ≡ y

singletons-contractible : {X : U} {x : X} (w : paths-from x) → (x , refl x) ≡ w
singletons-contractible {X} {x} (y , p) = yoneda-const η y p
 where
  η : Nat (Id x) (constPrShf(paths-from x))
  η {y} p = (y , p)

new-J' : (X : U) (x : X) (B' : paths-from x → U)
   → B' (x , refl x) → ∀ w → B' w
new-J' X x B' b w = transport B' (singletons-contractible w) b

uncurry : {X : U}{x : X} → ((y : X) → x ≡ y → U) → (paths-from x → U)
uncurry B (y , p) = B y p

new-J : (X : U) (x : X) (B : (y : X) → x ≡ y → U)
   → B x (refl x) → (y : X) (p : x ≡ y) → B y p
new-J X x B b y p = new-J' X x (uncurry B) b (y , p)

new-J-computation : {X : U} {x : X} {B : (y : X) → x ≡ y → U} (b : B x (refl x)) 
                  → new-J X x B b x (refl x) ≡ b
new-J-computation = refl

\end{code}

Agda reports the following normal form for new-J, which is
definitionally different from J:

λ X x B b y p →
  J (Σ (λ y₁ → Id x y₁)) (x , refl x) (λ y₁ p₁ → B (π₀ y₁) (π₁ y₁)) b
  (y , p)
  (J (Σ (λ y₁ → Id x y₁))
   (J X x (λ y₁ p₁ → Σ (λ y₂ → Id x y₂)) (x , refl x) y p)
   (λ y₁ p₁ → Id (x , refl x) y₁)
   (J (Σ (λ y₁ → Id x y₁))
    (J X x (λ y₁ p₁ → Σ (λ y₂ → Id x y₂)) (x , refl x) y p)
    (λ y₁ p₁ →
       Id y₁ (J X x (λ y₂ p₂ → Σ (λ y₃ → Id x y₃)) (x , refl x) y p))
    (refl (J X x (λ y₁ p₁ → Σ (λ y₂ → Id x y₂)) (x , refl x) y p))
    (x , refl x)
    (J X x
     (λ y₁ p₁ →
        Id (J X x (λ y₂ p₂ → Σ (λ y₃ → Id x y₃)) (x , refl x) y₁ p₁)
        (x , refl x))
     (refl (x , refl x)) y p))
   (y , p)
   (J X x
    (λ y₁ p₁ →
       Id (J X x (λ y₂ p₂ → Σ (λ y₃ → Id x y₃)) (x , refl x) y₁ p₁)
       (y₁ , p₁))
    (refl (x , refl x)) y p))


\begin{code}

infix 1 _≡_ 
infixl 0 _•_

\end{code}
