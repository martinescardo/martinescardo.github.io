Martin Escardo, May 2012. Compiles in Agda 2.3.0.

A remark on
-------------------------------------------------------
 Function graphs in intensional Martin-Löf type theory
-------------------------------------------------------

For f, g : X → Y, define

      graph f = Σ \x → Σ \y → f x ≡ y,

where "≡" is propositional equality (identity type). It may be 
natural to suppose that, in IMLTT,

  (*) graph f ≡ graph g → ∀(x : X) → f x ≡ g x. 

However, one can show

  (**) univalence → ∀(f g : X → Y) → graph f ≡ graph g.

Because univalence is consistent, and (*) together with (**) proves an
inconsistency (all functions are pointwise equal), we conclude that (*) 
is not provable in MLTT.

This file is self-contained. After a short prelude of standard
definitions, we give the easy proof of (**).

\begin{code}

{-# OPTIONS --without-K #-}

module FunctionGraphsInIMLTT where 

infixr 20 _×_     -- cartesian product
infixr  3 _,_     -- pairing
infix  11 _~_     -- pointwise function equality
infix  11 _≈_     -- pointwise isomorphism
infixl 30 _∘_     -- function composition
infix  30 _≡_     -- identity type for small types
infix  30 _≡₁_    -- identity type for large types

record Σ {X : Set} (Y : X → Set) : Set where
 constructor _,_
 field
  π₀ : X
  π₁ : Y π₀

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

J : {X : Set} → (A : ∀(x x' : X) → x ≡ x' → Set)
 → (∀(x : X) → A x x refl) →  ∀{x x' : X} → ∀(r : x ≡ x') → A x x' r
J A f {x} refl = f x

pseudo-uip : {X : Set} →
 ∀{x x' : X} → ∀(r : x ≡ x') → (x , refl) ≡ (x' , r)
pseudo-uip {X} = J {X} A (λ x → refl)
 where A : ∀(x x' : X) → x ≡ x' → Set
       A x x' r = _≡_ {Σ \(x' : X) → x ≡ x'} (x , refl) (x' , r)

trans : {X : Set} → {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
trans refl refl = refl

cong : {X Y : Set} → ∀(f : X → Y) → {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

data _≡₁_ {X : Set₁} : X → X → Set₁ where
  refl₁ : {x : X} → x ≡₁ x

graph : {X Y : Set} → (X → Y) → Set
graph f = Σ \x → Σ \y → f x ≡ y

_~_ : {X Y : Set} → (X → Y) → (X → Y) → Set
f ~ g = ∀ x → f x ≡ g x

id : {X : Set} → X → X
id x = x

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)

_≈_ : Set → Set → Set
X ≈ Y = Σ \(u : X → Y) → Σ \(v : Y → X) → (u ∘ v ~ id)  ×  (v ∘ u ~ id)

≈-refl : {X : Set} → X ≈ X
≈-refl = (id , id , (λ x → refl) , (λ x → refl))

≈-sym : {X Y : Set} → X ≈ Y → Y ≈ X
≈-sym (u , v , r , s) = (v , u , s , r)

≈-trans : {X Y Z : Set} → X ≈ Y → Y ≈ Z → X ≈ Z
≈-trans (u , v , r , s) (u' , v' , r' , s') = (u' ∘ u , v ∘ v' ,  r'' , s'')
 where 
  r'' : ∀ z → u' (u (v (v' z))) ≡ z
  r'' z = trans (cong u' (r(v' z))) (r' z)
  s'' : ∀ x → v (v' (u' (u x))) ≡ x
  s'' x = trans (cong v (s'(u x))) (s x)

\end{code}

End of prelude. 

The remark starts here. In all varieties of mathematics (constructive
or not), the graph {(x , y) | f x = y} of a function f: X → Y is
isomorphic to X. In one direction, the isomorphism simply sends a pair
(x,y) in the graph of f to x, and its inverse maps x to (x, f x). Type
theory is no exception, but of course we have to be a little bit more
careful with both the construction and argument. Moreover, in the
absence of extensionality, we have to work with pointwise isomorphism
(defined above). This means that the composition of the isomorphism
with its inverse is not equal to the identity, but only pointwise
equal to the identity.

\begin{code}

fact : {X Y : Set} → ∀(f : X → Y) → graph f ≈ X
fact {X} f = (u , v , r , s)
 where
  u : graph f → X
  u (x , y , r) = x
  v : X → graph f
  v x = (x , f x , refl)
  r : u ∘ v ~ id
  r x = refl
  s : v ∘ u ~ id
  s (x , y , r) = cong (λ z → (x , z)) (pseudo-uip r)
  
lemma : {X Y : Set} → ∀(f g : X → Y) → graph f ≈ graph g
lemma f g = ≈-trans (fact f) (≈-sym(fact g))

\end{code}

There is nothing surprising or specific to type theory so far: in
classical mathematics, any two functions X → Y have isomorphic graphs
too. However, in classical mathematics any two functions with equal
graphs must themselves be equal, and, in fact, the official definition
of a function is that it is a graph. 

The following is a consequence of univalence, where ≡₁ is type
identity (I am deliberately avoiding universe polymorphism). The
reason is that univalence implies the axiom of extensionality (two
pointwise equal functions are equal), and hence that pointwise
isomorphic types are isomorphic, and also that isomorphic types are
equal.

\begin{code}

weak-univalence : Set₁
weak-univalence = ∀{X Y : Set} → X ≈ Y → X ≡₁ Y

proposition : 

 weak-univalence → ∀{X Y : Set} → ∀(f g : X → Y) → graph f ≡₁ graph g

proposition uni f g = uni(lemma f g)

\end{code}

By the consistency of univalence, it follows that IMLTT cannot prove
that any two functions with equal graphs must be pointwise equal.

Thus, the statement "any two functions with equal graphs must be
equal" cannot be used to express extensionality in MLTT, because it is
provably false in IMLTT+univalence, which proves extensionality.

Idle thought: Is the statement 

  ∀(X Y : Set) → ∀(f g : X → Y) → graph f ≡₁ graph g 

equivalent to univalence? (Where ≡₁ is identity of small types.)

The source file is available at 

  http://www.cs.bham.ac.uk/~mhe/papers/FunctionGraphsInIMLTT/FunctionGraphsInIMLTT.lagda
