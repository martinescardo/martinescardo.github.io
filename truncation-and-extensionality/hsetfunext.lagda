Martin Escardo, 7 Jun 2013, updated 10 Jun with input by Nicolai Kraus
on extensionality, and 16 and 18 July with other things.

We show that in the presence of hpropositional truncation, function
extensionality holds for hset-valued functions.

For this to work, we need the equations for the elimination rule of
hpropositional reflection to hold definitionally.

Also updated 16-17 Jul showing that the truncation of ₂ is the
interval. This is perhaps surprising, because the truncation and the
interval have different higher-inductive definitions.

This file has its origin in a discussion in the Agda mailing list. For
historical reasons, I've kept the ideas in the order they have
evolved, rather than in their most natural logical order. This
explains the obscure name hsetfunext for this file. I may eventually
produce another file with the ideas presented in logical order.

\begin{code}

{-# OPTIONS --without-K #-}

module hsetfunext where

open import tiny-library 
open import hprop-truncation

module extensionality-discussion where
 
 truncation-rec-rec : {X Y P : Type} → hprop P → (X → Y → P) → ∥ X ∥ → ∥ Y ∥ → P
 truncation-rec-rec  {X} {Y} {P} h f u v = truncation-rec h (λ x → truncation-rec h (f x) v) u

 hset-truncation-rec : {X Y : Type} → hset Y → (f : X → Y) → constant f → ∥ X ∥ → Y
 hset-truncation-rec {X} {Y} hs f c u = π₀(F u)
  where
   ψ : (y y' : Y) → (Σ \x → f x ≡ y) → (Σ \x' → f x' ≡ y') → y ≡ y'
   ψ y y' (x , r) (x' , r') = r ⁻¹ • c x x' • r'  
   P : Type
   P = Σ \(y : Y) → ∥ (Σ \x → f x ≡ y) ∥
   P-hprop : hprop P
   P-hprop (y , u) (y' , u') = Σ-≡ {Y} {λ y →  ∥ (Σ \x → f x ≡ y) ∥} y y' u u' p (truncation-path (transport p u) u') 
    where
     p : y ≡ y'
     p = truncation-rec-rec (hs y y') (ψ y y') u u'
   F : ∥ X ∥ → P
   F = truncation-rec P-hprop (λ x → f x , ∣ (x , refl) ∣)

 extension-property : {X Y : Type} (hs : hset Y) (f : X → Y) (c : constant f) (x : X)
                    → hset-truncation-rec hs f c ∣ x ∣ ≡ f x
 extension-property hs f c x = refl

 hset-funext : {X : Type} {Y : X → Type} → ((x : X) → hset(Y x)) → {f g : (x : X) → Y x}
             → ((x : X) → f x ≡ g x) → f ≡ g
 hset-funext {X} {Y} hs {f} {g} φ = ap H' (truncation-path ∣ ₀ ∣ ∣ ₁ ∣) 
  where
   h : (x : X) → ₂ → Y x
   h x ₀ = f x
   h x ₁ = g x
   hx-constant : (x : X) → constant(h x)
   hx-constant x ₀ ₀ = refl
   hx-constant x ₀ ₁ = φ x
   hx-constant x ₁ ₀ = (φ x)⁻¹
   hx-constant x ₁ ₁ = refl 
   H : (x : X) → ∥ ₂ ∥ → Y x
   H x = hset-truncation-rec (hs x) (h x) (hx-constant x)
   H' : ∥ ₂ ∥ → (x : X) → Y x
   H' n x = H x n
  
\end{code}

Notice that we have H' ∣ ₀ ∣ x = f x and H' ∣ ₁ ∣ x = g x
definitionally, and so H' ∣ ₀ ∣ = λ x → f x and H' ∣ ₁ ∣ = λ x → g x,
which is crucial to get λ x → f x ≡ λ x → g x from ∣ ₀ ∣ ≡ ∣ ₁ ∣, and
thus f ≡ g from the η rule.

Every hprop is an hset, and hence the above holds for hprop-valued
functions. But this particular case can be proved more directly:

\begin{code}

 hprop-funext : {X : Type} {P : X → Type} → ((x : X) → hprop(P x)) → {f g : (x : X) → P x} 
             → ((x : X) → f x ≡ g x) → f ≡ g
 hprop-funext {X} {P} hp {f} {g} φ = ap H' (truncation-path ∣ ₀ ∣ ∣ ₁ ∣) 
  where
   h : (x : X) → ₂ → P x
   h x ₀ = f x
   h x ₁ = g x
   H : (x : X) → ∥ ₂ ∥ → P x
   H x = truncation-rec (hp x) (h x) 
   H' : ∥ ₂ ∥ → (x : X) → P x
   H' n x = H x n

\end{code}

Notice that the above proofs use the same idea applied to show that
the presence of a homotopy interval type implies function
extensionality:
http://homotopytypetheory.org/2011/04/04/an-interval-type-implies-function-extensionality/

Added 10 Jun 2013, 18.15:

As observed by Nicolai Kraus, hprop-funext actually gives funext for
arbitrary functions, using the following formulation of function
extensionality due to Voevodsky:

\begin{code}

 contractible-closed-under-Π : {X : Type} {P : X → Type} → ((x : X) → contractible(P x)) → contractible((x : X) → P x) 
 contractible-closed-under-Π {X} {P} φ = 
  ψ , (λ ψ' → hprop-funext (λ x p p' → (c x p)⁻¹ • (c x p')) {ψ} {ψ'} (λ x → c x (ψ' x)))
  where
   ψ : (x : X) → P x
   ψ x = π₀(φ x)
   c : (x : X) → (p : P x) → ψ x ≡ p
   c x = π₁(φ x)

\end{code}

That this implies full function extensionality is due to Voevodsky
(but notice that our proof is different from his, and works only for
the above proof of contractible-closed-under-Π - if we replace the
definition by a postulate, the following no longer type checks):

\begin{code}

 funext : {X : Type} {Y : X → Type} → {f g : (x : X) → Y x} 
       → ((x : X) → f x ≡ g x) → f ≡ g
 funext {X} {Y} {f} {g} φ = ap (λ H x → π₀(H x)) e
  where
   P : X → Type
   P x = Σ \(y : Y x) → f x ≡ y 
   u : (x : X) (p : P x) → (f x , refl) ≡ p
   u _ (_ , r) = path-from-trivial-loop r
   c : ((x : X) → contractible(P x))
   c x = (f x , refl) , u x
   d : contractible((x : X) → P x)
   d = contractible-closed-under-Π c
   F : (x : X) → P x
   F = π₀ d
   G : (x : X) → P x
   G x = g x , φ x
   e : F ≡ G
   e = π₁ d G

\end{code}

(Notice that again this proves (λ x → f x) ≡ (λ x → g x), and 
hence f ≡ g because we have the η rule in Agda.)

So the proposition hset-funext is now superfluous. With an equally
short proof, we get a more general conclusion.

For future use:

\begin{code} 

 hprop-hprop : {X : Type} → hprop(hprop X)
 hprop-hprop {X} f g = funext q
  where
   h : hset X
   h = hprop-is-hset f
   p : (x y : X) → f x y ≡ g x y
   p x y = h x y (f x y) (g x y) 
   q : (x : X) → f x ≡ g x 
   q x = funext (p x)

\end{code}

This is the end of the module extensionality-discussion.

Added 16 Jul 2013: Is ∥ ₂ ∥ the interval? Nicolai assumed that this
is the case, but I pointed out that their defining universal
properties (or higher induction principles) are different (see the
HoTT book).

I show that ∥ ₂ ∥ equipped with appropriate data does satisfy the
universal property of the interval (judgementally for the first-order
equations, and propositionally for the higher-order equation, just as
in the definition of the interval). Is this known?

\begin{code}

module interval where

 I : Type
 I = ∥ ₂ ∥ 
 seg : ∣ ₀ ∣ ≡ ∣ ₁ ∣
 seg = truncation-path ∣ ₀ ∣  ∣ ₁ ∣ 

 I-hset : hset I
 I-hset = hprop-is-hset truncation-path

\end{code}

We begin with a technical, auxiliary definition:

\begin{code}

 I-rec' : {X : Type} {x₀ x₁ : X} → x₀ ≡ x₁ → I → paths-from x₀
 I-rec' {X} {x₀} {x₁} p = truncation-rec (paths-from-is-hprop x₀) f
  where
   f : ₂ → paths-from x₀
   f ₀ = trivial-loop x₀
   f ₁ = x₁ , p

 I-rec : {X : Type} {x₀ x₁ : X} → x₀ ≡ x₁ → I → X
 I-rec p i = end-point(I-rec' p i)

\end{code}

The required two equations hold judgementally (because their proofs
are refl):

\begin{code}

 I-rec-equation₀ : {X : Type} {x₀ x₁ : X} (p : x₀ ≡ x₁) → I-rec p ∣ ₀ ∣ ≡ x₀
 I-rec-equation₀ p = refl

 I-rec-equation₁ : {X : Type} {x₀ x₁ : X} (p : x₀ ≡ x₁) → I-rec p ∣ ₁ ∣ ≡ x₁
 I-rec-equation₁ p = refl


\end{code}

We also need to show that seg satisfies the required equation
(propositionally). We begin with the base case of a proof by
induction:

\begin{code}

 I-rec-seg-equation-base : {X : Type} {x : X} → ap (I-rec refl) seg ≡ refl
 I-rec-seg-equation-base {X} {x} = r ⁻¹ • q
  where
   p : ap (I-rec' refl) seg ≡ refl {paths-from x} {trivial-loop x}
   p = paths-from-is-hset x (I-rec' refl ∣ ₀ ∣) (trivial-loop x) (ap (I-rec' refl) seg) refl
   q : ap end-point (ap (I-rec' refl) seg) ≡ refl
   q = ap (ap end-point) p
   r : ap end-point (ap (I-rec' refl) seg) ≡ ap (I-rec refl) seg
   r = ap-functorial (I-rec' refl) end-point seg

 I-rec-seg-equation : {X : Type} {x₀ x₁ : X} (p : x₀ ≡ x₁) → ap (I-rec p) seg ≡ p
 I-rec-seg-equation refl = I-rec-seg-equation-base

\end{code}

So we are done, and the answer is yes. 

Hence we can get a simpler proof of extensionality (the one
reported by Shulman). We only show the non-dependent version here.

\begin{code}

 funext-from-interval : {X Y : Type} {f g : X → Y} → ((x : X) -> f x ≡ g x) → f ≡ g
 funext-from-interval {X} {Y} h = ap I-X-family seg 
  where
   X-I-family : X → I → Y
   X-I-family x = I-rec (h x) 
   I-X-family : I → X → Y
   I-X-family i x = X-I-family x i

\end{code}

For the sake of completeness, let's prove the induction principle,
by reduction to recursion (added 19 July):

\begin{code}

 module I-induction (A : I → Type) where

  T : {i j : I} → i ≡ j → A i → A j
  T = transport {I} {A} 

  I-ind' : {a₀ : A ∣ ₀ ∣} {a₁ : A ∣ ₁ ∣} → T seg a₀ ≡ a₁ → I → Σ \(i : I) → A i
  I-ind' {a₀} {a₁} r = I-rec p
   where
    x₀ x₁ : Σ \(i : I) → A i
    x₀ = ∣ ₀ ∣ , a₀
    x₁ = ∣ ₁ ∣ , a₁
    p : x₀ ≡ x₁
    p = Σ-≡ ∣ ₀ ∣ ∣ ₁ ∣ a₀ a₁ seg r

  I-ind-path : {a₀ : A ∣ ₀ ∣} {a₁ : A ∣ ₁ ∣} → (p : T seg a₀ ≡ a₁) → (i : I) → π₀(I-ind' p i) ≡ i
  I-ind-path p = truncation-ind h g
   where
    h : (i : I) → hprop(π₀(I-ind' p i) ≡ i)
    h i = I-hset (π₀(I-ind' p i)) i
    g : (n : ₂) → π₀(I-ind' p ∣ n ∣) ≡ ∣ n ∣
    g ₀ = refl
    g ₁ = refl

  I-ind : {a₀ : A ∣ ₀ ∣} {a₁ : A ∣ ₁ ∣} → T seg a₀ ≡ a₁ → (i : I) → A i
  I-ind p i = T (I-ind-path p i) (π₁(I-ind' p i))

  I-ind-equation₀ : {a₀ : A ∣ ₀ ∣} {a₁ : A ∣ ₁ ∣} (p : T seg a₀ ≡ a₁) → I-ind p ∣ ₀ ∣ ≡ a₀
  I-ind-equation₀ p = refl

  I-ind-equation₁ : {a₀ : A ∣ ₀ ∣} {a₁ : A ∣ ₁ ∣} (p : T seg a₀ ≡ a₁) → I-ind p ∣ ₁ ∣ ≡ a₁
  I-ind-equation₁ p = refl


\end{code}

We also need to show

  I-ind-seg-equation-base : {a₀ : A ∣ ₀ ∣} 
                          → apd {I} (I-ind refl) seg ≡ refl {A ∣ ₁ ∣} {T seg a₀}
  I-ind-seg-equation-base = {!!}

  I-ind-seg-equation : {a₀ : A ∣ ₀ ∣} {a₁ : A ∣ ₁ ∣} (p : T seg a₀ ≡ a₁) 
                     → apd {I} (I-ind p) seg ≡ p
  I-ind-seg-equation {a₀} refl =  I-ind-seg-equation-base {a₀}
   
But I leave this for another opportunity.

Additional (expected) information, using extensionality:

\begin{code}

 trivial-Loop : {X : Type} (x : X) → I → X
 trivial-Loop x i = x 

 I-rec-refl-is-trivial-Loop : {X : Type} {x : X} → I-rec refl ≡ trivial-Loop x
 I-rec-refl-is-trivial-Loop {X} {x} = funext g 
  where
   open extensionality-discussion
   P : I → Type
   P i = I-rec' refl i ≡ trivial-loop x
   H : (i : I) → hprop(P i)
   H i = paths-from-is-hset x (I-rec' refl i) (trivial-loop x)
   f : (n : ₂) → I-rec' refl ∣ n ∣ ≡ trivial-loop x
   f ₀ = refl
   f ₁ = refl
   f' : (i : I) → I-rec' refl i ≡ trivial-loop x
   f' = truncation-ind H f
   g : (i : I) → I-rec refl i ≡ x 
   g i = ap end-point (f' i)

\end{code}

I initially tried to use this to prove I-rec-seg-equation. The given
proof is better, because it doesn't use function extensionality.

This is the end of the module interval.

Added 18 July 2013: If X is inhabited, then any constant function into
any type Y factors through ∣_∣ : X → ∥ X ∥ judgementally.

\begin{code}

module factor-constant where

\end{code}

A simple idea is to define a section ∥ X ∥ → X by mapping everything
to x₀ and then define the factorization f' : ∥ X ∥ → Y to be this
section followed by f, that is, f' _ = f x₀. This works, because f is
constant, but not judgementally:

\begin{code}

 propositional-factorization : {X Y : Type} (x₀ : X) (f : X → Y) → constant f → ∥ X ∥ → Y
 propositional-factorization x₀ f _ _ = f x₀ 

\end{code}

We don't need the constancy of f to construct the factor
f' : ∥ X ∥ → Y. But we need it to prove that it is a factor:

\begin{code}

 propositional-factorization-equation : {X Y : Type} (x₀ : X) (f : X → Y) (c : constant f) (x : X) 
                                      → propositional-factorization x₀ f c (∣ x ∣) ≡ f x
 propositional-factorization-equation x₀ f c x = c x₀ x

\end{code}

Instead we generalize part of what we did to show that the truncation
of the two-point type has the universal property of the interval:

\begin{code}

 judgemental-factorization : {X Y : Type} (x₀ : X) (f : X → Y) → constant f → ∥ X ∥ → Y
 judgemental-factorization {X} {Y} x₀ f c s = end-point(g' s)
  where
   g : X → paths-from(f x₀)
   g x = f x , c x₀ x
   g' : ∥ X ∥ → paths-from(f x₀)
   g' = truncation-rec (paths-from-is-hprop (f x₀)) g

 judgemental-factorization-equation : {X Y : Type} (x₀ : X) (f : X → Y) (c : constant f)
                                    → (judgemental-factorization x₀ f c) ∘  ∣_∣ ≡ f
 judgemental-factorization-equation x₀ f c = refl

\end{code}

The factorization equation holds judgementally because its proof is
refl. This relies on the (judgemental) η-rule for functions.

What if we instead assume that ∥ X ∥ is inhabited? Solving the problem
in this particular case actually solves the problem in general:

\begin{code}

 factorizable : {X Y : Type} (f : X → Y) → Type
 factorizable {X} {Y} f = Σ \( f' : ∥ X ∥ → Y) → (x : X) → f' ∣ x ∣ ≡ f x 

 observation : {X Y : Type} (f : X → Y) → (∥ X ∥ → factorizable f) → factorizable f
 observation {X} {Y} f F = f' , e
  where
   f' : ∥ X ∥ → Y
   f' s = π₀ (F s) s
   e : (x : X) → f' ∣ x ∣ ≡ f x
   e x = π₁ (F ∣ x ∣) x

 factors-through : {X X' Y : Type} → (X → X') → (X → Y) → Type
 factors-through {X} {X'} {Y} g f = Σ \( f' : X' → Y) → (x : X) → f'(g x) ≡ f x 

 observation-bis : {X X' Y : Type} (g : X → X') (f : X → Y) → (X' → factors-through g f) → factors-through g f
 observation-bis {X} {X'} {Y} g f F = f' , e
  where
   f' : X' → Y
   f' s = π₀ (F s) s
   e : (x : X) → f'(g x) ≡ f x
   e x = π₁ (F(g x)) x

\end{code}

We can consider a stronger notion of constancy of functions f : X → Y,
that forces Y to be inhabited but allows X to be empty.

\begin{code}

 constant-valued : {X Y : Type} → (f : X → Y) → Type
 constant-valued {X} {Y} f = Σ \(y : Y) → (x : X) → y ≡ f x

 observation' : {X Y : Type} (f : X → Y) → factorizable f → ∥ X ∥ → constant-valued f
 observation' f (f' , e) s = f' s , (λ x → ap f' (truncation-path s ∣ x ∣) • e x)

 constant-valued-factorization : {X Y : Type} (f : X → Y) → constant-valued f → ∥ X ∥ → Y
 constant-valued-factorization {X} {Y} f (y , φ) s = end-point(g' s)
  where
   g : X → paths-from y
   g x = f x , φ x
   g' : ∥ X ∥ → paths-from y
   g' = truncation-rec (paths-from-is-hprop y) g

 constant-valued-factorization-equation : {X Y : Type} (f : X → Y) (c : constant-valued f)
                                        → (constant-valued-factorization f c) ∘ ∣_∣ ≡ f
 constant-valued-factorization-equation f c = refl

\end{code}

Observation added 23 Jul:

If X is empty, then any (necessarily constant) f : X → Y is
factorizable. We have seen that this is also the case of X is
inhabited. A common generalization of types that are empty or
inhabited are the hstable types (equivalently, the types that admit
constant endomaps - see
http://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/html/GeneralizedHedberg.html).

Putting the above together, if X is hstable then any constant map out
of it factors through ∥X∥ judgementally:

\begin{code}

 hstable : Type → Type
 hstable X = ∥ X ∥ → X

 hstable-factorization : {X Y : Type} → hstable X → (f : X → Y) → constant f → ∥ X ∥ → Y
 hstable-factorization h f c s = judgemental-factorization (h s) f c s

 hstable-factorization-equation : {X Y : Type} (h : hstable X) (f : X → Y) (c : constant f) 
                               → (hstable-factorization h f c) ∘ ∣_∣ ≡ f
 hstable-factorization-equation h f c = refl

\end{code}

Notice that if we simply compose f with h we get a propositional
factorization.

Notice also that the assumption (hstable X) can be replaced by the
logically equivalent assumption (collapsible X), which amounts to
saying that X admits a constant endomap.

Added 23 July: We can actually get any factorization to be judgemental:

\begin{code}

 judgementalize : {X Y : Type} → (f : X → Y) → factorizable f → ∥ X ∥ → Y
 judgementalize f fa s = constant-valued-factorization f (observation' f fa s) s

 judgementalize-equation : {X Y : Type} (f : X → Y) (fa : factorizable f)
                        → (judgementalize f fa) ∘ ∣_∣ ≡ f
 judgementalize-equation f fa = refl

 judgementalization : {X Y : Type} → (f : X → Y) → factorizable f → factorizable f
 judgementalization f fa = judgementalize f fa , λ x → refl

\end{code}

It is better, at this stage, to produce the judgementalization in one
go, to see all ingredients at once, and, more importantly, because we
will likely need access to internal parts of the construction to prove
things about it:

\begin{code} 

 judgementalize-bis' : {X Y : Type} (f : X → Y) (f' : ∥ X ∥ → Y) (e : (x : X) → f' ∣ x ∣ ≡ f x) 
                     → (s : ∥ X ∥) → paths-from(f' s)
 judgementalize-bis' {X} {Y} f f' e s = g' s 
  where
   φ : (x : X) → f' s ≡ f x
   φ x = ap f' (truncation-path s ∣ x ∣) • e x
   g : X → paths-from(f' s)
   g x = f x , φ x
   g' : ∥ X ∥ → paths-from(f' s)
   g' = truncation-rec (paths-from-is-hprop(f' s)) g

 judgementalize-bis : {X Y : Type} → (f : X → Y) → factorizable f → ∥ X ∥ → Y
 judgementalize-bis {X} {Y} f (f' , e) s = π₀(judgementalize-bis' f f' e s) 

 judgementalize-same-as-judgementalize-bis : {X Y : Type} → judgementalize {X} {Y} ≡ judgementalize-bis {X} {Y}
 judgementalize-same-as-judgementalize-bis = refl

\end{code}

28 Feb 2014.

This should have been included much ealier:

\begin{code} 

 Constant : {X Y : Type} (f : X → Y) → Type
 Constant {X} f = ∥ X ∥ → constant-valued f

 fact-charac₀ : {X Y : Type} (f : X → Y) → factorizable f → Constant f
 fact-charac₀ f (f' , φ) s = (f' s) , (λ x → ap f' (truncation-path s ∣ x ∣) • φ x)

 fact-charac₁ : {X Y : Type} (f : X → Y) → Constant f → factorizable f 
 fact-charac₁ f C = (λ s → π₀ (C s)) , (λ x → π₁ (C ∣ x ∣) x)

\end{code}

So, the logical equivalence of (constant f) and (factorizable f), is
equivalent to the equivalence of (constant f) and (Constant f).


