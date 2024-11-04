


   G e n e r a l i z a t i o n s   o f   H e d b e r g' s   T h e o r e m
   
   under the axioms of extensionality and/or propositional reflection



       Thierry Coquand  University of Gothenburg, Sweden
       Martin Escardo   Univerity of Birmingham, UK
       Nicolai Kraus    University of Nottingham, UK

       7th October 2012

   This file type checks in Agda version 2.3.0.1.


\begin{code} 

{-# OPTIONS --without-K #-}

module GeneralizedHedberg where

open import preliminaries

\end{code}

"x ≡ y" denotes the identity type Id X x y for some implicitly
given X.  Its elements p : x ≡ y are called paths from x to y. 

In Agda, "Set" means "Type", which gives a rather unfortunate clash of
terminology with Homotopy Type Theory (HoTT), where sets are taken to
be certain types, namely those that satisfy the uniqueness of identity
proofs (UIP), that is, of paths. To avoid terminological conflicts, we
define:

\begin{code} 

Type  = Set
Type₁ = Set₁

\end{code}

An (h-)proposition is a type that has at most one element, or,
equivalently, such that there is a path from any point to any other
point:

\begin{code} 

prop : Type → Type
prop X = (x y : X) → x ≡ y

\end{code}

This definition of prop is not exactly the same as Voevodsky's, but is
logically and even weakly equivalent.

Notice that prop X amounts to saying that X is a subsingleton.  For
future reference, notice that it also amounts to saying the identity
function X → X is constant. Of course:

\begin{code} 

∅-is-prop : prop ∅
∅-is-prop x y = ∅-elim x

\end{code}

An (h-)set is a type whose path relation is a proposition:

\begin{code} 

set : Type → Type
set X = {x y : X} → prop(x ≡ y)

\end{code}

We call a type X collapsible if there is a constant map X → X.  The
idea is that such a map collapses X to a single point, if X has a
point. Its image is a sub-singleton, or proposition.

\begin{code}

constant : {X Y : Type} → (f : X → Y) → Type
constant {X} {Y} f = (x y : X) → f x ≡ f y

collapsible : Type → Type
collapsible X = Σ \(f : X → X) → constant f

\end{code}

The empty type ∅ is collapsible, and any inhabited type is
collapsible.

\begin{code}

∅-is-collapsible : collapsible ∅
∅-is-collapsible = (λ x → x) , (λ x → λ ())

inhabited : Type → Type
inhabited X = X

inhabited-is-collapsible : {X : Type} → inhabited X → collapsible X
inhabited-is-collapsible = (λ x → (λ y → x) , (λ y y' → refl))

\end{code}

This suggests that under excluded-middle (EM), all types are
collapsible, and so the collapsibility of all types is a weakening of
EM. In fact, we have more than that: if a particular type is
decidable, then it is is collapsible:

\begin{code} 

empty : Type → Type
empty X = X → ∅

empty-is-collapsible : {X : Type} → empty X → collapsible X
empty-is-collapsible u = ((λ x → x) , (λ x x' → ∅-elim(u x)))

∅-is-collapsible-as-a-particular-case : collapsible ∅
∅-is-collapsible-as-a-particular-case = empty-is-collapsible (λ x → x)

\end{code}

NB. This second inhabitant of collapsible ∅ is not definitionally the
same as the previous one. (This cannot be expressed in Agda or as a
term of MLTT - definitional equality is a meta-level concept.)

\begin{code} 

decidable : Type → Type
decidable X = inhabited X + empty X 

decidable-is-collapsible : {X : Type} → decidable X → collapsible X
decidable-is-collapsible (in₀ x) = inhabited-is-collapsible x
decidable-is-collapsible (in₁ u) = empty-is-collapsible u

EM : Type₁
EM = (X : Type) → decidable X

all-types-are-collapsible-under-EM : EM → (X : Type) → collapsible X
all-types-are-collapsible-under-EM em X = decidable-is-collapsible (em X)

\end{code}

In constructive mathematics a set is customarily called discrete if it
has decidable equality:

\begin{code} 

discrete : Type → Type
discrete X = {x y : X} → decidable(x ≡ y)

\end{code}

With the above terminology, Hedberg's Theorem is that any discrete
type is a set.

The essence of Hedberg's argument is that:

  (i) A type with decidable equality is path-collapsible.
      (Particular case of the above development.)
 
 (ii)  A type is a set if and only if it is path-collapsible.
      (The following development.)

\begin{code} 

path-collapsible : Type → Type
path-collapsible X = {x y : X} → collapsible(x ≡ y)

\end{code}

A type is a set if and only if it is path-collapsible. One direction
is trivial and the other is rather subtle, requiring path-induction
(that is, J) with a non-obvious induction hypothesis.

\begin{code} 

any-set-is-path-collapsible : {X : Type} → set X → path-collapsible X
any-set-is-path-collapsible u = ((λ p → p) , u)

any-path-collapsible-type-is-a-set : {X : Type} → path-collapsible X → set X
any-path-collapsible-type-is-a-set {X} pc p q = trans (claim₀ p) (trans claim₁ (sym(claim₀ q)))
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f = π₀ pc
  g : {x y : X} (p q : x ≡ y) → f p ≡ f q
  g = π₁ pc
  claim₀ : {x y : X} (p : x ≡ y) → p ≡ trans (sym(f refl)) (f p)
  claim₀ = J (λ p → p ≡ trans (sym (f refl)) (f p)) (sym-is-inverse(f refl))
  claim₁ : trans (sym(f refl)) (f p) ≡ trans (sym(f refl)) (f q)
  claim₁ = cong (λ h → trans (sym(f refl)) h) (g p q)
 
discrete-is-path-collapsible : {X : Type} → discrete X → path-collapsible X
discrete-is-path-collapsible d = decidable-is-collapsible d

\end{code}

This is Hedberg's Theorem:

\begin{code} 

corollary₀ : {X : Type} → discrete X → set X
corollary₀ d = any-path-collapsible-type-is-a-set(discrete-is-path-collapsible d)

\end{code}

Two applications of this analysis of Hedberg's argument follow.

The first one is a generalization of Hedberg's Theorem with a caveat:
Hedberg's Theorem doesn't require extensionality but our
"generalization" does. So it is a generalization only in the presence
of extensionality.

\begin{code} 

nonempty : Type → Type
nonempty X = empty(empty X)

stable : Type → Type
stable X = nonempty X → inhabited X
 
decidable-is-stable : {X : Type} → decidable X → stable X
decidable-is-stable (in₀ x) φ = x
decidable-is-stable (in₁ u) φ = ∅-elim(φ u)

separated : Type → Type
separated X = {x y : X} → stable(x ≡ y)

discrete-is-separated : {X : Type} → discrete X → separated X
discrete-is-separated {X} d = decidable-is-stable d

\end{code}

The separatedness condition holds often in constructive mathematics
and its generalizations. E.g. the (Dedekind and Cauchy) reals in a
topos are separated, and so are the Cantor space and the Baire
space. In MLTT, the Cantor space and the Baire space are separated
under the assumption that any two pointwise equal functions are equal
(the axiom of extensionality).

Extensionality for (certain) ∅-valued functions is all we use here,
and as sparsely as possible:

\begin{code} 

extensionality : Type → Type → Type
extensionality X Y = {f g : X → Y} → ((x : X) → f x ≡ g x) → f ≡ g

extensionality-special-case₀ : Type → Type
extensionality-special-case₀ X = extensionality (empty X) ∅

stable-is-collapsible-under-extensionality : 
  {X : Type} → extensionality-special-case₀ X → stable X → collapsible X 
stable-is-collapsible-under-extensionality {X} e s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)
  claim₀ : (x y : X) → (u : empty X) → u x ≡ u y
  claim₀ x y u = ∅-elim(u x)
  claim₁ : (x y : X) → (λ u → u x) ≡ (λ u → u y)
  claim₁ x y = e (claim₀ x y) 
  g : (x y : X) → f x ≡ f y
  g x y = cong s (claim₁ x y)

extensionality-special-case₁ : Type → Type
extensionality-special-case₁ X = {x y : X} → extensionality-special-case₀ (x ≡ y)

separated-is-path-collapsible-under-extensionality : 
  {X : Type} → extensionality-special-case₁ X → separated X → path-collapsible X
separated-is-path-collapsible-under-extensionality e s = stable-is-collapsible-under-extensionality e s

\end{code}

discrete-is-separated shows that the following is a generalization of
Hedberg's theorem under the assumption of extensionality.

\begin{code} 

corollary₁ : {X : Type} → extensionality-special-case₁ X → separated X → set X
corollary₁ e s = any-path-collapsible-type-is-a-set(separated-is-path-collapsible-under-extensionality e s)

\end{code}

We now give a further generalization, assuming the types that are
h-propositions form a reflective subcategory of that of all types.

We define propositional reflection axiomatically, to avoid
impredicativity and resizing axioms.  The axiomatization is given by
postulating the universal property that says that propositions form a
reflective subcategory of the category of types:

\begin{code} 

postulate _* : Type → Type
postulate *-gives-prop : {X : Type} → prop(X *)
postulate η : {X : Type} → X → X *
postulate *-universal-property : (X P : Type) → prop P → (X → P) → (X * → P)

\end{code}

Assuming extensionality, the reflection diagram 

           η {X}
       X -------> X*
        \         .
         \        .          
          \       .    _          _
      ∀ g  \      . ∃! g  (namely g = *-universal-property X P f g)
            \     .
             \    .
              \   .   
               v  v    
                 P

commmutes because any two prop-valued maps are equal by
extensionality.  Moreover, the "extension" of g : X → P to X * → P
is unique for the same reason.  

Voevodsky constructs the propositional reflection as follows, where
he uses a resizing axiom to go down from Type₁ to Type:

\begin{code} 

_*¹ : Type → Type₁
X *¹ = (P : Type) → prop P → (X → P) → P

\end{code}

The large type X *¹ is equivalent to our postulated small type X *:

\begin{code} 

*-universal-property' : (X : Type) → X * → X *¹
*-universal-property' X p P f g = *-universal-property X P f g p

*-universal-property'-converse : (X : Type) → X *¹ → X * 
*-universal-property'-converse X f = f (X *) *-gives-prop η

*-stable : Type → Type
*-stable X = X * → X

*-separated : Type → Type
*-separated X = {x y : X} → *-stable(x ≡ y)

\end{code}

*-separation is a weakening of separation:

\begin{code} 

*-is-stronger-than-nonempty : {X : Type} → X * → nonempty X
*-is-stronger-than-nonempty {X} a u = *-universal-property X ∅ ∅-is-prop u a

*-stability-is-weaker-than-stability : {X : Type} → stable X → *-stable X
*-stability-is-weaker-than-stability {X} s a = s(*-is-stronger-than-nonempty a) 

separated-is-*-separated : {X : Type} → separated X → *-separated X
separated-is-*-separated s a = s(*-is-stronger-than-nonempty a)

\end{code}

Notice that the universal property is not used in the following lemma
and corollary:
  
\begin{code} 

*-stable-is-collapsible :  {X : Type} → *-stable X → collapsible X
*-stable-is-collapsible {X} s = (f , g)
 where 
  f : X → X
  f x = s(η x)
  claim₀ : (x y : X) → η x ≡ η y
  claim₀ x y = *-gives-prop (η x) (η y)
  g : (x y : X) → f x ≡ f y
  g x y = cong s (claim₀ x y)

*-separated-is-path-collapsible :  {X : Type} → *-separated X → path-collapsible X
*-separated-is-path-collapsible {X} s = *-stable-is-collapsible s

\end{code}

By separated-is-*-separated, this is a further generalization of
Hedberg's Theorem.

\begin{code} 

corollary₂ : {X : Type} → *-separated X → set X
corollary₂ s = any-path-collapsible-type-is-a-set(*-separated-is-path-collapsible s)

\end{code}

This is as far as we can get in our generalization, because the converse holds:

\begin{code} 

any-prop-is-*-stable : {X : Type} → prop X → *-stable X
any-prop-is-*-stable {X} ui a = *-universal-property X X ui (λ x → x) a

any-set-is-*-separated : {X : Type} → set X → *-separated X
any-set-is-*-separated uip a = any-prop-is-*-stable uip a

\end{code}

Hence we have proved that the following are logically equivalent:

    (i) X is a set
   (ii) X is path-collapsible
  (iii) X is *-separated

Because decidability implies separation, which in turn implies
*-separation, Hedberg's theorem follows from this.

We haven't thought about the possibility of examples that are
*-separated but not already separated.  In any case, this gives an
example showing that to assume A* → A for any A is unreasonable,
because then we would get UIP for all types, and we know that there
are (intended HoTT) models in which this fails. But the assumption
that A* → A for all A looks much more unreasonable than that. Is it
classical? Very likely. What is exactly it status?

Some speculative code follows. Can the gap be filled? Maybe not. Can a
suitable alternative P be found to prove the conjecture with the
following strategy? Or do we further need to assume that X is a set
(as above)?

-- \begin{code} 

conjecture:collapsible-is-*-stable : {X : Type} → collapsible X → *-stable X
conjecture:collapsible-is-*-stable {X} (f , g) a = π₀ lemma
 where
  P : Type
  P = Σ \(y : X) → (x : X) → f x ≡ y
  P-is-prop : prop P
  P-is-prop = {!!}
  X-gives-P : X → P
  X-gives-P x = (f x , (λ x' → g x' x))
  lemma : P
  lemma = *-universal-property X P P-is-prop X-gives-P a

-- \end{code}

Notice that this argument shows at least that

 set X → collapsible X → *-stable X

since if set X then Q y  =  (x : X) → f x = y is a proposition and we have
Q x → Q x' → x = x' and so prop P.

More generally we can ask:

-- \begin{code} 

conjecture:η-is-universal-constant-map : {X Y : Type} (f : X → Y) → constant f → (X * → Y)
conjecture:η-is-universal-constant-map {X} {Y} f  g a = π₀ lemma
 where
  P : Type
  P = Σ \(y : Y) → (x : X) → f x ≡ y
  P-is-prop : prop P
  P-is-prop = ?
  X-gives-P : X → P
  X-gives-P x = (f x , (λ x' → g x' x))
  lemma : P
  lemma = *-universal-property X P P-is-prop X-gives-P a

-- \end{code}

The reason this is interesting is that it would mean than X* is the
quotient of X by the chaotic relation that relates any two points. The
reason is that being constant amounts to transforming the chaotic
relation into the identity relation, and hence the previous property
is the universal property of the quotient by the chaotic relation.