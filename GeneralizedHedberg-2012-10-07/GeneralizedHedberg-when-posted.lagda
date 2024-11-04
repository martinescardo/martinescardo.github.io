


   G e n e r a l i z a t i o n s   o f   H e d b e r g' s   T h e o r e m
   
   under the axioms of extensionality and/or hpropositional reflection


       Thorsten Altenkirch University of Nottingham, UK
       Thierry  Coquand    University of Gothenburg, Sweden
       Martin   Escardo    University of Birmingham, UK
       Nicolai  Kraus      University of Nottingham, UK

       12th October 2012, last updated 28 November 2012

   This file type checks in Agda version 2.3.2


I n t r o d u c t i o n

Hedberg's Theorem says that any type with decidable equality satisfies
the uniqueness of identity proofs (UIP), or equivalently, is an hset.

We say that a type X is collapsible if there is a constant map X → X,
and that a type X is path-collapsible if the path space x ≡ y is
collapsible for all x,y: X.

We claim that the essence of Hedberg's argument is this:

  (i) If a type is path-collapsible then it is an hset.  
 (ii) A type with decidable equality is path-collapsible.

Condition (i) also gives immediately the well-known fact that
hpropositions are hsets.

We apply this analysis of Hedberg's argument to develop two
generalizations of Hedberg's theorem, by successively weakening the
decidability hypothesis:

 (1) If a type X is separated then X is path-collapsible and hence an hset.

     The hypothesis means that if the path type x ≡ y is nonempty then
     it is inhabited, for any two points x,y: X.

     The conclusion requires the axiom of extensionality for ∅-valued
     functions, where ∅ is the empty type.


 (2) If a type X is hseparated then X is path-collapsible and hence an hset.

     The hypothesis means that if the path type x ≡ y is hinhabited
     then it is inhabited.

     The proof this time doesn't rely on extensionality, but the very
     formulation of this fact of course requires that hpropositional
     reflections, denoted by hinhabited, exist.


Decidable equality (also known as discreteness) implies separatedness
assuming extensionality of ∅-valued functions, which in turn implies
hseparatedness. Hence in the presence of extensionality and
hpropositional reflection, (2) generalizes (1), which in turn
generalizes Hedberg's theorem.

This is as far as one can go in this sequence of weakenings of the
discreteness hypothesis in Hedberg's Theorem, because

     If X is an hset then X must be hseparated.

In summary, we prove that the following are logically equivalent:

    (i) X is an hset.
   (ii) X is path-collapsible.
  (iii) X is hseparated.

Because discreteness implies separation, which in turn implies
hseparation, Hedberg's theorem follows from this.

Generalizing part of the above, we also prove, with a non-trivial
argument, that the following are logically equivalent:

   (ii') X is collapsible.
  (iii') X is inhabited if it is hinhabited (we say that X is hstable).


Organization.
------------

    1. Weakenings of the hypothesis of Hedberg's Theorem.
    2. collapsible X <-> hstable X.
    3. A type size reduction without resizing axioms.
    4. Taboos and counter-models.

The last two sections are motivated by technical considerations
arising in the previous two, and hence we don't discuss them in this
introduction. They include some open questions.

We now proceed to the technical development.

\begin{code} 

{-# OPTIONS --without-K #-}

module GeneralizedHedberg where

open import mini-library

\end{code}

-----------------------------------------------------------
-- 1. Weakenings of the hypothesis of Hedberg's Theorem. --
-----------------------------------------------------------

"x ≡ y" denotes the identity type Id X x y for some implicitly
given X.  Its elements p : x ≡ y are called paths from x to y. 

In Agda, "Set" means "Type", which gives a rather unfortunate clash of
terminology with Homotopy Type Theory (HoTT), where (h-)sets are taken
to be certain types, which amount to those that satisfy the uniqueness
of identity proofs (UIP), that is, of paths. To avoid terminological
conflicts, we define:

\begin{code} 

Type  = Set
Type₁ = Set₁

\end{code}

The following definition of hproposition is not quite the same as
Voevodsky's, but is logically and even (weakly) equivalent. An
hproposition is a type that has at most one element, or, equivalently,
such that there is a path from any point to any other point.

\begin{code} 

hprop : Type → Type
hprop X = (x y : X) → x ≡ y

\end{code}

This amounts to saying that X is a subsingleton.  For future
reference, notice that it also amounts to saying that the identity
function X → X is constant. Of course:

\begin{code} 

∅-is-hprop : hprop ∅
∅-is-hprop x y = ∅-elim x

\end{code}

An hset amounts to a type whose path relation is an hproposition:

\begin{code} 

hset : Type → Type
hset X = {x y : X} → hprop(x ≡ y)

\end{code}

We call a type X collapsible if there is a constant map X → X.  The
idea is that such a map collapses X to a single point, if X has a
point, and that its image is a sub-singleton, or hproposition.

\begin{code}

constant : {X Y : Type} → (f : X → Y) → Type
constant {X} {Y} f = (x y : X) → f x ≡ f y

collapsible : Type → Type
collapsible X = Σ \(f : X → X) → constant f

path-collapsible : Type → Type
path-collapsible X = {x y : X} → collapsible(x ≡ y)

\end{code}

A type is an hset if and only if it is path-collapsible. One direction
is trivial and the other is rather subtle, requiring path-induction
(that is, Martin-Löf's J eliminator) with a non-obvious induction
hypothesis (claim₀).

\begin{code} 

hset-is-path-collapsible : {X : Type} → hset X → path-collapsible X
hset-is-path-collapsible u = (id , u)

path-collapsible-is-hset : {X : Type} → path-collapsible X → hset X
path-collapsible-is-hset {X} pc p q = claim₂
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f = π₀ pc
  g : {x y : X} (p q : x ≡ y) → f p ≡ f q
  g = π₁ pc
  claim₀ : {x y : X} (r : x ≡ y) → r ≡ (f refl)⁻¹ • (f r)
  claim₀ = J (λ r → r ≡ ((f refl)⁻¹) • (f r)) (sym-is-inverse(f refl))
  claim₁ : (f refl)⁻¹ • (f p) ≡ (f refl)⁻¹ • (f q)
  claim₁ = cong (λ h → (f refl)⁻¹ • h) (g p q)
  claim₂ : p ≡ q
  claim₂ = (claim₀ p) • claim₁ • (claim₀ q)⁻¹ 

\end{code}

An immediate consequence is the well-known fact that hpropositions are
hsets:

\begin{code} 
 
hprop-is-path-collapsible : {X : Type} → hprop X → path-collapsible X
hprop-is-path-collapsible h {x} {y} = ((λ p → h x y) , (λ p q → refl))

hprop-is-hset : {X : Type} → hprop X → hset X
hprop-is-hset h = path-collapsible-is-hset(hprop-is-path-collapsible h)

\end{code}

To arrive at Hedberg's Theorem and its generalizations discussed
above, we investigate collapsible types.

The empty type ∅ is collapsible, and any inhabited type is
collapsible.

\begin{code}

∅-is-collapsible : collapsible ∅
∅-is-collapsible = (λ x → x) , (λ x → λ ())

inhabited : Type → Type
inhabited X = X

inhabited-is-collapsible : {X : Type} → inhabited X → collapsible X
inhabited-is-collapsible x = ((λ y → x) , λ y y' → refl)

\end{code}

This suggests that under excluded-middle (EM), all types are
collapsible, and so the collapsibility of all types is a weakening of
EM. In fact, we have more than that: if a particular type is
decidable, then it is is collapsible:

\begin{code} 

empty : Type → Type
empty X = inhabited(X → ∅)

empty-is-collapsible : {X : Type} → empty X → collapsible X
empty-is-collapsible u = (id , (λ x x' → ∅-elim(u x)))

∅-is-collapsible-as-a-particular-case : collapsible ∅
∅-is-collapsible-as-a-particular-case = empty-is-collapsible id

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

all-types-are-hsets-under-EM : EM → (X : Type) → hset X
all-types-are-hsets-under-EM em X = path-collapsible-is-hset(λ {x} {y} → all-types-are-collapsible-under-EM em (x ≡ y))

\end{code}

In constructive mathematics a set is customarily called discrete if it
has decidable equality:

\begin{code} 

discrete : Type → Type
discrete X = {x y : X} → decidable(x ≡ y)

discrete-is-path-collapsible : {X : Type} → discrete X → path-collapsible X
discrete-is-path-collapsible d = decidable-is-collapsible d

\end{code}

With the above terminology, Hedberg's Theorem is that any discrete
type is an hset:

\begin{code} 

discrete-is-hset : {X : Type} → discrete X → hset X
discrete-is-hset d = path-collapsible-is-hset(discrete-is-path-collapsible d)

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
topos are separated, and so are the Cantor space and the Baire space,
but they are not discrete. In MLTT, the Cantor space and the Baire
space are separated under the assumption that any two pointwise equal
functions are equal (the axiom of extensionality).

Extensionality for (certain) ∅-valued functions is all we use here,
and as sparsely as possible:

\begin{code} 

extensionality : Type → Type → Type
extensionality X Y = {f g : X → Y} → ((x : X) → f x ≡ g x) → f ≡ g

extensionality-special-case₀ : Type → Type
extensionality-special-case₀ X = extensionality (empty X) ∅

stable-is-collapsible : {X : Type} → extensionality-special-case₀ X → stable X → collapsible X 
stable-is-collapsible {X} e s = (f , g)
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
extensionality-special-case₁ X = {x y : X} → extensionality-special-case₀(x ≡ y)

separated-is-path-collapsible : {X : Type} → extensionality-special-case₁ X → separated X → path-collapsible X
separated-is-path-collapsible e s = stable-is-collapsible e s

\end{code}

discrete-is-separated shows that the following is a generalization of
Hedberg's theorem under the assumption of extensionality.

\begin{code} 

separated-is-hset : {X : Type} → extensionality-special-case₁ X → separated X → hset X
separated-is-hset e s = path-collapsible-is-hset(separated-is-path-collapsible e s)

\end{code}

We now give a further generalization, assuming the types that are
hpropositions form a reflective subcategory of that of all types.

We define hpropositional reflection axiomatically, to avoid
impredicativity and resizing axioms.  The axiomatization is given by
postulating the universal property of the reflection, with the
reflector called hinhabited. The universal property is given by the
(non-dependent) eliminator.

\begin{code} 

postulate hinhabited : Type → Type
postulate hinhabited-is-hprop : {X : Type} → hprop(hinhabited X)
postulate η : {X : Type} → X → hinhabited X
postulate hinhabited-elim : (X P : Type) → hprop P → (X → P) → (hinhabited X → P)

\end{code}

Assuming extensionality, the reflection diagram 

           η {X}
       X -------> hinhabited X
        \         .
         \        .          
          \       .    _          _
      ∀ g  \      . ∃! g  (namely g = hinhabited-elim X P f g)
            \     .
             \    .
              \   .   
               v  v    
                 P

commmutes because any two hprop-valued maps are equal by
extensionality.  Moreover, the "extension" of g : X → P to a map
hinhabited X → P is unique for the same reason.

Voevodsky constructs the hpropositional reflection as follows, where
he uses a resizing axiom to go down from Type₁ to Type:

\begin{code} 

hinhabited₁ : Type → Type₁
hinhabited₁ X = (P : Type) → hprop P → (X → P) → P

\end{code}

This can be read as saying that X is hinhabited iff every hproposition
implied by X is inhabited.

The large type (hinhabited₁ X) is equivalent to our postulated small
type (hinhabited X):

\begin{code} 

hinhabited-elim' : (X : Type) → hinhabited X → hinhabited₁ X
hinhabited-elim' X p P f g = hinhabited-elim X P f g p

hinhabited-elim'-converse : (X : Type) → hinhabited₁ X → hinhabited X 
hinhabited-elim'-converse X f = f (hinhabited X) hinhabited-is-hprop η

hstable : Type → Type
hstable X = hinhabited X → inhabited X

hseparated : Type → Type
hseparated X = {x y : X} → hstable(x ≡ y)

\end{code}

hinhabitation is a weakening of inhabitation and a strenghening of
nonemptiness.

\begin{code} 

inhabited-is-hinhabited : {X : Type} → inhabited X → hinhabited X
inhabited-is-hinhabited = η

hinhabited-is-nonempty : {X : Type} → hinhabited X → nonempty X
hinhabited-is-nonempty {X} a u = hinhabited-elim X ∅ ∅-is-hprop u a

\end{code}

Hence hseparation is a weakening of separation:

\begin{code} 

stable-is-hstable : {X : Type} → stable X → hstable X
stable-is-hstable {X} s a = s(hinhabited-is-nonempty a) 

separated-is-hseparated : {X : Type} → separated X → hseparated X
separated-is-hseparated s a = s(hinhabited-is-nonempty a)

\end{code}
    
Notice that the universal property is not used in the following lemma
and corollary:
  
\begin{code} 

hstable-is-collapsible :  {X : Type} → hstable X → collapsible X
hstable-is-collapsible {X} s = (f , g)
 where 
  f : X → X
  f x = s(η x)
  claim₀ : (x y : X) → η x ≡ η y
  claim₀ x y = hinhabited-is-hprop (η x) (η y)
  g : (x y : X) → f x ≡ f y
  g x y = cong s (claim₀ x y)

hseparated-is-path-collapsible :  {X : Type} → hseparated X → path-collapsible X
hseparated-is-path-collapsible s = hstable-is-collapsible s

\end{code}

By separated-is-hseparated, the following is a further generalization
of Hedberg's Theorem:

\begin{code} 

hseparated-is-hset : {X : Type} → hseparated X → hset X
hseparated-is-hset s = path-collapsible-is-hset(hseparated-is-path-collapsible s)

\end{code}

This is as far as we can get in our sequence of weakenings of the
hypothesis of Hedberg's Theorem, because the converse holds:

\begin{code} 

hprop-is-hstable : {X : Type} → hprop X → hstable X
hprop-is-hstable {X} h a = hinhabited-elim X X h id a

hset-is-hseparated : {X : Type} → hset X → hseparated X
hset-is-hseparated h a = hprop-is-hstable h a

\end{code}

Hence we have proved that the following are logically equivalent:

    (i) X is an hset.
   (ii) X is path-collapsible.
  (iii) X is hseparated.

Because discreteness implies separation, which in turn implies
hseparation, Hedberg's theorem follows from this.

We haven't thought about the possibility of meaningful examples that
are hseparated but not already separated.  In any case, the above
shows that to assume that every type is hstable is unreasonable,
because then all types would be hsets, and we know that there are
(intended HoTT) models in which this fails. But the assumption that
all types are hstable looks much more unreasonable than that. Is it
classical?  Very likely. What is its status exactly? See Section 4.


--------------------------------------
--  2. collapsible X <-> hstable X. --
--------------------------------------

Next we prove that the following are logically equivalent:

   (ii') X is collapsible.
  (iii') X is hstable.

In order to establish this, we need a non-trivial lemma, due to
Nicolai Kraus, which is interesting in its own right. It asserts that
the type of fixed points of any constant endomap is an hproposition.

\begin{code} 

fix : {X : Type} → (f : X → X) → Type
fix f = Σ \x → x ≡ f x

from-fix : {X : Type} (f : X → X) → fix f → X
from-fix f = π₀

to-fix : {X : Type} (f : X → X) → constant f → X → fix f
to-fix f g x = (f x , g x (f x))

\end{code}

The key insight for the proof of Kraus Lemma is the following:

    If f : X → Y is constant, then f maps any path x ≡ x to the
    trivial path refl.

We need to prove a slightly more general version.

\begin{code} 

key-insight-generalized : {X Y : Type} (f : X → Y) (g : constant f) {x y : X} (p : x ≡ y) 
                       → cong f p ≡ (g x x)⁻¹ • (g x y) 
key-insight-generalized f g {x} {y} = 
  J (λ {x} {y} p → cong f p ≡ (g x x)⁻¹ • (g x y)) (λ {x} → sym-is-inverse(g x x))

key-insight : {X Y : Type} (f : X → Y) → constant f → {x : X} (p : x ≡ x) → cong f p ≡ refl
key-insight f g p = (key-insight-generalized f g p) • ((sym-is-inverse(g _ _))⁻¹) 

\end{code}

We need that substitution of equalities in equalities can be described
as composition.  We prove a fairly general version and the version we
actually need.

\begin{code} 

transport-paths-along-paths : {X Y : Type} {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x) 
                           → subst p q ≡ (cong h p)⁻¹ • q • (cong k p)
transport-paths-along-paths {X} {Y} {x} p h k q = 
 J' x (λ p → subst p q ≡ ((cong h p)⁻¹) • q • (cong k p)) (refl-is-right-id q) p

transport-paths-along-paths' : {X : Type} {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x) 
                            → subst {X} {λ z → z ≡ f z} p q ≡ p ⁻¹ • q • (cong f p)
transport-paths-along-paths' {X} {x} p f q = 
 (transport-paths-along-paths p (λ z → z) f q) • (cong (λ pr → pr ⁻¹ • q • (cong f p)) ((cong-id-is-id p)⁻¹))

\end{code}

The main ingredients of Kraus Lemma are the possibility to write
substitution of equalities in equalities as composition, and of course
what we have called the "key insight" above.

\begin{code} 

Kraus-Lemma : {X : Type} → (f : X → X) → constant f → hprop(fix f)
Kraus-Lemma {X} f g (x , p) (y , q) = 
  -- p : x ≡ f x
  -- q : y ≡ f y
  (x , p)        ≡⟨ split x y p p' r refl ⟩
  (y , p')       ≡⟨ split y y p' q s t ⟩∎           
  (y , q) ∎
    where
     r : x ≡ y
     r = x ≡⟨ p ⟩
       f x ≡⟨ g x y ⟩
       f y ≡⟨ q ⁻¹ ⟩∎
         y ∎
     p' : y ≡ f y
     p' = subst r p
     s : y ≡ y
     s = y   ≡⟨ p' ⟩
         f y ≡⟨ q ⁻¹ ⟩∎
         y   ∎
     q' : y ≡ f y
     q' = subst {X} {λ y → y ≡ f y} s p'
     t : q' ≡ q
     t = q'                         ≡⟨ transport-paths-along-paths' s f p' ⟩
         s ⁻¹ • (p' • cong f s)     ≡⟨ cong (λ pr → s ⁻¹ • (p' • pr)) (key-insight f g s) ⟩
         s ⁻¹ • (p' • refl)         ≡⟨ cong (λ pr → s ⁻¹ • pr) ((refl-is-right-id p')⁻¹)  ⟩
         s ⁻¹ • p'                  ≡⟨ refl  ⟩
         (p' • (q ⁻¹))⁻¹ • p'       ≡⟨ cong (λ pr → pr • p') ((sym-trans p' (q ⁻¹))⁻¹)  ⟩
         ((q ⁻¹)⁻¹ • (p' ⁻¹)) • p'  ≡⟨ cong (λ pr → (pr • (p' ⁻¹)) • p') ((sym-sym-trivial q)⁻¹) ⟩
         (q • (p' ⁻¹)) • p'         ≡⟨ trans-assoc q (p' ⁻¹) p'  ⟩
         q • ((p' ⁻¹) • p')         ≡⟨ cong (λ pr → q • pr) ((sym-is-inverse p')⁻¹) ⟩
         q • refl                   ≡⟨ (refl-is-right-id q)⁻¹  ⟩∎
         q  ∎

\end{code}

As discussed above, our main motivation for this lemma is to show that
any collapsible type is hstable, that is, 

  collapsible X → (hinhabited X → X).

We can equivalently write this as

  hinhabited X → (collapsible X → X).

This says that if X is hinhabited, then from any constant function 
f : X → X we can inhabit X, which may be surprising. Of course, this
inhabitant of X will be a fixed point of f and hence the constant
value of f.

More generally, we can ask what is necessary to know about X in order
to inhabit X from any given constant function X → X.

It is natural to conjecture that the weakest condition is that X is
hinhabited.  But in fact there is a weaker condition.

We define (populated₁ X), and show that we have a logical equivalence

  (collapsible X → X) ⇔ populated₁ X.

The large type (populated₁ X) is defined in the same way as the large
type (hinhabited₁ X), but quantifying over the sub-hpropositions of X,
rather than all hpropositions, so that

 hinhabited X → populated₁ X, and populated₁ X → nonempty X.

The type (populated₁ X) is an hproposition, assuming extensionality
and ignoring size issues, which is larger than (hinhabited X), as the
map hinhabited X → populated₁ X is trivially a monomorphism. 

A small version of populated₁ is constructed in the next section,
using the results of this section.

As already discussed, hinhabited₁ X can be read as saying that any
hproposition implied by X is inhabited. Likewise, populated₁ X can be
read as saying that any hproposition that is logically equivalent to
X must be inhabited:

\begin{code} 

populated₁ : Type → Type₁
populated₁ X = (P : Type) → hprop P → (P → X) → (X → P) → P

hinhabited-is-populated₁ : {X : Type} → hinhabited X → populated₁ X
hinhabited-is-populated₁ {X} hi P h a b = hinhabited-elim X P h b hi

populated₁-is-hinhabited-under-hstability : {X : Type} → hstable X → populated₁ X → hinhabited X
populated₁-is-hinhabited-under-hstability {X} s po = po (hinhabited X) hinhabited-is-hprop s η 

\end{code}

Of course, it shouldn't be the case that (populated₁ X → hinhabited X)
in general.  But how does one argue about this conjecture? The trouble
is that excluded middle does give that. So we should get a "taboo" out
of (populated₁ X → hinhabited X) to establish the conjecture, or, as a
last resource, provide a counter-model. This conjecture is similar in
this respect to the conjecture that ((X : Type) → collapsible X)
should "fail". This is investigated in Section 4.

Of course:

\begin{code} 

populated₁-is-nonempty : {X : Type} → populated₁ X → nonempty X
populated₁-is-nonempty p = p ∅ (∅-is-hprop) ∅-elim

\end{code}

We now prove the logical equivalence (collapsible X → X) ⇔ populated₁ X
and derive collapsible X → hstable X as a corollary.

\begin{code} 

D : Type → Type
D X = collapsible X → X

D-is-populated₁ : {X : Type} → D X → populated₁ X
D-is-populated₁ {X} d P h a b = b x
 where
  f : X → X
  f x = a(b x)
  g : constant f
  g x y = cong a (h (b x) (b y))
  x : X
  x = d(f , g) 

populated₁-is-D : {X : Type} → populated₁ X → D X 
populated₁-is-D {X} p (f , g) = 
 from-fix f (p (fix f) (Kraus-Lemma f g) (from-fix f) (to-fix f g))

\end{code}

A special case of this is the following (recall that we have proved
above that hstable-is-collapsible, and that hstable X means that
hinhabited X → X):

\begin{code} 

collapsible-is-hstable : {X : Type} → collapsible X → hstable X
collapsible-is-hstable c hi = populated₁-is-D (hinhabited-is-populated₁ hi) c

\end{code}

This seems to generalize the main step of the original version of
Hedberg's Theorem:

\begin{code} 

path-collapsible-is-hset-bis : {X : Type} → path-collapsible X → hset X
path-collapsible-is-hset-bis c = hseparated-is-hset(collapsible-is-hstable c)

\end{code}

But this is cheating, because hseparated-is-hset uses Hedberg's original proof.

Finally, we can combine both directions:

\begin{code} 

both-directions-combined : {X : Type} → ((populated₁ X → X) → X) → populated₁ X
both-directions-combined {X} hypothesis = D-is-populated₁ fact₁
 where
  fact₀ : collapsible X → (populated₁ X → X) 
  fact₀ c p = populated₁-is-D p c

  fact₁ : D X 
  fact₁ c = hypothesis(fact₀ c)

both-directions-combined-converse : {X : Type} → populated₁ X → ((populated₁ X → X) → X)
both-directions-combined-converse p u = u p

both-directions-combined-bis : {X : Type} → ((hinhabited X → X) → X) → populated₁ X
both-directions-combined-bis {X} hypothesis = D-is-populated₁(λ c → hypothesis(collapsible-is-hstable c))

\end{code}

Notice that "populated₁" doesn't seem to be functorial, for the same
reasons that D X doesn't seem to be functorial. This gives further
support to the conjecture that (populated₁ X → hinhabited X) ought to
fail (in the sense of being a taboo or having a counter-model). See
Section 4.

This concludes the main development. 

--------------------------------------------------------
--  3. A type size reduction without resizing axioms. --
--------------------------------------------------------

Next we show that the large type (populated₁ X) is equivalent to a
small definable type (populated X), which is an hproposition, without
using hpropositional reflections.

The proof that φ defined below is constant uses extensionality. There
is an alternative construction of φ, given later, that doesn't use
extensionality but uses hpropositional reflections.  (It seems that
hpropositional reflection has some built-in amount of
extensionality. Does it imply some instance of extensionality?)

Notice that the type D X (=collapsible X → X) is empty if X is empty,
and is inhabited if X is inhabited (and more generally if X is
populated₁, as we have seen above). Of course we cannot in general
decide whether X is empty or inhabited, or that the type D X is empty
or inhabited.

But the following illustrates that there are types that can be shown
to have constant endomaps (and hence to be hstable) without knowledge
of whether they are empty or inhabited.

\begin{code} 

postulate extensionality-special-case₂ : {X : Type} → extensionality (collapsible X) X

φ : (X : Type) → D X → D X
φ X h (f , g) = f(h(f , g))

\end{code}

To understand this, recall that D X = collapsible X → X where
collapsible X = Σ \(f : X → X) → constant f.  

Then the inputs of φ are

   h : collapsible X → X
   f : X → X
   g : constant f

and hence

   (f , g) : collapsible X.

Now h(f , g) : X, but this doesn't need to be the constant value of
the function f : X → X. Hence we apply f to h(f , g) to force it to be
the constant value of f. Because f is constant, φ defined in this way
is pointwise constant, and hence constant by extensionality:

\begin{code} 

φ-constant : (X : Set) → constant(φ X)
φ-constant X h k = extensionality-special-case₂(claim₁ h k)
 where
  claim₀ : (h k : D X) → (f : X → X) → (g : constant f) → φ X h (f , g) ≡ φ X k (f , g)
  claim₀ h k f g = g (h(f , g)) (k(f , g))
  claim₁ : (h k : D X) → (c : collapsible X) → φ X h c ≡ φ X k c
  claim₁ h k (f , g) = claim₀ h k f g

populated : Type → Type
populated X = fix(φ X)

populated-is-hprop : (X : Type) → hprop(populated X)
populated-is-hprop X = Kraus-Lemma (φ X) (φ-constant X)

populated-is-D : {X : Type} → populated X → D X
populated-is-D {X} = from-fix (φ X)

D-is-populated : {X : Type} → D X → populated X
D-is-populated {X} = to-fix (φ X) (φ-constant X)

populated-is-populated₁ : {X : Type} → populated X → populated₁ X
populated-is-populated₁ po = D-is-populated₁(populated-is-D po)

populated₁-is-populated : {X : Type} → populated₁ X → populated X
populated₁-is-populated po = D-is-populated(populated₁-is-D po)

\end{code}

The last two functions are isomorphisms as the two types are
hpropositions, and hence we have a (weak) equivalence.

The following can be proved by reduction to populated₁, but the given
proof avoids detours via large types:

\begin{code} 

inhabited-is-populated : {X : Type} → X → populated X
inhabited-is-populated {X} x = D-is-populated (λ c → x)

populated-is-nonempty : {X : Type} → populated X → nonempty X
populated-is-nonempty {X} (f , g) u = u(f(h , h-constant)) 
 where
  h : X → X
  h = ∅-elim ∘ u
  h-constant : (x y : X) → h x ≡ h y
  h-constant x y = ∅-elim(u x)

\end{code}

Similarly, the facts that hinhabited-is-populated and that
collapsible-is-hstable can be proved without a detour via large types.

Q u e s t i o n.  It is hence natural to ask whether it is possible to
perform a similar type size reduction to show that inhabited₁ X has a
small definable counter-part, in particular getting rid of postulates
and resizing axioms to define hinhabited X.

Hence we formulate:

P r o b l e m.  Prove (by exhibiting a construction within type
theory) or disprove (by exhibiting a counter-model or using
syntactical arguments or reducing to a taboo) that there is a
definable type constructor hinhabited : Type → Type such that
hinhabited X ⇔ hinhabited₁ X. This problem can be considered with and
without assuming extensionality axioms, and with and without assuming
univalence, and with or without considering universes, etc. 

D i s c u s s i o n   o f   t h e   p r o b l e m.  
We have inhabited₁ X → populated X, and this map (and any such map) is
a monomorphism embedding the large type inhabited₁ X into the small
type populated X.  Can a small version of inhabited₁ X be carved out
of the small type populated X? A difficulty is that that inhabited₁ X
cannot be a retract of populated X, because this would amount to the
existence of a map populated X → inhabited₁ X, which is shown to be
impossible in general in Section 4. But there may be other ways of
getting a small copy of inhabited₁ X out of the small type populated X.  
It is unclear at the time of writing whether the large type
inhabited₁ X can be made small without axioms. Of course, it may be
natural to conjecture that it cannot. But we don't know. At least it
is interesting to know that it is monomorphically embedded into a
small definable type. This is analogous to the fact that a subset of a
finite set doesn't need to be finite.


Ignoring this question, next we show that if we instead assume (small)
hpropositional reflections, we don't need to assume extensionality to
perform the above size reduction from populated₁ x to populated X.

To do this, it is convenient to first define the monad structure on
hinhabited coming from the reflection. To define it as a Kleisli
triple, it remains to define the Kleisli extension operator (following
standard category theory):

\begin{code} 

hinhabited-extension : {X Y : Type} → (X → hinhabited Y) → (hinhabited X → hinhabited Y)
hinhabited-extension {X} {Y} f p = hinhabited-elim X (hinhabited Y) hinhabited-is-hprop f p

\end{code}

The Kleisli-triple laws are trivial, because they are equations
between hproposition-valued functions. We formulate them pointwise to
avoid extensionality.

\begin{code} 

kleisli-law₀ : {X : Type} (p : hinhabited X) → hinhabited-extension η p ≡ p 
kleisli-law₀ p = hinhabited-is-hprop (hinhabited-extension η p) p

kleisli-law₁ : {X Y : Type} → (f : X → hinhabited Y) → (x : X) → (hinhabited-extension f)(η x) ≡ f x
kleisli-law₁ {X} {Y} f x = hinhabited-is-hprop ((hinhabited-extension f)(η x)) (f x)

kleisli-law₂ : {X Y Z : Type} → (f : X → hinhabited Y) → (g : Y → hinhabited Z) → (p : hinhabited X) →
 hinhabited-extension((hinhabited-extension g) ∘ f) p  ≡ (hinhabited-extension g)(hinhabited-extension f p)
kleisli-law₂ f g p = 
 hinhabited-is-hprop (hinhabited-extension((hinhabited-extension g) ∘ f) p) ((hinhabited-extension g)(hinhabited-extension f p)) 

\end{code}

Now the standard data that defines the monad (which automatically
satisfies the monad laws (pointwise)):

\begin{code} 

hinhabited-functor : {X Y : Type} → (X → Y) → hinhabited  X → hinhabited  Y 
hinhabited-functor f = hinhabited-extension(η ∘ f)

μ : {X : Type} → hinhabited(hinhabited  X) → hinhabited  X 
μ = hinhabited-extension id

\end{code}

Because the functor is enriched (that is, internally defined) and the
category of types is cartesian closed, the monad is strong:

\begin{code} 

hinhabited-strength : {X Y : Type} → X × hinhabited Y → hinhabited(X × Y)
hinhabited-strength (x , q) = hinhabited-functor(λ y → (x , y)) q

hinhabited-shift : {X Y : Type} → hinhabited X × hinhabited Y → hinhabited(X × Y)
hinhabited-shift (p , q) = hinhabited-extension(λ x → hinhabited-strength(x , q)) p

\end{code}

This time we prove directly that a certain type is hstable without
knowing whether it is empty or inhabited:

\begin{code} 

hstable-example : (X : Type) → hstable(D X)
hstable-example X h c = x
 -- h : hinhabited(D X)
 -- c : collapsible X
 where
  p : hinhabited(collapsible X × D X)
  p = hinhabited-strength(c , h)
  f : collapsible X × D X → X
  f(c , φ) = φ c
  q : hinhabited X
  q = hinhabited-functor f p
  x : X
  x = collapsible-is-hstable c q 
  
collapsible-example-bis : (X : Type) → collapsible(D X)
collapsible-example-bis X = hstable-is-collapsible(hstable-example X)

\end{code}

Hence alternatively we can take:

\begin{code} 

φ-bis : (X : Type) → D X → D X
φ-bis X = π₀(collapsible-example-bis X)

φ-constant-bis : (X : Type) → constant(φ-bis X)
φ-constant-bis X = π₁(collapsible-example-bis X)

\end{code}

There is yet another natural way of definining the small type
populated X:

populated X = (f : X → X) → constant f → fix f

This says that a type is populated iff every constant endomap has a
fixed point, and hence we can inhabit the type given any constant
endomap.

Again it is easy to show that populated X ⇔ D X, using the above
ideas. We leave the details to the reader. But to show that 
populated X is an hproposition we need the dependent version of
function extensionality, using the fact that fix f is an hproposition.


------------------------------------
--  4. Taboos and counter-models. --
------------------------------------

We want to undertand the differences between the various notions of
inhabitation, hinhabitation, population and nonemptiness. We use two
techniques, namely taboos (expressed in Agda) and HoTT models
(expressed in our meta-language, namely mathematical English).

We have the chain of implications

   inhabited X → hinhabited X → populated X → nonempy X.

All implications can be reversed if excluded middle holds. 

Conversely, from the assumption that any of them can be reversed, for
all types X, we get a constructively dubious instance of excluded
middle (a constructive taboo) or that all types are hsets (a HoTT
taboo, backed by a counter-model).

A particularly nice implication to reverse would be 

   hinhabited X → populated X.

In that case we would have

   hinhabited X ⇔ populated X.

This would answer positively the open question of Section 3, showing
that hinhabited : Type → Type is MLTT+extensionality definable,
because populated : Type → Type is definable, as we have seen in
Section 3, and because logical equivalence of hpropositions amounts to
isomorphism (and in turn to homotopy equivalence (called weak
equivalence for historical reasons)). 

"Unfortunately", the reversal of this implication is a taboo, and so
are all reversals.

We have already investigated the reversal of the implication 

  inhabited X → hinhabited X

to some extent.

When this reversal can be performed, we said that X is hstable. This
reversal can be performed when X is empty, and when X is inhabited,
but not necessarily in the absence of knowledge of which is the
case. In fact, we have already argued, but not proved in Agda, that:

\begin{code} 

all-types-are-hstable-is-a-HoTT-taboo : ((X : Type) → hstable X) → ((X : Type) → hset X)
all-types-are-hstable-is-a-HoTT-taboo h _ = hseparated-is-hset(h(_ ≡ _))

\end{code}

This is an application of our generalization hseparated-is-hset of
Hedberg's Theorem.

We have seen that a type X is hstable iff it is collapsible, using
Kraus Lemma. Thus, saying that all types are hstable amounts to saying
that every type has a constant endofunction. This reduction is nice
because the notion of collapsibility can be understood without
reference to the notion of hpropositional reflection.

That every type X has a constant endofunction is rather dubious from a
constructive point of view, bearing in mind that X may or may not be
empty, but we have no means of knowing in general which case
holds. But, in any case, it is a HoTT taboo, as shown above, and hence
we have:

   M e t a - t h e o r e m.  It is not provable in MLTT that every
   type has a constant endofunction, or in MLTT+hinhabited that every
   type is hstable.

The reason is that simplicial sets form a model of (homotopy) type
theory in which type variables can be interpreted as spaces that are
not necessarily hsets. This can be seen as a negative application of
homotopy models of MLTT. Of course, people are mostly interested in
their positive applications.

It turns out that the reversal of the implication 
(hinhabited X → populated X) is also related to hstability or
equivalently collapsibility, as discussed below.

In light of the above, the following is perhaps surprising: although
we cannot necessarily inhabit the type (hstable X), we can always
populate it:

\begin{code}

populated₁-hstable : {X : Type} → populated₁(hstable X)
populated₁-hstable {X} P h a b = f u
 -- h : hprop P
 -- a : P → hstable X
 -- b : hstable X → P
 where
  u : X → P
  u x = b(λ _ → x)

  f : (X → P) → P
  f u = b hstable-X
   where
    g : hinhabited X → P
    g hi = hinhabited-elim X P h u hi
    hstable-X' : hinhabited X → hinhabited X → X
    hstable-X' = a ∘ g
    hstable-X : hinhabited X → X
    hstable-X hi = hstable-X' hi hi

populated-hstable : {X : Type} → populated(hstable X)
populated-hstable = populated₁-is-populated populated₁-hstable

nonempty-hstable : {X : Type} → nonempty(hstable X)
nonempty-hstable = populated₁-is-nonempty populated₁-hstable

\end{code}

We can now understand why it is not necessarily the case that every
populated type is hinhabited:

   Every populated type is hinhabited iff every type h-has a constant endomap.

\begin{code} 

one-direction : ((X : Type) → populated X → hinhabited X) → ((X : Type) → hinhabited(collapsible X))
one-direction a X = hinhabited-functor hstable-is-collapsible (a (hstable X) populated-hstable)

\end{code}

A stronger version of the converse has already been proved above
(populated₁-is-hinhabited-under-hstability):

\begin{code} 

other-direction : ((X : Type) → hinhabited(collapsible X)) → ((X : Type) → populated X → hinhabited X)
other-direction f X po = hinhabited-functor (populated-is-D po) (f X)

\end{code}

By the first direction, if every hinhabited type were populated, then
for every type X we would have

  hinhabited(hset X),

because hinhabited is functorial. But, assuming extensionality, the
type (hset X) is an hproposition, as is well known. And for any
hproposition P we have hinhabited P → P by hinhabited-elim, and hence
we would have (hset X) for any X. This shows that

   M e t a - t h e o r e m.  It is not provable that every populated
   type is hinhabited.

This holds assuming function extensionality, and hence also without
assuming it.


It remains to discuss the reversal of the implication 
populated X → nonempty X.

The type (decidable P), where P is any hproposition, is an example of
a nonempty, collapsible type whose (h)inhabitation is a taboo:

\begin{code} 

nonempty-decidable : {X : Type} → nonempty(decidable X)
nonempty-decidable d = d(in₁(λ x → d(in₀ x)))

postulate extensionality-special-case₃ : {X : Type} → extensionality X ∅

∅-valued-functions-are-equal : {X : Type} → hprop(empty X)
∅-valued-functions-are-equal {X} f g = extensionality-special-case₃ {X} (λ x → ∅-elim(f x))

hhd   : {P : Type} → hprop P → hprop(decidable P)
hhd h (in₀ p) (in₀ q) = cong in₀ (h p q)
hhd h (in₀ p) (in₁ v) = ∅-elim(v p)
hhd h (in₁ u) (in₀ q) = ∅-elim(u q)
hhd {P} h (in₁ u) (in₁ v) = cong in₁ (∅-valued-functions-are-equal u v)

hcd : {P : Type} → hprop P → collapsible(decidable P)
hcd {P} h = (id , hhd h)

\end{code}

We know that populated-is-nonempty. From the above we conclude that
the converse is a constructive taboo, in the sense that it implies
h-excluded middle, which in turn implies weak excluded middle:

\begin{code} 

hEM : Type₁
hEM = (P : Type) → hprop P → decidable P

wEM : Type₁
wEM = (X : Type) → decidable(empty X)

hEM-implies-wEM : hEM → wEM
hEM-implies-wEM hem X = hem (empty X) ∅-valued-functions-are-equal

all-nonempty-types-are-populated-taboo : ((X : Type) → nonempty X → populated X) → hEM
all-nonempty-types-are-populated-taboo a P h = populated-is-D p c
 where
  p : populated(decidable P)
  p = a (decidable P) nonempty-decidable
  c : collapsible(decidable P)
  c = hcd h

\end{code}

We have argued that not every type is collapsible by reducing to a
HoTT taboo and exhibiting a counter-model. It would be much nicer to
instead derive a constructive taboo from the hypothetical
collapsibility of all types, expressed in Agda, in a fragment of the
language corresponding to MLTT, possibly extended with function
extensionality.

