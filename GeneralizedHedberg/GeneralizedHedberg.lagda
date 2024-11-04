


   G e n e r a l i z a t i o n s   o f   H e d b e r g' s   T h e o r e m

   under the axioms of extensionality and/or hpropositional reflection


       Thorsten Altenkirch University of Nottingham, UK
       Thierry  Coquand    University of Gothenburg, Sweden
       Martin   Escardo    University of Birmingham, UK
       Nicolai  Kraus      University of Nottingham, UK

       12th October 2012, last updated 29 November 2012.
       Total separatedness added 16 Feb 2013 flying over the atlantic ocean.
       Choice discussion added 12 Mar 2013.

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
    2. collapsible X ⇔ hstable X.
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

constant : {X Y : Type} → (X → Y) → Type
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
  claim₁ = ap (λ h → (f refl)⁻¹ • h) (g p q)
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
Hedberg's Theorem doesn't require function extensionality but our
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
functions are equal (the axiom of function extensionality).

Extensionality for (certain) ∅-valued functions is all we use here,
and as sparsely as possible:

\begin{code}

funext : Type → Type → Type
funext X Y = {f g : X → Y} → ((x : X) → f x ≡ g x) → f ≡ g

funext-special-case₀ : Type → Type
funext-special-case₀ X = funext (empty X) ∅

stable-is-collapsible : {X : Type} → funext-special-case₀ X → stable X → collapsible X
stable-is-collapsible {X} e s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)
  claim₀ : (x y : X) → (u : empty X) → u x ≡ u y
  claim₀ x y u = ∅-elim(u x)
  claim₁ : (x y : X) → (λ u → u x) ≡ (λ u → u y)
  claim₁ x y = e (claim₀ x y)
  g : (x y : X) → f x ≡ f y
  g x y = ap s (claim₁ x y)

funext-special-case₁ : Type → Type
funext-special-case₁ X = {x y : X} → funext-special-case₀(x ≡ y)

separated-is-path-collapsible : {X : Type} → funext-special-case₁ X → separated X → path-collapsible X
separated-is-path-collapsible e s = stable-is-collapsible e s

\end{code}

discrete-is-separated shows that the following is a generalization of
Hedberg's theorem under the assumption of function extensionality.

\begin{code}

separated-is-hset : {X : Type} → funext-special-case₁ X → separated X → hset X
separated-is-hset e s = path-collapsible-is-hset(separated-is-path-collapsible e s)

\end{code}

We now give a further generalization, assuming the types that are
hpropositions form a reflective subcategory of that of all types.

We define hpropositional reflection axiomatically, to avoid
impredicativity and resizing axioms, which are not available in Agda
anyway.  The axiomatization is given by postulating the universal
property of the reflection, with the reflector called hinhabited. The
universal property is given by the (non-dependent) eliminator.

\begin{code}

postulate hinhabited : Type → Type
postulate hprop-hinhabited : {X : Type} → hprop(hinhabited X)
postulate η : {X : Type} → X → hinhabited X
postulate hinhabited-elim : (X P : Type) → hprop P → (X → P) → (hinhabited X → P)
postulate hinhabited-ind : {X : Type} {P : hinhabited X → Type} → ((s : hinhabited X) → hprop(P s)) → ((x : X) → P (η x)) → (s : hinhabited X) → P s

\end{code}

Assuming function extensionality, the reflection diagram

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

commmutes because any two hprop-valued maps are equal by function
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
hinhabited-elim'-converse X f = f (hinhabited X) hprop-hinhabited η

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

hstable-is-collapsible : {X : Type} → hstable X → collapsible X
hstable-is-collapsible {X} s = (f , g)
 where
  f : X → X
  f x = s(η x)
  claim₀ : (x y : X) → η x ≡ η y
  claim₀ x y = hprop-hinhabited (η x) (η y)
  g : (x y : X) → f x ≡ f y
  g x y = ap s (claim₀ x y)

hseparated-is-path-collapsible : {X : Type} → hseparated X → path-collapsible X
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


A p p e n d i x   t o   t h i s   s e c t i o n.

Another class of examples of types that are hsets is that of totally
separated types. Notice that the type (totally-separated X) is an
hproposition, assuming function extensionality.  A type is totally
separated if any two points satisfying the same decidable properties
are equal.

\begin{code}

₂-discrete : discrete ₂
₂-discrete {₀} {₀} = in₀ refl
₂-discrete {₀} {₁} = in₁(λ())
₂-discrete {₁} {₀} = in₁(λ())
₂-discrete {₁} {₁} = in₀ refl

totally-separated : Type → Type
totally-separated X = {x y : X} → ((p : X → ₂) → p x ≡ p y) → x ≡ y

dependent-funext : Type₁
dependent-funext = {X : Type} {Y : X → Type} {f g : (x : X) → Y x} → ((x : X) → f x ≡ g x) → f ≡ g

totally-separated-is-hset : dependent-funext → (X : Type) → totally-separated X → hset X
totally-separated-is-hset de X t = path-collapsible-is-hset h
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f r = t(λ p → ap p r)
  b : {x y : X} (φ γ : (p : X → ₂) → p x ≡ p y) → φ ≡ γ
  b φ γ = de(λ p → discrete-is-hset ₂-discrete (φ p) (γ p))
  c : {x y : X} (r s : x ≡ y) → (λ p → ap p r) ≡ (λ p → ap p s)
  c r s = b(λ p → ap p r) (λ p → ap p s)
  g : {x y : X} → constant(f {x} {y})
  g r s = ap t (c r s)
  h : path-collapsible X
  h {x} {y} = f , g

\end{code}

There is a better and shorter proof than the above by showing that
totally separated spaces are separated, and concluding the hset
condition from that. This also avoids dependent function
extensionality (but in any case it is known that dependent
extensionality follows from extensionality).

\begin{code}

contra-positive : {R X Y : Type} → (X → Y) → (Y → R) → (X → R)
contra-positive f p x = p(f x)

₂-separated : separated ₂
₂-separated = discrete-is-separated ₂-discrete

totally-separated-is-separated : {X : Type} → totally-separated X → separated X
totally-separated-is-separated {X} t {x} {y} φ = t h
 where
  a : (p : X → ₂) → nonempty(p x ≡ p y)
  a p = φ ∘ contra-positive(ap p)
  h : (p : X → ₂) → p x ≡ p y
  h p = ₂-separated(a p)

totally-separated-is-hset' : {X : Type} → funext-special-case₁ X → totally-separated X → hset X
totally-separated-is-hset' e t = separated-is-hset e (totally-separated-is-separated t)

\end{code}

Here is another application of (the main lemma
path-collapsible-is-hset of) Hedberg's theorem (17 Feb 2013):

\begin{code}

injective : {X Y : Type} → (f : X → Y) → Type
injective {X} f = {x x' : X} → f x ≡ f x' → x ≡ x'

subtype-of-hset-is-hset : {X Y : Type} (m : X → Y) → injective m → hset Y → hset X
subtype-of-hset-is-hset {X} m i h = path-collapsible-is-hset(f , g)
 where
  f : {x x' : X} → x ≡ x' → x ≡ x'
  f r = i(ap m r)
  g : {x x' : X} (r s : x ≡ x') → f r ≡ f s
  g r s = ap i (h (ap m r) (ap m s))


π₀-injective : {X : Type} {Y : X → Type} → ({x : X} → hprop(Y x)) → injective π₀
π₀-injective {X} {Y} f {u} {v} r = lemma r (π₁ u) (π₁ v) (f(transport {X} {Y} r (π₁ u)) (π₁ v))
 where
  A : {x x' : X} → x ≡ x' → Type
  A {x} {x'} r = (y : Y x) (y' : Y x') → transport r y ≡ y' → (x , y) ≡ (x' , y')

  lemma : {x x' : X} (r : x ≡ x') → A {x} {x'} r
  lemma = J A (λ {x} x' y → ap (λ y → (x , y)))


subset-of-hset-is-hset : (X : Type) (Y : X → Type) → hset X → ({x : X} → hprop(Y x)) → hset(Σ \(x : X) → Y x)
subset-of-hset-is-hset X Y h p = subtype-of-hset-is-hset π₀ (π₀-injective p) h

\end{code}


-------------------------------------
--  2. collapsible X ⇔ hstable X. --
-------------------------------------

Next we prove that the following are logically equivalent:

   (ii') X is collapsible.
  (iii') X is hstable.

In order to establish this, we need a non-trivial lemma, due to
Nicolai Kraus, which is interesting in its own right. It asserts that
the type of fixed points of any constant endomap is an hproposition.

\begin{code}

fix : {X : Type} → (f : X → X) → Type
fix f = Σ \x → x ≡ f x

\end{code}

The key insight for the proof of Kraus Lemma is the following:

    If f : X → Y is constant, then f maps any path x ≡ x to the
    trivial path refl.

We need to prove a slightly more general version.

\begin{code}

Kraus-Lemma₀ : {X Y : Type} (f : X → Y) (g : constant f) {x y : X} (p : x ≡ y) → ap f p ≡ (g x x)⁻¹ • (g x y)
Kraus-Lemma₀ f g {x} {y} = J (λ {x} {y} p → ap f p ≡ (g x x)⁻¹ • (g x y)) (λ {x} → sym-is-inverse(g x x))

Kraus-Lemma₁ : {X Y : Type} (f : X → Y) → constant f → {x : X} (p : x ≡ x) → ap f p ≡ refl
Kraus-Lemma₁ f g p = (Kraus-Lemma₀ f g p) • ((sym-is-inverse(g _ _))⁻¹)

\end{code}

We need that transport of equalities in equalities can be described as
composition.  We prove a fairly general version and the version we
actually need.

\begin{code}

transport-paths-along-paths : {X Y : Type} {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x)
                           → transport p q ≡ (ap h p)⁻¹ • q • (ap k p)
transport-paths-along-paths {X} {Y} {x} p h k q =
 J' x (λ p → transport p q ≡ ((ap h p)⁻¹) • q • (ap k p)) (refl-is-right-id q) p

transport-paths-along-paths' : {X : Type} {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x)
                            → transport {X} {λ z → z ≡ f z} p q ≡ p ⁻¹ • q • (ap f p)
transport-paths-along-paths' {X} {x} p f q =
 (transport-paths-along-paths p (λ z → z) f q) • (ap (λ pr → pr ⁻¹ • q • (ap f p)) ((ap-id-is-id p)⁻¹))

\end{code}

We are now ready to prove the fixed-point lemma:

\begin{code}

Kraus-Lemma : {X : Type} (f : X → X) → constant f → hprop(fix f)
Kraus-Lemma {X} f g (x , p) (y , q) =
  -- p : x ≡ f x
  -- q : y ≡ f y
  (x , p)        ≡⟨ Σ-≡ x y p p' r refl ⟩
  (y , p')       ≡⟨ Σ-≡ y y p' q s t ⟩
  (y , q) ∎
    where
     r : x ≡ y
     r = x ≡⟨ p ⟩
       f x ≡⟨ g x y ⟩
       f y ≡⟨ q ⁻¹ ⟩
         y ∎
     p' : y ≡ f y
     p' = transport r p
     s : y ≡ y
     s = y   ≡⟨ p' ⟩
         f y ≡⟨ q ⁻¹ ⟩
         y   ∎
     q' : y ≡ f y
     q' = transport {X} {λ y → y ≡ f y} s p'
     t : q' ≡ q
     t = q'                          ≡⟨ transport-paths-along-paths' s f p' ⟩
         s ⁻¹ • (p' • ap f s)        ≡⟨ ap (λ pr → s ⁻¹ • (p' • pr)) (Kraus-Lemma₁ f g s) ⟩
         s ⁻¹ • (p' • refl)          ≡⟨ ap (λ pr → s ⁻¹ • pr) ((refl-is-right-id p')⁻¹)  ⟩
         s ⁻¹ • p'                   ≡⟨ refl  ⟩
         ((p' • q ⁻¹ • refl)⁻¹) • p' ≡⟨ ap (λ pr → ((p' • pr)⁻¹) • p') ((refl-is-right-id (q ⁻¹))⁻¹) ⟩
         (p' • (q ⁻¹))⁻¹ • p'        ≡⟨ ap (λ pr → pr • p') ((sym-trans p' (q ⁻¹))⁻¹)  ⟩
         ((q ⁻¹)⁻¹ • (p' ⁻¹)) • p'   ≡⟨ ap (λ pr → (pr • (p' ⁻¹)) • p') ((sym-sym-trivial q)⁻¹) ⟩
         (q • (p' ⁻¹)) • p'          ≡⟨ trans-assoc q (p' ⁻¹) p'  ⟩
         q • ((p' ⁻¹) • p')          ≡⟨ ap (λ pr → q • pr) ((sym-is-inverse p')⁻¹) ⟩
         q • refl                    ≡⟨ (refl-is-right-id q)⁻¹  ⟩
         q  ∎

\end{code}

It is now easy to prove that collapsible types are hstable:

\begin{code}

from-fix : {X : Type} (f : X → X) → fix f → X
from-fix f = π₀

to-fix : {X : Type} (f : X → X) → constant f → X → fix f
to-fix f g x = (f x , g x (f x))

collapsible-is-hstable : {X : Type} → collapsible X → hstable X
collapsible-is-hstable {X} (f , g) hi = from-fix f l
 --  f : X → X
 --  g : constant f
 -- hi : hinhabited X
 where
  h : X → fix f
  h = to-fix f g
  k : hinhabited X → fix f
  k = hinhabited-elim X (fix f) (Kraus-Lemma f g) h
  l : fix f
  l = k hi

\end{code}

This amounts to

  collapsible X → (hinhabited X → X),

which can equivalently be written as

  hinhabited X → (collapsible X → X).

This says that if X is hinhabited, then from any constant function
f : X → X we can inhabit X, which may be surprising. This inhabitant
of X is a fixed point of f and hence the constant value of f.

More generally, we can ask what is necessary to know about X in order
to inhabit X from any given constant function X → X.

It is natural to conjecture that the weakest condition is that X is
hinhabited.  But in fact there is a seemingly weaker condition.

We define (populated₁ X), and show that we have a logical equivalence

  populated₁ X ⇔ (collapsible X → X).


The large type (populated₁ X) is defined in the same way as the large
type (hinhabited₁ X), but quantifying over the sub-hpropositions of X,
rather than all hpropositions, so that

 hinhabited X → populated₁ X, and populated₁ X → nonempty X.

The type (populated₁ X) is an hproposition, assuming function
extensionality and ignoring size issues, which is larger than
(hinhabited X), as the map hinhabited X → populated₁ X is trivially a
monomorphism.

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
populated₁-is-hinhabited-under-hstability {X} s po = po (hinhabited X) hprop-hinhabited s η

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

populated₁-is-D : {X : Type} → populated₁ X → D X
populated₁-is-D {X} p (f , g) = from-fix f (p (fix f) (Kraus-Lemma f g) (from-fix f) (to-fix f g))

D-is-populated₁ : {X : Type} → D X → populated₁ X
D-is-populated₁ {X} d P h a b = b x
 where
  f : X → X
  f x = a(b x)
  g : constant f
  g x y = ap a (h (b x) (b y))
  x : X
  x = d(f , g)

\end{code}

We have already proved a special case of this:

\begin{code}

collapsible-is-hstable-bis : {X : Type} → collapsible X → hstable X
collapsible-is-hstable-bis c hi = populated₁-is-D (hinhabited-is-populated₁ hi) c

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

The proof that φ defined below is constant uses function
extensionality. There is an alternative construction of φ, given
later, that doesn't use extensionality but uses hpropositional
reflections.  (It seems that hpropositional reflection has some
built-in amount of extensionality. Does it imply some instance of
extensionality?)

Notice that the type D X (=collapsible X → X) is empty if X is empty,
and is inhabited if X is inhabited (and more generally if X is
populated₁, as we have seen above). Of course we cannot in general
decide whether X is empty or inhabited, or that the type D X is empty
or inhabited.

But the following illustrates that there are types that can be shown
to have constant endomaps (and hence to be hstable) without knowledge
of whether they are empty or inhabited.

\begin{code}

postulate funext-special-case₂ : {X : Type} → funext (collapsible X) X

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
is pointwise constant, and hence constant by function extensionality:

\begin{code}

φ-constant : (X : Type) → constant(φ X)
φ-constant X h k = funext-special-case₂(claim₁ h k)
 where
  claim₀ : (h k : D X) → (f : X → X) → (g : constant f) → φ X h (f , g) ≡ φ X k (f , g)
  claim₀ h k f g = g (h(f , g)) (k(f , g))
  claim₁ : (h k : D X) → (c : collapsible X) → φ X h c ≡ φ X k c
  claim₁ h k (f , g) = claim₀ h k f g

populated : Type → Type
populated X = fix(φ X)

hprop-populated : (X : Type) → hprop(populated X)
hprop-populated X = Kraus-Lemma (φ X) (φ-constant X)

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

   Q u e s t i o n.  It is hence natural to ask whether it is possible
   to perform a similar type size reduction to show that inhabited₁ X
   has a small definable counter-part, in particular getting rid of
   postulates and resizing axioms to define hinhabited X.

Hence we formulate:

   P r o b l e m.  Prove (by exhibiting a construction within type
   theory) or disprove (by exhibiting a counter-model or using
   syntactical arguments or reducing to a taboo) that there is a
   definable type constructor hinhabited : Type → Type such that
   hinhabited X ⇔ hinhabited₁ X. This problem can be considered with
   and without assuming extensionality axioms, and with and without
   assuming univalence, and with or without considering universes,
   etc.

   D i s c u s s i o n   o f   t h e   p r o b l e m.
   We have inhabited₁ X → populated X, and this map (and any such map)
   is a monomorphism embedding the large type inhabited₁ X into the
   small type populated X.  Can a small version of inhabited₁ X be
   carved out of the small type populated X? A difficulty is that that
   inhabited₁ X cannot be a retract of populated X, because this would
   amount to the existence of a map populated X → inhabited₁ X, which
   is shown to be unlikely in Section 4. But there may be other ways
   of getting a small copy of inhabited₁ X out of the small type
   populated X.  It is unclear at the time of writing whether the
   large type inhabited₁ X can be made small without axioms. Of
   course, it may be natural to conjecture that it cannot. But we
   don't know. At least it is interesting to know that it is
   monomorphically embedded into a small definable type. This is
   analogous to the fact that a subset of a finite set doesn't need to
   be finite.


Ignoring this question, next we show that if we instead assume (small)
hpropositional reflections, we don't need to assume extensionality to
perform the above size reduction from populated₁ x to populated X.

To do this, it is convenient to first define the monad structure on
hinhabited coming from the reflection. To define it as a Kleisli
triple, it remains to define the Kleisli extension operator (following
standard category theory):

\begin{code}

hinhabited-extension : {X Y : Type} → (X → hinhabited Y) → (hinhabited X → hinhabited Y)
hinhabited-extension {X} {Y} f p = hinhabited-elim X (hinhabited Y) hprop-hinhabited f p

\end{code}

The Kleisli-triple laws are trivial, because they are equations
between hproposition-valued functions. We formulate them pointwise to
avoid extensionality.

\begin{code}

kleisli-law₀ : {X : Type} (p : hinhabited X) → hinhabited-extension η p ≡ p
kleisli-law₀ p = hprop-hinhabited (hinhabited-extension η p) p

kleisli-law₁ : {X Y : Type} → (f : X → hinhabited Y) → (x : X) → (hinhabited-extension f)(η x) ≡ f x
kleisli-law₁ {X} {Y} f x = hprop-hinhabited ((hinhabited-extension f)(η x)) (f x)

kleisli-law₂ : {X Y Z : Type} → (f : X → hinhabited Y) → (g : Y → hinhabited Z) → (p : hinhabited X) →
 hinhabited-extension((hinhabited-extension g) ∘ f) p  ≡ (hinhabited-extension g)(hinhabited-extension f p)
kleisli-law₂ f g p =
 hprop-hinhabited (hinhabited-extension((hinhabited-extension g) ∘ f) p) ((hinhabited-extension g)(hinhabited-extension f p))

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

Can them be reversed in general?

  1. If the first implication can be reversed, then all types are
     hsets (a homotopy type theory taboo, which is not valid e.g. in
     the model of simplicial sets).

  2. We don't know the answer for the middle implication, which is the
     most interesting one, but we reduce it to a simpler question.

  3. If the last implication can be reversed, we get excluded middle
     for hpropositions, and weak excluded middle for arbitrary types
     (a constructive taboo, which is not valid in recursive models).

It would be wonderful to be able to reverse the middle implication,
because then we would have that hinhabited is MLTT definable as

   hinhabited X = populated X,

answering positively the open question of Section 3. We very much
doubt that this is the case, but we don't know.

We now discuss each of the three implications in the order they are
given above.


4.1. We have already investigated the reversal of the implication

   inhabited X → hinhabited X

to some extent.

When this reversal can be performed, we said that X is hstable. This
reversal can be performed when X is empty, and when X is inhabited,
but not necessarily in the absence of knowledge of which is the
case. In fact, we have already argued, but not proved in Agda, that:

\begin{code}

HoTT-taboo : Type₁
HoTT-taboo = (X : Type) → hset X

all-types-are-hstable-is-a-HoTT-taboo : ((X : Type) → hstable X) → HoTT-taboo
all-types-are-hstable-is-a-HoTT-taboo h _ = hseparated-is-hset(h(_ ≡ _))

\end{code}

This is an application of our generalization hseparated-is-hset of
Hedberg's Theorem.

Because a type is hstable iff it is collapsible, we see that saying
that all types are hstable amounts to saying that every type has a
constant endofunction. This reduction is nice because the notion of
collapsibility can be understood without reference to the notion of
hpropositional reflection.

That every type X has a constant endofunction is rather dubious from a
constructive point of view, bearing in mind that X may or may not be
empty, but we have no means of knowing in general which case
holds. Both empty and inhabited types have constant endomaps, but
defined in different ways. In any case, it is a HoTT taboo, as shown
above, and hence we have:

   M e t a - t h e o r e m.  It is not provable in MLTT that every
   type has a constant endofunction, or in MLTT+hinhabited that every
   type is hstable.

We have argued that not every type is collapsible by reducing to a
HoTT taboo and exhibiting a counter-model. It would be much nicer to
instead derive a constructive taboo from the hypothetical
collapsibility of all types, expressed in Agda, in a fragment of the
language corresponding to MLTT, possibly extended with function
extensionality.


4.2. It turns out that the reversal of the implication

   hinhabited X → populated X

is also related to hstability or equivalently collapsibility, as
discussed below, in two ways.

Firstly, pstability is logically equivalent to hstability, which is
part of the reason why the reversibility of the implication
hinhabited X → populated X is a difficult question.

\begin{code}

pstable : Type → Type
pstable X = populated X → X

pstable-is-hstable : (X : Type) → pstable X → hstable X
pstable-is-hstable X p h = p(populated₁-is-populated(hinhabited-is-populated₁ h))

hstable-is-pstable : (X : Type) → hstable X → pstable X
hstable-is-pstable X h p = populated-is-D p (hstable-is-collapsible h)

\end{code}

Secondly, in light of the above, the following is perhaps surprising:
although we cannot necessarily inhabit the type (hstable X), we can
always populate it:

\begin{code}

populated₁-hstable : {X : Type} → populated₁(hstable X)
populated₁-hstable {X} P h a b = b hs
 -- h : hprop P
 -- a : P → hstable X
 -- b : hstable X → P
 where
  u : X → P
  u x = b(λ _ → x)
  g : hinhabited X → P
  g hi = hinhabited-elim X P h u hi
  hs : hinhabited X → X
  hs hi = a (g hi) hi

populated-hstable : {X : Type} → populated(hstable X)
populated-hstable = populated₁-is-populated populated₁-hstable

nonempty-hstable : {X : Type} → nonempty(hstable X)
nonempty-hstable = populated₁-is-nonempty populated₁-hstable

\end{code}

Using this, we show that the implication (hinhabited X → populated X)
can be reversed for all X if and only if the type (hstable X) is
hinhabited for all X.

\begin{code}

populated-inhabited-charac : ((X : Type) → populated X → hinhabited X) → ((X : Type) → hinhabited(hstable X))
populated-inhabited-charac f X = f (hstable X) populated-hstable

populated-inhabited-charac' : ((X : Type) → hinhabited(hstable X)) → ((X : Type) → populated X → hinhabited X)
populated-inhabited-charac' f X po =
 hinhabited-extension (λ h → populated₁-is-hinhabited-under-hstability h (populated-is-populated₁ po)) (f X)

\end{code}


   P r o b l e m.  Prove that

      (X : Type) → hinhabited(hstable X)

   by exhibiting a construction, or show that no such construction is
   possible by reduction to a taboo or by the use of a counter-model.


We don't expect such a construction to exist. If it is not possible,
an argument with a taboo rather than a counter-model would be
preferable.

4.3. It remains to discuss the reversal of the implication

   populated X → nonempty X.

The type (decidable P), where P is any hproposition, is an example of
a nonempty, collapsible type whose (h)inhabitation is a taboo:

\begin{code}

nonempty-decidable : {X : Type} → nonempty(decidable X)
nonempty-decidable d = d(in₁(λ x → d(in₀ x)))

postulate funext-special-case₃ : {X : Type} → funext X ∅

∅-valued-functions-are-equal : {X : Type} → hprop(empty X)
∅-valued-functions-are-equal {X} f g = funext-special-case₃ {X} (λ x → ∅-elim(f x))

hhd : {P : Type} → hprop P → hprop(decidable P)
hhd h (in₀ p) (in₀ q) = ap in₀ (h p q)
hhd h (in₀ p) (in₁ v) = ∅-elim(v p)
hhd h (in₁ u) (in₀ q) = ∅-elim(u q)
hhd h (in₁ u) (in₁ v) = ap in₁ (∅-valued-functions-are-equal u v)

hcd : {P : Type} → hprop P → collapsible(decidable P)
hcd h = (id , hhd h)

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

A d d e n d u m (12 Mar 2013).


hAC is the (h-)proposition

  (X : Type) (Y : X → Type)

     → ((x : X) → hinhabited(Y x)) → hinhabited((x : X) → Y x).


We show that hEM (defined above) gives a weak form of hAC:

  (X Y : Type) → (X → hinhabited Y) → hinhabited(X → Y).


First we prove some "choice" facts that don't depend on hEM.

The first proof is obtained automatically by Agda with Ctrl-C Ctrl-A,
but we give a proof organized in steps, which we found before trying
to get an automatic proof, which is

   b (λ x → a (h x P hP (λ p → a p x) (λ y → b (λ _ → y))) x),

after we renamed some variables to match the names below.

The term pAC below normalizes to λ {X} {Y} h P hP a b →
  b (λ x → a (h x P hP (λ p → a p x) (λ y → b (λ _ → y))) x).

\begin{code}

pAC : {X Y : Type} → (X → populated₁ Y) → populated₁(X → Y)
pAC {X} {Y} h P hP a b = b hs
 -- h : X → populated Y
 -- hP : hprop P
 -- a : P → X → Y
 -- b : (X → Y) → P
 where
  u : X → Y → P      -- We could try (x : X) → Y x → P with Y : X → Type
  u x y = b(λ _ → y) -- But this line breaks with Y : X → Type.
  g : X → populated₁ Y → P
  -- po : (P : Type) → hprop P → (P → Y) → (Y → P) → P
  g x po = po P hP (λ p → a p x) (λ y → u x y)
  hs : X → Y
  hs x = a (g x (h x)) x

mixed-AC : {X Y : Type} → (X → hinhabited Y) → populated₁(X → Y)
mixed-AC f = pAC (λ x → hinhabited-is-populated₁(f x))

weak-mixed-AC : {X Y : Type} → (X → hinhabited Y) → nonempty(X → Y)
weak-mixed-AC {X} {Y} p = populated₁-is-nonempty (mixed-AC p)

DN : {R X Y : Type} → (X → Y) → ((X → R) → R) → ((Y → R) → R)
DN f = contra-positive(contra-positive f)

weak-hAC : hEM → {X Y : Type} → (X → hinhabited Y) → hinhabited(X → Y)
weak-hAC hem {X} {Y} h = f hEM-special-case
 where
  hEM-special-case : hinhabited(X → Y) + empty(hinhabited(X → Y))
  hEM-special-case = hem (hinhabited(X → Y)) hprop-hinhabited
  fact : nonempty(X → Y)
  fact = weak-mixed-AC h
  claim : nonempty(X → Y) → nonempty(hinhabited(X → Y))
  claim = DN η
  f : hinhabited(X → Y) + empty(hinhabited(X → Y)) → hinhabited(X → Y)
  f (in₀ hi) = hi
  f (in₁ nhi) = ∅-elim(claim fact nhi)

very-weak-hAC : hEM → {X : Type} → hinhabited(hstable X)
very-weak-hAC hem {X} = weak-hAC hem id

\end{code}

Does {X : Type} → hinhabited(hstable X) imply hEM?

More modestly, does  {X Y : Type} → (X → hinhabited Y) → hinhabited(X → Y)
imply hEM?

Actually, this is not more modest (26 Mar 2013):

\begin{code}

hh→hh : ((X : Type) → hinhabited(hstable X)) → (X Y : Type) → (X → hinhabited Y) → hinhabited(X → Y)
hh→hh hh X Y f = hinhabited-functor (λ p → (π₁ p) ∘ (π₀ p)) lemma
 where
  lemma : hinhabited ((X → hinhabited Y) × (hinhabited Y → Y))
  lemma = hinhabited-strength (f , hh Y)

hh←hh : ((X Y : Type) → (X → hinhabited Y) → hinhabited(X → Y)) → (X : Type) → hinhabited(hstable X)
hh←hh hh X = hh (hinhabited X) X id

\end{code}


A d d e n d u m  (22 Mar 2013)

A local version of Hedberg's theorem, using J' (Paulin-Mohring)
instead of J to get the localization (compare with the proof of
path-collapsible-is-hset above):

\begin{code}

local-hedberg : {X : Type} → (x : X)
      → ({y : X} → collapsible(x ≡ y))
      → (y : X) → hprop(x ≡ y)
local-hedberg {X} x pc y p q = claim₂
 where
  f : {y : X} → x ≡ y → x ≡ y
  f = π₀ pc
  g : {y : X} (p q : x ≡ y) → f p ≡ f q
  g = π₁ pc
  claim₀ : {y : X} (r : x ≡ y) → r ≡ (f refl)⁻¹ • (f r)
  claim₀ = J' x (λ r → r ≡ ((f refl)⁻¹) • (f r)) (sym-is-inverse(f refl))
  claim₁ : (f refl)⁻¹ • (f p) ≡ (f refl)⁻¹ • (f q)
  claim₁ = ap (λ h → (f refl)⁻¹ • h) (g p q)
  claim₂ : p ≡ q
  claim₂ = (claim₀ p) • claim₁ • (claim₀ q)⁻¹

path-collapsible-is-hset-as-a-special-case : {X : Type} → path-collapsible X → hset X
path-collapsible-is-hset-as-a-special-case {X} pc {x} {y} p q = local-hedberg x (λ {y} → (π₀(pc {x} {y})) , (π₁(pc {x} {y}))) y p q


\end{code}

So, for instance, if x is isolated in the sense that equality x ≡ y is
decidable for all y, then x ≡ y is an hprop for all y. And example is
the set ℕ∞ defined elsewhere, in which ∞ is not isolated but all
finite points are isolated. This example is not very good because ℕ∞
is an hset anyway (shown in another file).


A d d e n d u m  (30 March 2013)
--------------------------------

We have seen that the hstability of all types is a HoTT taboo. But
actually it is already a constructive taboo that implies the HoTT
taboo.

The main lemma says that if the type

    (a₀ ≡ x) + (a₁ ≡ x)

is hstable for every x : X, then the type a₀ ≡ a₁ is decidable. We
formulate this in a more convenient way:

\begin{code}

global-choice-lemma : (X : Type) → (a : ₂ → X) → ({x : X} → hstable(Σ \(i : ₂) → a i ≡ x)) → decidable(a ₀ ≡ a ₁)
global-choice-lemma X a choice  = equal-or-different
 where
  E : Type
  E = Σ \(x : X) → hinhabited(Σ \(i : ₂) → a i ≡ x)

  r : ₂ → E
  r i = a i , η(i , refl)

  r-Σ-≡s : (e : E) → Σ \(i : ₂) → r i ≡ e
  r-Σ-≡s (x , p) = π₀ p' , Σ-≡ (a(π₀ p')) x (η((π₀ p') , refl)) p (π₁ p') (hprop-hinhabited _ p)
   where
    p' : Σ \(i : ₂) → a i ≡ x
    p' = choice p

  s : E → ₂
  s e = π₀(r-Σ-≡s e)

  r-retract : (e : E) → r(s e) ≡ e
  r-retract e = π₁(r-Σ-≡s e)

  s-injective : (e e' : E) → s e ≡ s e' → e ≡ e'
  s-injective e e' p = (r-retract e)⁻¹ • ap r p • r-retract e'

  a-r : (i j : ₂) → a i ≡ a j → r i ≡ r j
  a-r i j p = Σ-≡ (a i) (a j) (η(i , refl)) (η(j , refl)) p (hprop-hinhabited _ (η(j , refl)))

  r-a : (i j : ₂) → r i ≡ r j → a i ≡ a j
  r-a i j q = ap π₀ q

  a-s : (i j : ₂) → a i ≡ a j → s(r i) ≡ s(r j)
  a-s i j p = ap s (a-r i j p)

  s-a : (i j : ₂) → s(r i) ≡ s(r j) → a i ≡ a j
  s-a i j p = r-a i j (s-injective (r i) (r j) p)

  equal-or-different : (a ₀ ≡ a ₁) + (a ₀ ≡ a ₁ → ∅)
  equal-or-different = claim(₂-discrete {s(r ₀)} {s(r ₁)})
   where
    claim : (s(r ₀) ≡ s(r ₁)) + (s(r ₀) ≡ s(r ₁) → ∅) → (a ₀ ≡ a ₁) + (a ₀ ≡ a ₁ → ∅)
    claim (in₀ p) = in₀ (s-a ₀ ₁ p)
    claim (in₁ u) = in₁ (λ p → u (a-s ₀ ₁ p))

global-choice-constructive-taboo : ({X : Type} → hinhabited X → X) → (X : Type) → discrete X
global-choice-constructive-taboo global-choice X {a₀} {a₁} = global-choice-lemma X a (λ {x} → global-choice)
 where
  a : ₂ → X
  a ₀ = a₀
  a ₁ = a₁

\end{code}

Remark: This uses only MLTT extended with hinhabited. But actually not
even this is needed, because if every type has a constant endomap
(another formulation of global choice) then hinhabited is definable. See
http://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/ConstantChoice/ConstantChoice.html

So "every type has a constant endomap" (global choice) implies the
discreteness of all types without any extension to intensional MLTT.

A d d e n d u m  (2 April 2013)
--------------------------------

Another way of seeing something already observed above.

\begin{code}

p→h : {X : Type} → populated₁ X → hinhabited(hinhabited X → X) → hinhabited X
p→h {X} po = hinhabited-elim (hinhabited X → X) (hinhabited X) hprop-hinhabited lemma
 where
  lemma : (hinhabited X → X) → hinhabited X
  lemma s = po (hinhabited X) hprop-hinhabited s η

h→p : {X : Type} → (hinhabited(hinhabited X → X) → hinhabited X) → populated₁ X
h→p {X} φ P h a b = b'(lemma(a ∘ b'))
 where
  b' : hinhabited X → P
  b' = hinhabited-elim X P h b
  lemma : (hinhabited X → X) → hinhabited X
  lemma = φ ∘ η

\end{code}

This gives another way of seeing directly why (X*->X)* gives populated X → hinhabited X:
Another possible small definition of populated is

   populated X = (X* → X)* → X*


A d d e n d u m  (3 April 2013)
--------------------------------

Our hypothesis is that (X*->X)* for every type X. We show that it is
equivalent to hpropositional choice:

  (P : Type)(Y : P → Type) → hprop P → ((p : P) → (Y p)*) → ((p : P) → Y p)*

\begin{code}

hprop-choice-gives-hypothesis :

     ((P : Type)(Y : P → Type) → hprop P → ((p : P) → hinhabited(Y p)) → hinhabited((p : P) → Y p))

  →  ((X : Type) → hinhabited(hinhabited X → X))

hprop-choice-gives-hypothesis hprop-AC X = hprop-AC (hinhabited X) (λ p → X) hprop-hinhabited id


Σ-hinhabited-shift : {X : Type} {Y : X → Type} → (Σ \(x : X) → hinhabited(Y x)) → hinhabited(Σ \(x : X) → Y x)
Σ-hinhabited-shift {X} {Y} (x , h) = lemma x h
 where
  lemma : ∀(x : X) → hinhabited(Y x) → hinhabited(Σ \(x : X) → Y x)
  lemma x = hinhabited-functor(λ y → (x , y))


hypothesis-gives-hprop-choice :

       ((X : Type) → hinhabited(hinhabited X → X))

     → (P : Type)(Y : P → Type) → hprop P → ((p : P) → hinhabited(Y p)) → hinhabited((p : P) → Y p)

hypothesis-gives-hprop-choice φ P Y h f = hinhabited-functor claim₅ claim₄
 where
  -- f : (p : P) → hinhabited (Y p)
  X : Type
  X = Σ \(p : P) → Y p
  φ' : hinhabited(hinhabited X → X)
  φ' = φ X
  claim₀ : (p : P) → Σ \(p' : P) → hinhabited(Y p')
  claim₀ p = (p , f p)
  claim₁ : P → hinhabited X
  claim₁ p = Σ-hinhabited-shift(claim₀ p)
  claim₂ : hinhabited((P → hinhabited X) × (hinhabited X → X))
  claim₂ = hinhabited-strength(claim₁ , φ')
  claim₃ : (P → hinhabited X) × (hinhabited X → X) → P → X
  claim₃ (g , h) = h ∘ g
  claim₄ : hinhabited(P → X)
  claim₄ = hinhabited-functor claim₃ claim₂
  claim₅ : (P → X) → (p : P) → Y p
  claim₅ ψ p = transport {P} {Y} e y
    where
     p' : P
     p' = π₀(ψ p)
     y : Y p'
     y = π₁ (ψ p)
     e : p' ≡ p
     e = h p' p

\end{code}

Combining this with the type-theoretic theorem of choice, we get a
more familiar looking (equivalent) version of choice (Spector):

\begin{code}

tt-TC : {X : Type}{Y : X → Type}{A : (x : X) → Y x → Type}
      → (∀(x : X) → Σ \(y : Y x) → A x y) → Σ \(f : (x : X) → Y x) → ∀(x : X) → A x (f x)
tt-TC f = (λ x → π₀(f x)) , (λ x → π₁(f x))


∃ : {X : Type}(Y : X → Type) → Type
∃ Y = hinhabited(Σ Y)


hypothesis-gives-hprop-choice' :

       ((X : Type) → hinhabited(hinhabited X → X))

     → (P : Type)(Y : P → Type) → (A : (p : P) → Y p → Type) → hprop P

          → (∀(p : P) → ∃ \(y : Y p) → A p y) → ∃ \(f : (p : P) → Y p) → ∀(p : P) → A p (f p)

hypothesis-gives-hprop-choice' φ P Y A h = hinhabited-functor tt-TC ∘ hshift
 where
  hshift : (∀(p : P) → hinhabited(Σ \(y : Y p) → A p y)) → hinhabited(∀(p : P) → Σ \(y : Y p) → A p y)
  hshift = hypothesis-gives-hprop-choice φ P (λ p → Σ \(y : Y p) → A p y) h


\end{code}

Part of the above doesn't use the fact that P is an hprop:

\begin{code}

hypothesis-gives-funny-choice :

       ((Z : Type) → hinhabited(hinhabited Z → Z))

     → (X : Type)(Y : X → Type) → ((x : X) → hinhabited(Y x)) → hinhabited(X → Σ \(x : X) → Y x)

hypothesis-gives-funny-choice φ X Y f = claim₄
 where
  -- f : (x : X) → hinhabited (Y x)
  Z : Type
  Z = Σ \(x : X) → Y x
  φ' : hinhabited(hinhabited Z → Z)
  φ' = φ Z
  claim₀ : (x : X) → Σ \(x' : X) → hinhabited(Y x')
  claim₀ x = (x , f x)
  claim₁ : X → hinhabited Z
  claim₁ x = Σ-hinhabited-shift(claim₀ x)
  claim₂ : hinhabited((X → hinhabited Z) × (hinhabited Z → Z))
  claim₂ = hinhabited-strength(claim₁ , φ')
  claim₃ : (X → hinhabited Z) × (hinhabited Z → Z) → X → Z
  claim₃ (g , h) = h ∘ g
  claim₄ : hinhabited(X → Z)
  claim₄ = hinhabited-functor claim₃ claim₂

\end{code}

Added 26 July after a useful discussion in the HoTT
mailing list:

Let's change terminology to match the HoTT list discussion (and the
TLCA'2013 paper):

\begin{code}

∥_∥ : Type → Type
∥ X ∥ = hinhabited X

∣_∣ : {X : Type} → X → ∥ X ∥
∣ x ∣ = η x

postulate hprop-hprop : {X : Type} → hprop(hprop X) -- Standard fact. A proof will be included.

\end{code}

We introduce a sub-module with the purpose of saying "let ... then ..."

\begin{code}

module HoTT-list-discussion
  (X : Type)
  (f : X → X)
  (s : ∥ constant f ∥)
 where

\end{code}

Recall that we defined above

   constant f = (x y : X) → f x ≡ f y

   fix f = Σ \x → x ≡ f x

\begin{code}

  lemma₀ : constant f → hprop(fix f)
  lemma₀ = Kraus-Lemma f

  lemma₁ : ∥ constant f ∥ → hprop(fix f)
  lemma₁ = hinhabited-elim (constant f) (hprop(fix f)) hprop-hprop lemma₀

  F : constant f → X → fix f
  F κ x = f x , κ x (f x)

  G : ∥ constant f ∥ → X → fix f
  G s x = hinhabited-elim (constant f) (fix f) (lemma₁ s) (λ κ → F κ x) s

\end{code}

So the inhabitation of ∥ constant f ∥ suffices to extract an element
of X as soon as we have ∥ X ∥:

\begin{code}

  choice : ∥ X ∥ → X
  choice t = π₀ (hinhabited-elim X (fix f) (lemma₁ s) (G s) t)

\end{code}

But we can say more:

\begin{code}

  g : X → X
  g x = π₀(G s x)

  g-fixes-f : (x : X) → g x ≡ f(g x)
  g-fixes-f x = π₁(G s x)

  g-constant : constant g
  g-constant x y = ap π₀ p
   where
    p : G s x ≡ G s y
    p = lemma₁ s _ _

  g-is-f-truncated : ∥ ((x : X) → g x ≡ f x) ∥
  g-is-f-truncated = hinhabited-functor conditional-agreement s
   where
    conditional-agreement : constant f → (x : X) → g x ≡ f x
    conditional-agreement κ x = g-fixes-f x • κ (g x) x

\end{code}
