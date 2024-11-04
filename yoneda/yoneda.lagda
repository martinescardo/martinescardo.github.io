Martin Escardo, 7 May 2015. This is a literate Agda file.

Updated 2015, 2016, 2017 with promises made in 12 May 2015, and a few
other minor things (Agda code and remarks), with precise dates given
at the update points.

Using Yoneda rather than J to present the identity type
-------------------------------------------------------

Abstract. We take Yoneda as primitive and then construct J (based path
induction) from Yoneda, so that its computation rule holds
*definitionally*. This is intended to (1) try to explain the identity
type to category theorists in familiar terms and (2) try to explain
why "defining functions on refl" is enough for defining them on all
paths to (pre HoTT/UF) type theorists. However, at the moment, this is
addressed to HoTT/UF practitioners.

Related work. Egbert Rijke formulated and proved the type-theoretical
Yoneda Lemma in his master thesis under Andrej Bauer:

http://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/
https://hottheory.files.wordpress.com/2012/08/hott2.pdf (Section 2.8).

This gives the construction J ↦ Yoneda. What we show here is the
opposite construction Yoneda ↦ J.

Remark. This is about HoTT/UF, but we don't use function
extensionality, univalence, or any postulate (and we disable K). We
work in MLTT with Π, Σ, Id, U.  No other type is needed in this
discussion.

Brief introduction
------------------

Here by the Yoneda Lemma (or rather the Yoneda Construction) we mean a
particular equivalence

   ((y : X) → x = y → A y) ≃ A x

for any X:U, x:X, A:X→U. We regard a function with the lhs type as a
natural transformation from Id x to A, and we write

   Nat (Id x) A ≃ A x.

Regarding the type X as an ω-groupoid, its identity type is its Hom,
and we write the above as

   Nat (Hom x) A ≃ A x,

in more familiar categorical notation.

We start from Yoneda, constructed by pattern matching on the identity
path. There are only two definitions by pattern matching for this (and
pattern matching on the identity path is not used anywhere else in
this file).

The use of pattern matching rather than J here is deliberate. The
path-induction construction J itself is defined by pattern matching in
Agda and in MLTT. Here we instead have Yoneda as primitive, defined by
pattern matching. We then construct J (based path induction) from
Yoneda, so that its computation rule holds *definitionally*.

We could of course have used J to derive Yoneda, but we deliberately
don't do that, to make the point that it is possible to present
identity types via Yoneda rather than path induction J, and then
derive J.

But both Yoneda and path induction say essentially the same thing,
although in significantly different ways, namely that to define
something on all paths, it is enough to say what it does to the
identity path.

We can view path induction as an alternative, type theoretic,
presentation of the categorical Yoneda Lemma. We don't advocate that
one is better than the other. In fact, both are rather elegant, in
different ways, and equally useful.

For category theorists that like "just" explanations: Martin-Lӧf's J
is just the Yoneda Lemma presented as an induction principle.

See also http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda-concise.html
         http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda2.html

Technical exposition
--------------------

The elements of the universe U are called (homotopy) types and we
regard them as ω-groupoids.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module yoneda where

open import NonStandardUniverseNotation

\end{code}

We let U, V, W range over universes.

The Hom of an ω-groupoid is inductively defined under the traditional
(homotopy) type-theoretic view, by specifying only the identity
paths. This is justified by Yoneda. We perform this justification
"synthetically".

\begin{code}

data Path {U : Universe} {X : U ̇} : X → X → U ̇ where
  idp : (x : X) → Path x x

\end{code}

The type x ≡ y is the hom type of paths from x to y, which is itself
another ω-groupoid for every x,y:X. Traditional synonyms are the
following:

\begin{code}

Id Hom _≡_ : ∀ {U} {X : U ̇} → X → X → U ̇
Id  = Path
Hom = Path
_≡_ = Path

refl : ∀ {U} {X : U ̇} {x : X} → Id x x
refl {U} {X} {x} = idp x

\end{code}

We use all these notations in the following development, except 'refl'
and 'Path' at this time.

A "presheaf" on an ω-groupoid X is a function X → V into a universe V.
It is automatically functorial in the synthetic approach (see the HoTT
book). But (perhaps surprisingly) this is not needed here.

Nat A B is the type of natural transformations of presheaves on the
ω-groupoid X.  The automatic naturality of an element of this type is
discussed in the HoTT book, but (again perhaps surprisingly) it is not
needed here.

\begin{code}

Nat : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
Nat A B = ∀ x → A x → B x

\end{code}

To avoid function extensionality, we work with the following notions of
pointwise equality:

\begin{code}

Π : ∀ {U V} {X : U ̇} → (X → V ̇) → U ⊔ V ̇
Π A = ∀ x → A x

_∼_ : ∀ {U V} {X : U ̇} {A : X → V ̇} → Π A → Π A → U ⊔ V ̇
f ∼ g = ∀ x → f x ≡ g x

_≈_ : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} → Nat (Hom x) A → Nat (Hom x) A → U ⊔ V ̇
η ≈ θ = ∀ y → η y ∼ θ y

\end{code}

The following is defined as in the classical (i.e. non-synthetic)
case, by applying the natural transformation to the identity:

\begin{code}

yoneda-elem : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇)
           → Nat (Hom x) A → A x
yoneda-elem {U} {V} {X} {x} A η = η x (idp x)

\end{code}

The first use of pattern matching on the identity path (out of two) is
to define the (based) recursion principle Id-rec of the identity type
former.

Then the inverse of yoneda-elem amounts to Id-rec:

\begin{code}

Id-rec : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇) → A x → (y : X) → x ≡ y → A y
Id-rec _ a _ (idp x) = a

yoneda-nat : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇) → A x → Nat (Hom x) A
yoneda-nat = Id-rec

\end{code}

And this is the second and last use of pattern matching on identity
paths in this file:

\begin{code}

yoneda-lemma : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η : Nat (Hom x) A)
            → yoneda-nat A (yoneda-elem A η) ≈ η
yoneda-lemma {U} {V} {X} {.x} {A} η x (idp .x) = idp (yoneda-elem A η)

\end{code}

We could use funext (twice) to get η ≡ yoneda-nat A (yoneda-elem A η).
But we deliberately work in plain MLTT, and in fact in a very spartan
subset of it as explained in the introduction.

The other way round is trivial (it holds definitionally), and is the
computation rule for the Yoneda Construction:

\begin{code}

yoneda-computation : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (a : A x)
                   → yoneda-elem A (yoneda-nat A a) ≡ a
yoneda-computation = idp

\end{code}

The following is the HoTT synonym of yoneda-nat, with the arguments
permuted:

\begin{code}

transport : ∀ {U V} {X : U ̇} (A : X → V ̇) {x y : X} → x ≡ y → A x → A y
transport {U} {V} {X} A {x} {y} p a = yoneda-nat {U} {V} {X} {x} A a y p

\end{code}

The essence of the Yoneda Lemma is then that every natural
transformation from Hom x to a presheaf A is a transport, or,
equivalently, that every such natural transformation is recursively
defined.

\begin{code}

transport-lemma : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η : Nat (Hom x) A) (y : X) (p : x ≡ y)
                → transport A p (η x (idp x)) ≡ η y p
transport-lemma = yoneda-lemma

Id-rec-lemma : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η : Nat (Hom x) A) (y : X) (p : x ≡ y)
             → Id-rec A (η x (idp x)) y p ≡ η y p
Id-rec-lemma = yoneda-lemma

\end{code}

There are a number of special cases of interest.

Path composition, inversion and application are defined from yoneda-nat
(that is, from based path recursion or transport):

\begin{code}

source : ∀ {U} {X : U ̇} {x y : X} → x ≡ y → X
source {U} {X} {x} p = x

target : ∀ {U} {X : U ̇} {x y : X} → x ≡ y → X
target {U} {X} {x} {y} p = y

_∙_ : ∀ {U} {X : U ̇} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = yoneda-nat (Id (source p)) p (target q) q

Id⁻¹  : ∀ {U} {X : U ̇} → X → X → U ̇
Id⁻¹ x y = Id y x

_⁻¹ : ∀ {U} {X : U ̇} {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = yoneda-nat (Id⁻¹ (source p)) (idp (source p)) (target p) p

ap : ∀ {U V} {X : U ̇} {A : V ̇} (f : X → A) {x y : X} → x ≡ y → f x ≡ f y
ap f {x} {y} = yoneda-nat (λ y → f x ≡ f y) (idp (f x)) y

\end{code}

We now introduce the usual Agda notation for chains of equalities:

\begin{code}

_≡⟨_⟩_ : ∀ {U} {X : U ̇} (x {y z} : X) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : ∀ {U} {X : U ̇} (x : X) → x ≡ x
_∎ = idp

\end{code}

The function yoneda-elem is left-cancellable in the following sense:

\begin{code}

yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η θ : Nat (Hom x) A)
              → yoneda-elem A η ≡ yoneda-elem A θ → η ≈ θ
yoneda-elem-lc {U} {V} {X} {x} {A} η θ q y p =
  η y p                              ≡⟨ (yoneda-lemma η y p)⁻¹ ⟩
  yoneda-nat A (yoneda-elem A η) y p ≡⟨ ap (λ e → yoneda-nat A e y p) q ⟩
  yoneda-nat A (yoneda-elem A θ) y p ≡⟨ yoneda-lemma θ y p ⟩
  θ y p ∎

\end{code}

As in the classical (i.e. non-synthetic) situation, we have that every
natural transformation η of representable presheaves is
pre-composition with a fixed morphism, that is, a path q in our case,
namely name the yoneda element of η:

\begin{code}

yoneda-nat' : ∀ {U} {X : U ̇} (x {y} : X) → Hom x y → Nat (Hom y) (Hom x)
yoneda-nat' x = yoneda-nat (Hom x)

yoneda-elem' : ∀ {U} {X : U ̇} (x {y} : X) → Nat (Hom y) (Hom x) → Hom x y
yoneda-elem' x = yoneda-elem (Hom x)

yoneda-lemma' : ∀ {U} {X : U ̇} (x {y} : X) (η : Nat (Hom y) (Hom x)) (z : X) (p : y ≡ z)
              → (yoneda-elem' x η) ∙ p ≡ η z p
yoneda-lemma' {U} {X} x {y} = yoneda-lemma {U} {U} {X} {y} {Hom x}

yoneda-lemma'' : ∀ {U} {X : U ̇} (x {y} : X) (η : Nat (Hom y) (Hom x)) (z : X) (p : y ≡ z)
              → yoneda-nat' x (yoneda-elem' x η) z p ≡ η z p
yoneda-lemma'' {U} {X} x {y} = yoneda-lemma {U} {U} {X} {y} {Hom x}

\end{code}

The above is a generalized version of the main lemma in Hedberg's
Theorem:

\begin{code}

hedberg-lemma : ∀ {U} {X : U ̇} (x : X) (η : Nat (Hom x) (Hom x)) (y : X) (p : x ≡ y)
              → (yoneda-elem' x η) ∙ p ≡ η y p
hedberg-lemma x η y p = yoneda-lemma' x η y p

\end{code}

The following is an alternative construction of the identity type,
using the identity type, where path composition becomes simply
composition of natural transformations, and hence is definitionally
associative with the identity path definitionally its (left and right)
neutral element.

\begin{code}

Id' : ∀ {U} {X : U ̇} → X → X → U ̇
Id' x y = Nat (Id y) (Id x)

idp' : ∀ {U} {X : U ̇} (x : X) → Id' x x
idp' x y p = p

_◦_ : ∀ {U V} {X : U ̇} {A B C : X → V ̇} → Nat B C → Nat A B → Nat A C
θ ◦ η = λ y p → θ y (η y p)

_∙'_  : ∀ {U} {X : U ̇} {x y z : X} → Id' x y → Id' y z → Id' x z
_∙'_ = _◦_

-- Cheating (because we chase equivalences):
_⁻¹' : ∀ {U} {X : U ̇} {x y : X} → Id' x y → Id' y x
_⁻¹' {U} {X} {x} {y} η z p = yoneda-nat (Id⁻¹ z) p y (yoneda-elem (Id x) η)

\end{code}

To prove (idp x) ∙ p = p, we apply Yoneda to the identity natural
transformation. Right neutrality holds definitionally.

\begin{code}

idp-left-neutral : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → idp x ∙ p ≡ p
idp-left-neutral {U} {X} {x} {y} {p} = yoneda-lemma (idp' x) y p

idp-right-neutral : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ≡ p ∙ (idp y)
idp-right-neutral = idp

\end{code}

Another crucial particular case is when the presheaf A is constant
with value B:U ̇. Then every natural tranformation η is constant with
value yoneda-elem η.

\begin{code}

yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : Nat (Hom x) (λ _ → B)) (y : X) (p : x ≡ y)
             → yoneda-elem (λ _ → B) η ≡ η y p
yoneda-const {X} {B} {x} η = yoneda-elem-lc (λ y p → yoneda-elem _ η) η (idp (yoneda-elem _ η))

\end{code}

We now derive (based) path-induction, called J, from the Yoneda
Construction. The idea is that J can be reduced to transport and
"sigletons are contractible" (or the type of paths from a given point
is contractible). We learned this reduction from Thierry Coquand.

(Added 8 May 2015: See also
http://www.carloangiuli.com/blog/j-is-singleton-contractibility-plus-transport-definitionally/)

To apply it in our situation, we need to prove that singletons are
contractible from Yoneda, but we have already done our homework in
yoneda-const.

\begin{code}

record Σ {U V : Universe} {X : U ̇} (A : X → V ̇) : U ⊔ V ̇ where
 constructor _,_
 field
  pr₁ : X
  pr₂ : A pr₁

open Σ public

_×_ : ∀ {U} → U ̇ → U ̇ → U ̇
X × Y = Σ \(x : X) → Y

paths-from : ∀ {U} {X : U ̇} → X → U ̇
paths-from x = Σ \y → x ≡ y

is-center-of-contraction : ∀ {U} (X : U ̇) → X → U ̇
is-center-of-contraction X c = (x : X) → c ≡ x

is-contr : ∀ {U} → U ̇ → U ̇
is-contr X = Σ \(c : X) → is-center-of-contraction X c

singletons-contractible : ∀ {U} {X : U ̇} {x : X}
                        → is-center-of-contraction (paths-from x) (x , idp x)
singletons-contractible {U} {X} {x} (y , p) = yoneda-const η y p
 where
  η : Nat (Hom x) (λ _ → paths-from x)
  η y p = (y , p)

J' : ∀ {U V} {X : U ̇} (x : X) (B' : paths-from x → V ̇) → B' (x , idp x) → ∀ w → B' w
J' x B' b w = yoneda-nat B' b w (singletons-contractible w)

\end{code}

Finally, based path induction then reduces to J' in the obvious way:

\begin{code}

uncurry : ∀ {U V} {X : U ̇} {x : X} → ((y : X) → x ≡ y → V ̇) → (paths-from x → V ̇)
uncurry B (y , p) = B y p

J : ∀ {U V} {X : U ̇} (x : X) (B : (y : X) → x ≡ y → V ̇)
  → B x (idp x) → (y : X) (p : x ≡ y) → B y p
J x B b y p = J' x (uncurry B) b (y , p)

\end{code}

The computation rule holds definitionally (and this amounts to
yoneda-computation, which doesn't need to be mentioned, as it itself
holds definitionally):

\begin{code}

J-computation : ∀ {U V} {X : U ̇} {x : X} {B : (y : X) → x ≡ y → V ̇} (b : B x (idp x))
              → J x B b x (idp x) ≡ b
J-computation = idp

\end{code}

J constructed in this way has the following normal form reported by Agda:

  λ {U} {V} {X} x B b y p →
    Id-rec b
    (Id-rec
     (Id-rec (idp (Id-rec (x , idp x) p))
      (yoneda-lemma (λ y p → x , idp x) y p))
     (Id-rec (idp (Id-rec (x , idp x) p))
      (yoneda-lemma (λ y p → y , p) y p)))

Some generalities now (15th Nov 2017). Everything that follows is
proved from the Yoneda machinery rather than J, for the sake of
illustration.

\begin{code}

⁻¹-involutive : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive {U} {X} {x} {y} = yoneda-elem-lc (λ x p → (p ⁻¹)⁻¹) (λ x p → p) (idp(idp x)) y

⁻¹-contravariant : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) {z : X} (q : y ≡ z)
                → q ⁻¹ ∙ p ⁻¹ ≡ (p ∙ q)⁻¹
⁻¹-contravariant {U} {X} {x} {y} p {z} = yoneda-elem-lc (λ z q → q ⁻¹ ∙ p ⁻¹)
                                                       (λ z q → (p ∙ q) ⁻¹)
                                                       idp-left-neutral
                                                       z

left-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ idp y
left-inverse {U} {X} {x} {y} = yoneda-elem-lc (λ x p → p ⁻¹ ∙ p) (λ x p → idp x) (idp(idp x)) y

right-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → idp x ≡ p ∙ p ⁻¹
right-inverse {U} {X} {x} {y} = yoneda-const (λ x p → p ∙ p ⁻¹) y

\end{code}

Associativity also follows from the Yoneda Lemma, again with the same
proof method. Notice that we prove that two functions (in a context)
are equal without using function extensionality:

\begin{code}

ext-assoc : ∀ {U} {X : U ̇} {z t : X} (r : z ≡ t)
          → (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ∙ r)
          ≡ (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → p ∙ (q ∙ r))
ext-assoc {U} {X} {z} {t} = yoneda-elem-lc {U} {U} {X} {z}
                             {λ - → (x y : X) (p : x ≡ y) (q : y ≡ z) → x ≡ - }
                             (λ z r x y p q → p ∙ q ∙ r)
                             (λ z r x y p q → p ∙ (q ∙ r))
                             (idp (λ x y p q → p ∙ q))
                             t
\end{code}

Then of course associativity of path composition follows:

\begin{code}

assoc : ∀ {U} {X : U ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc {U} {X} {x} {y} p q r = ap (λ f → f x y p q) (ext-assoc r)

cancel-left : ∀ {U} {X : U ̇} {x y z : X} {p : x ≡ y} {q r : y ≡ z}
            → p ∙ q ≡ p ∙ r → q ≡ r
cancel-left {U} {X} {x} {y} {z} {p} {q} {r} s =
       q              ≡⟨ idp-left-neutral ⁻¹ ⟩
       idp y ∙ q      ≡⟨ ap (λ t → t ∙ q) ((left-inverse p)⁻¹) ⟩
       (p ⁻¹ ∙ p) ∙ q ≡⟨ assoc (p ⁻¹) p q ⟩
       p ⁻¹ ∙ (p ∙ q) ≡⟨ ap (λ t → p ⁻¹ ∙ t) s ⟩
       p ⁻¹ ∙ (p ∙ r) ≡⟨ (assoc (p ⁻¹) p r)⁻¹ ⟩
       (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (λ t → t ∙ r) (left-inverse p) ⟩
       idp y ∙ r      ≡⟨ idp-left-neutral ⟩
       r ∎
\end{code}

Added 12 May 2015:

Contractibility also arises as follows with the Yoneda Lemma.
(see https://en.wikipedia.org/wiki/Representable_functor)

A representation of A:X→U ̇ is a given x:X together with a natural
equivalence

  Π(y:X), x=y → A y

(i.e. a y-indexed family of equivalences).

Then a universal element of A is nothing but a center of contraction
(x:X, a:A(x)) of the type Σ(x:X), A(x).

So A:X→U ̇ is representable iff Σ(x:X), A(x) is contractible.

   Example. An interesting instance of this is the case where X is U ̇,
   B:U ̇ and A(C)=(B≃C), in which we get that A is representable iff the
   type Σ(C:U ̇), B≃C is contractible.

   But saying that, for any given B:U ̇, the above "presheaf" A is
   representable is the same as saying that U ̇ is univalent.

   Hence U ̇ is univalent = (Π(B : U ̇), contractible(Σ(C:U ̇), B≃C)).

   We don't develop this example in this version of these Agda notes.

The Agda development of this has been added 5 Nov 2015 and 17 Nov 2017:

\begin{code}

from-Σ-Id : ∀ {U V} {X : U ̇} (A : X → V ̇) {σ τ : Σ A}
          → σ ≡ τ
          → Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ
from-Σ-Id {U} {V} {X} A {x , a} {τ} p = yoneda-nat B (idp x , idp a) τ p
 where
   B : (τ : Σ A) → U ⊔ V ̇
   B τ = Σ \(p : x ≡ pr₁ τ) → yoneda-nat A a (pr₁ τ) p ≡ pr₂ τ

to-Σ-Id : ∀ {U V} {X : U ̇} (A : X → V ̇) {σ τ : Σ A}
          → (Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ)
          → σ ≡ τ
to-Σ-Id {U} {X} A {x , a} {y , b} (p , q) = r
 where
  η : Nat (Hom x) (λ _ → Σ A)
  η y p = (y , yoneda-nat A a y p)
  yc : (x , a) ≡ (y , yoneda-nat A a y p)
  yc = yoneda-const η y p
  r : (x , a) ≡ (y , b)
  r = yoneda-nat (λ b → (x , a) ≡ (y , b)) yc b q

is-universal-element : ∀ {U V} {X : U ̇} (A : X → V ̇) → Σ A → U ⊔ V ̇
is-universal-element A (x , a) = ∀ y (b : A y) → Σ \(p : x ≡ y) → yoneda-nat A a y p ≡ b

ue-is-cc : ∀ {U V} {X : U ̇} {A : X → V ̇}
          (σ : Σ A) → is-universal-element A σ → is-center-of-contraction (Σ A) σ
ue-is-cc {U} {V} {X} {A} (x , a) u (y , b) = to-Σ-Id A ((u y) b)

cc-is-ue : ∀ {U V} {X : U ̇} (A : X → V ̇)
          (σ : Σ A) → is-center-of-contraction (Σ A) σ → is-universal-element A σ
cc-is-ue A (x , a) φ y b = from-Σ-Id A {x , a} {y , b} (φ(y , b))

\end{code}

The following says that if the pair (x,a) is a universal element, then
the natural transformation it induces (namely yoneda-nat {U} {X} {x} a)
has a section and a retraction (which can be taken to be the same
function), and hence is an equivalence. Here having a section or
retraction is data not property:

\begin{code}

id : ∀ {U} {X : U ̇} → X → X
id x = x

_∘_ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g(f x)

has-section : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
has-section r = Σ \s → r ∘ s ∼ id

has-retraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
has-retraction s = Σ \r → r ∘ s ∼ id

is-equiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-equiv f = has-section f × has-retraction f

_≃_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

ideq : ∀ {U} (X : U ̇) → X ≃ X
ideq X = id , ((id , idp) , (id , idp))

Eq : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
Eq = _≃_

universality-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → is-universal-element A (x , a) → (y : X) → has-section(yoneda-nat A a y)
universality-section {U} {V} {X} {A} x a u y = s y , φ y
 where
  s : Nat A (Hom x)
  s y b = pr₁ (u y b)
  φ : (y : X) (b : A y) → yoneda-nat A a y (s y b) ≡ b
  φ y b = pr₂ (u y b)

\end{code}

Actually, it suffices to just give the section, as shown next
(https://github.com/HoTT/book/issues/718#issuecomment-65378867):

\begin{code}

idemp-is-id : ∀ {U} {X : U ̇} {x : X} (η : Nat (Hom x) (Hom x)) (y : X) (p : x ≡ y)
           → η y (η y p) ≡ η y p → η y p ≡ p
idemp-is-id {U} {X} {x} η y p idemp = cancel-left (
        η x (idp x) ∙ η y p ≡⟨ hedberg-lemma x η y (η y p) ⟩
        η y (η y p)         ≡⟨ idemp ⟩
        η y p               ≡⟨ (hedberg-lemma x η y p)⁻¹ ⟩
        η x (idp x) ∙ p   ∎ )

natural-section-is-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇}
                           (x : X) (r : Nat (Hom x) A)
                        → ((y : X) → has-section(r y))
                        → ((y : X) → is-equiv(r y))
natural-section-is-equiv {U} {V} {X} {A} x r hass = λ y → (hass y , hasr y)
 where
  s : Nat A (Hom x)
  s y = pr₁ (hass y)
  rs : {y : X} (a : A y) → r y (s y a) ≡ a
  rs {y} = pr₂ (hass y)
  η : (y : X) → x ≡ y → x ≡ y
  η y p = s y (r y p)
  idemp : (y : X) (p : x ≡ y) → η y (η y p) ≡ η y p
  idemp y p = ap (s y) (rs (r y p))
  η-is-id : (y : X) (p : x ≡ y) → η y p ≡ p
  η-is-id y p = idemp-is-id η y p (idemp y p)
  hasr : (y : X) → has-retraction(r y)
  hasr y = s y , η-is-id y

\end{code}

We are interested in this corollary:

\begin{code}

universality-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → is-universal-element A (x , a)
                   → (y : X) → is-equiv(yoneda-nat A a y)
universality-equiv {U} {V} {X} {A} x a u = natural-section-is-equiv x (yoneda-nat A a)
                                                                      (universality-section x a u)
\end{code}

The converse is trivial:

\begin{code}

section-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → ((y : X) → has-section(yoneda-nat A a y))
                     → is-universal-element A (x , a)
section-universality x a φ y b = pr₁(φ y) b , pr₂(φ y) b

equiv-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → ((y : X) → is-equiv(yoneda-nat A a y))
                   → is-universal-element A (x , a)
equiv-universality x a φ = section-universality x a (λ y → pr₁ (φ y))

\end{code}

Next we show that a presheaf A is representable iff Σ A is contractible.

\begin{code}

_≊_ : ∀ {U V} {X : U ̇} → (X → V ̇) → (X → V ̇) → U ⊔ V ̇
A ≊ B = Σ \(η : Nat A B) → ∀ x → is-equiv(η x)

is-representable : ∀ {U} {X : U ̇} → (X → U ̇) → U ̇
is-representable A = Σ \x → Id x ≊ A

contr-is-repr : ∀ {U} {X : U ̇} {A : X → U ̇} → is-contr (Σ A) → is-representable A
contr-is-repr {U} {X} {A} ((x , a) , cc) = g
 where
  g : Σ \(x : X) → Id x ≊ A
  g = x , (yoneda-nat A a , universality-equiv x a (cc-is-ue A (x , a) cc))

equiv-closed-under-∼ : ∀ {U} {X Y : U ̇} (f g : X → Y) → is-equiv f →  g ∼ f  → is-equiv g
equiv-closed-under-∼ {U} {X} {Y} f g ((s , fs) , (r , rf)) peq = ((s , gs) , (r , rg))
 where
  gs : (y : Y) → g(s y) ≡ y
  gs y = g (s y) ≡⟨ peq (s y) ⟩ f (s y) ≡⟨ fs y ⟩ y ∎
  rg : (x : X) → r(g x) ≡ x
  rg x = r (g x) ≡⟨ ap r (peq x) ⟩ r (f x) ≡⟨ rf x ⟩ x ∎

is-repr→is-equiv-yoneda : ∀ {U} {X : U ̇} {A : X → U ̇} (x : X) (η : Nat (Id x) A) (y : X)
                        → is-equiv (η y) → is-equiv (yoneda-nat A (yoneda-elem A η) y)
is-repr→is-equiv-yoneda {U} {X} {A} x η y ise =
  equiv-closed-under-∼ (η y) (yoneda-nat A (yoneda-elem A η) y) ise (yoneda-lemma η y)

repr-is-contr : ∀ {U} {X : U ̇} {A : X → U ̇} → is-representable A → is-contr (Σ A)
repr-is-contr {U} {X} {A} (x , (η , φ)) = g
 where
  σ : Σ A
  σ = x , yoneda-elem A η
  is-ue-σ : is-universal-element A σ
  is-ue-σ = equiv-universality x (yoneda-elem A η) (λ y → is-repr→is-equiv-yoneda x η y (φ y))
  g : Σ \(σ : Σ A) → is-center-of-contraction (Σ A) σ
  g = σ , ue-is-cc σ is-ue-σ

\end{code}

Here are some further consequences:

\begin{code}

paths-from-contractible : ∀ {U} {X : U ̇} (x : X) → is-contr(paths-from x)
paths-from-contractible x = ((x , idp x) , singletons-contractible)

paths-to : ∀ {U} {X : U ̇} → X → U ̇
paths-to x = Σ \y → y ≡ x

rc-is-c : ∀ {U} {X Y : U ̇} (r : X → Y) → has-section r → is-contr X → is-contr Y
rc-is-c {U} {X} {Y} r (s , rs) (x , i) = r x , λ y → r x ≡⟨ ap r (i (s y)) ⟩ r (s y) ≡⟨ rs y ⟩ y ∎

pt-pf-equiv : ∀ {U} {X : U ̇} (x : X) → Σ \(f : paths-from x → paths-to x) → is-equiv f
pt-pf-equiv {U} {X} x = f , ((g , fg) , (g , gf))
 where
  f : paths-from x → paths-to x
  f (y , p) = y , (p ⁻¹)
  g : paths-to x → paths-from x
  g (y , p) = y , (p ⁻¹)
  fg : f ∘ g ∼ id
  fg (y , p) = ap (λ p → y , p) (⁻¹-involutive p)
  gf : g ∘ f ∼ id
  gf (y , p) = ap (λ p → y , p) (⁻¹-involutive p)

paths-to-contractible : ∀ {U} {X : U ̇} (x : X) → is-contr(paths-to x)
paths-to-contractible x = rc-is-c (pr₁(pt-pf-equiv x))
                                  (pr₁(pr₂((pt-pf-equiv x))))
                                  (paths-from-contractible x)

is-prop : ∀ {U} → U ̇ → U ̇
is-prop X = (x y : X) → x ≡ y

pcubp : ∀ {U} (X Y : U ̇) → is-prop X → is-prop Y → is-prop(X × Y)
pcubp X Y i j (x , y) (x' , y') = to-Σ-Id (λ _ → Y)
                                          (i x x' , j (yoneda-nat (λ _ → Y) y x' (i x x')) y')

c-is-p : ∀ {U} {X : U ̇} → is-contr X → is-prop X
c-is-p {U} {X} (c , φ) x y = x ≡⟨ (φ x) ⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎

ic-is-p : ∀ {U} {X : U ̇} → (X → is-contr X) → is-prop X
ic-is-p {U} {X} φ x = c-is-p (φ x) x

is-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-embedding f = ∀ y → is-prop(Σ \x → y ≡ f x)

is-embedding' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-embedding' f = ∀ x x' → is-equiv (ap f {x} {x'})

embedding-embedding' : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding f → is-embedding' f
embedding-embedding' {U} {V} {X} f ise = g
 where
  c : (x : X) → is-contr(Σ \(x' : X) → f x ≡ f x')
  c x = (x , idp (f x)) , ise (f x) (x , idp (f x))
  g : (x x' : X) → is-equiv(ap f {x} {x'})
  g x = universality-equiv x (idp (f x)) (cc-is-ue (λ x' → f x ≡ f x') (pr₁ (c x)) (pr₂ (c x)))

embedding'-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding' f → is-embedding f
embedding'-embedding {U} {V} {X} {Y} f ise = g
 where
  e : (x x' : X) → is-center-of-contraction (Σ \(x' : X) → f x ≡ f x') (x , idp (f x))
  e x x' = ue-is-cc (x , idp (f x)) (equiv-universality x (idp (f x)) (ise x))
  h : (x : X) → is-prop (Σ \(x' : X) → f x ≡ f x')
  h x σ τ = σ ≡⟨ (e x (pr₁ σ) σ)⁻¹ ⟩ (x , idp (f x)) ≡⟨ e x (pr₁ τ) τ ⟩ τ ∎
  g : (y : Y) → is-prop (Σ \(x' : X) → y ≡ f x')
  g y (x , p) = transport (λ y → is-prop (Σ \(x' : X) → y ≡ f x')) (p ⁻¹) (h x) (x , p)

\end{code}

9th Jun 2016:

Then it also follows that Id : X → (X → U ̇) is an embedding (the
Yoneda-embedding). In fact, the Id-fiber of A:X→U ̇ says that
A is representable, which is equivalent to the contractibility of ΣA,
which is a proposition. (Hence the injective types are the retracts of
the exponential powers of the universe.)

This works as follows in outline:

If A : X → U ̇ then the Id-fiber of A is Σ \(x : X) → Id x ≡ A.

If (x : X , p : Id x = A) is in the fiber, then

   ap Σ p : Σ (Id x) = Σ A,

and hence, being equal to a contractible type, Σ A is
contractible.

Next we have (*)

 A x ≃ Nat (Id x) A             (yoneda)
     = (y : Y) → Id x y → A y   (definition)
     ≃ (y : Y) → Id x y ≃ A y   (because Σ A is contractible (Yoneda corollary))
     ≃ (y : Y) → Id x y ≡ A y   (by univalence)
     ≃ Id x ≡ A                 (by function extensionality)

Hence the type Σ \(x : X) → Id x ≡ A y is contractible, because Σ A is
contractible, which shows that Id : X → (X → U) is an embedding.

2017:

This relies on univalence. But less than that suffices
(https://groups.google.com/forum/#!topic/homotopytypetheory/bKti7krHM-c)

First, Evan Cavallo showed that it is enough to assume funext and that
the canonical map X ≡ Y → X ≃ Y is an embedding. Then, using this idea
and the above proof outline, we further generalized this to assume
that the canonical map X ≡ Y → (X → Y) is left-cancellable (which is
much weaker than assuming that it is an embedding).

This is what we record next (9th December 2017), using the original
idea (*) in the weakened form discussed above.

We have already defined is-embedding, and the next definition is
equivalent, although we don't need to pause to show this.

\begin{code}

is-Embedding : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-Embedding f = ∀ y → is-prop(Σ \x → f x ≡ y)

left-cancellable : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable f = ∀ x x' → f x ≡ f x' → x ≡ x'

lcccomp : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z)
        → left-cancellable f → left-cancellable g → left-cancellable (g ∘ f)
lcccomp f g lcf lcg x x' = lcf x x' ∘ lcg (f x) (f x')

\end{code}

If the codomain of a left-cancellable function is a proposition, so is
its domain.

\begin{code}

lcmtpip : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → left-cancellable f → is-prop Y → is-prop X
lcmtpip f lc i x x' = lc x x' (i (f x) (f x'))

\end{code}

We next consider sums and products of families of left-cancellable
maps, which again give left-cancellable maps.

\begin{code}

NatΣ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΣ-lc : ∀ {U V W} (X : U ̇) (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
        → ((x : X) → left-cancellable(ζ x)) → left-cancellable(NatΣ ζ)
NatΣ-lc X A B ζ ζ-lc (x , a) (y , b) pq = g
  where
    p : x ≡ y
    p = pr₁ (from-Σ-Id B pq)
    η : Nat (Hom x) B
    η = yoneda-nat B (ζ x a)
    q : η y p ≡ ζ y b
    q = pr₂ (from-Σ-Id B pq)
    θ : Nat (Hom x) A
    θ = yoneda-nat A a
    η' : Nat (Hom x) B
    η' y p = ζ y (θ y p)
    r : η' ≈ η
    r = yoneda-elem-lc η' η (idp (ζ x a))
    r' : ζ y (θ y p) ≡ η y p
    r' = r y p
    s : ζ y (θ y p) ≡ ζ y b
    s = r' ∙ q
    t : θ y p ≡ b
    t = ζ-lc y (θ y p) b s
    g : x , a ≡ y , b
    g = to-Σ-Id A (p , t)

NatΠ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

happly : ∀ {U V} {X : U ̇} {A : X → V ̇} (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ h → h x) p

NatΠ-lc : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : Nat A B)
    → ((x : X) → left-cancellable(f x))
    → (g g' : Π A) → NatΠ f g ≡ NatΠ f g' → g ∼ g'
NatΠ-lc f flc g g' p x = flc x (g x) (g' x) (q x)
 where
   q : ∀ x → f x (g x) ≡ f x (g' x)
   q = happly (NatΠ f g) (NatΠ f g') p

\end{code}

Any section is left-cancellable, of course:

\begin{code}

section-lc : ∀ {U V} {X : U ̇} {A : V ̇} (s : X → A) → has-retraction s → left-cancellable s
section-lc {U} {V} {X} {Y} s (r , rs) x y p = (rs x)⁻¹ ∙ ap r p ∙ rs y

\end{code}

The function-extensionality principle in its univalent mathematics manifestation:

\begin{code}

FunExt : ∀ U V → U ′ ⊔ V ′ ̇
FunExt U V = {X : U ̇} {A : X → V ̇} (f g : Π A) → is-equiv (happly f g)

≃-funext : ∀ U V → FunExt U V → {X : U ̇} {A : X → V ̇} (f g : Π A)
         → (f ≡ g) ≃ ((x : X) → f x ≡ g x)
≃-funext U V fe f g = happly f g , fe f g

funext : ∀ {U V} (fe : FunExt U V) {X : U ̇} {A : X → V ̇} (f g : Π A)
      → ((x : X) → f x ≡ g x) → f ≡ g
funext fe f g = pr₁(pr₁(fe f g))

happly-funext : ∀ {U V} {X : U ̇} {A : X → V ̇}
                (fe : FunExt U V) (f g : Π A) (h : f ∼ g)
              → happly f g (funext fe f g h) ≡ h
happly-funext fe f g = pr₂(pr₁(fe f g))

happly-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : FunExt U V) (f g : Π A)
         → left-cancellable(happly f g)
happly-lc fe f g = section-lc (happly f g) ((pr₂ (fe f g)))

eqtofun : ∀ {U V} (X : U ̇) → Nat (Eq X) (λ (Y : V ̇) → X → Y)
eqtofun X Y (f , _) = f

idtoeq : ∀ {U} (X : U ̇) → Nat (Id X) (Eq X)
idtoeq X = yoneda-nat (Eq X) (ideq X)

idtofun : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
idtofun X Y p = eqtofun X Y (idtoeq X Y p)

idtofun' : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
idtofun' X = yoneda-nat (λ Y → X → Y) id

idtofun-agree : ∀ {U} (X : U ̇) → idtofun X ≈ idtofun' X
idtofun-agree X = yoneda-elem-lc (idtofun X) (idtofun' X) (idp id)

idtofun-is-equiv : ∀ {U} (X Y : U ̇) (p : X ≡ Y) → is-equiv(idtofun X Y p)
idtofun-is-equiv X Y p = pr₂(idtoeq X Y p)

\end{code}

Id : X → (X → U) is left-cancellable:

\begin{code}

Id-lc : ∀ {U} {X : U ̇} → left-cancellable (Id {U} {X})
Id-lc {U} {X} x y p = idtofun (Id y y) (Id x y) (happly (Id y) (Id x) (p ⁻¹) y) (idp y)

\end{code}

The Id Embedding Lemma. The idea is to show that the type
T := Σ \(x : X) → Id x ≡ A is a proposition by showing that there is a
left-cancellable map from it to a proposition, namely the contractible
type Σ A.

\begin{code}

Id-Embedding-Lemma : ∀ {U} → FunExt U U → FunExt U (U ′) → {X : U ̇}
                  → ((x y : X) (A : X → U ̇) → left-cancellable (idtofun (Id x y) (A y)))
                  → is-Embedding(Id {U} {X})
Id-Embedding-Lemma {U} fe fe' {X} iflc A (x₀ , p₀) = h (x₀ , p₀)
 where
  T = Σ \(x : X) → Id x ≡ A
  q : Σ (Id x₀) ≡ Σ A
  q = ap Σ p₀
  c : is-contr(Σ A)
  c = yoneda-nat is-contr (paths-from-contractible x₀) (Σ A) q
  f₀ : (x : X) → Id x ≡ A → (y : X) → Id x y ≡ A y
  f₀ x = happly (Id x) A
  f₁ : (x : X) → ((y : X) → Id x y ≡ A y) → (y : X) → Id x y → A y
  f₁ x = NatΠ (λ y → idtofun (Id x y) (A y))
  f₂ : (x : X) → Nat (Id x) A → A x
  f₂ x = yoneda-elem A
  f : (x : X) → Id x ≡ A → A x
  f x = f₂ x ∘ f₁ x ∘ f₀ x
  f₀-lc : (x : X) → left-cancellable(f₀ x)
  f₀-lc x = happly-lc fe' (Id x) A
  f₁-lc : (x : X) → left-cancellable(f₁ x)
  f₁-lc x = g
    where
      l : ∀ φ φ' → f₁ x φ ≡ f₁ x φ' → (x : X) → φ x ≡ φ' x
      l = NatΠ-lc (λ y → idtofun (Id x y) (A y)) (λ y → iflc x y A)
      g : ∀ φ φ' → f₁ x φ ≡ f₁ x φ' → φ ≡ φ'
      g φ φ' p = funext fe' φ φ' (l φ φ' p)
  f₂-lc : (x : X) → left-cancellable(f₂ x)
  f₂-lc x η η' p = funext fe η η' (λ y → funext fe (η y) (η' y) (l y))
    where
      l : η ≈ η'
      l = yoneda-elem-lc η η' p
  f-lc : (x : X) → left-cancellable(f x)
  f-lc x = lcccomp (f₀ x) (f₂ x ∘ f₁ x) (f₀-lc x) (lcccomp (f₁ x) (f₂ x) (f₁-lc x) (f₂-lc x))
  g : T → Σ A
  g = NatΣ f
  g-lc : left-cancellable g
  g-lc = NatΣ-lc X (λ x → Id x ≡ A) A f f-lc
  h : is-prop T
  h = lcmtpip g g-lc (c-is-p c)

\end{code}

The definition of a univalent universe and basic consequences:

\begin{code}

is-univalent : ∀ U → U ′ ̇
is-univalent U = (X Y : U ̇) → is-equiv(idtoeq X Y)

eqtoid : ∀ {U} → is-univalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y
eqtoid ua X Y = pr₁(pr₁(ua X Y))

idtoeq-eqtoid : ∀ {U} (ua : is-univalent U)
              → (X Y : U ̇) (e : X ≃ Y) → idtoeq X Y (eqtoid ua X Y e) ≡ e
idtoeq-eqtoid ua X Y = pr₂(pr₁(ua X Y))

is-univalent-≃ : ∀ {U} → is-univalent U → (X Y : U ̇) → (X ≡ Y) ≃ (X ≃ Y)
is-univalent-≃ ua X Y = idtoeq X Y , ua X Y

is-univalent-idtoeq-lc : ∀ {U} → is-univalent U → (X Y : U ̇) → left-cancellable(idtoeq X Y)
is-univalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (pr₂ (ua X Y))

\end{code}

The funext map is left-cancellable:

\begin{code}

funext-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : FunExt U V)
         → (f g : Π A) → left-cancellable(funext fe f g)
funext-lc fe f g = section-lc (funext fe f g) (happly f g , happly-funext fe f g)

\end{code}

The fact that idtofun is an equivalence is a proposition, assuming
function extensionality:

\begin{code}

jip' : ∀ {U} (fe : FunExt U U) (X Y : U ̇) (p : X ≡ Y) → is-prop(is-equiv(idtofun X Y p))
jip' {U} fe X = J X B go -- Only use of J in this file (can we get rid of it?)
 where
   B : (Y : U ̇) → X ≡ Y → U ̇
   B Y p = is-prop(is-equiv(idtofun X Y p))
   A = Σ \(f : X → X) → f ≡ id
   a : is-prop A
   a = c-is-p (paths-to-contractible id)
   A' = Σ \(f : X → X) → f ∼ id
   η : (f : X → X) → f ∼ id → f ≡ id
   η f = funext fe f id
   η-lc : (f : X → X) → left-cancellable(η f)
   η-lc f = funext-lc fe f id
   h : A' → A
   h = NatΣ η
   h-lc : left-cancellable h
   h-lc = NatΣ-lc (X → X) (λ f → f ∼ id) (λ f → f ≡ id) η η-lc
   b : is-prop A'
   b = lcmtpip h h-lc a
   go : is-prop(A' × A')
   go = pcubp A' A' b b

\end{code}

Equivalences are propositions, assuming univalence (and function
extensionality) (but also without the univalence assumption, although
we don't bother):

\begin{code}

jip : ∀ {U} → is-univalent U → FunExt U U → {X Y : U ̇}
   → (f : X → Y) → is-prop(is-equiv f)
jip {U} ua fe {X} {Y} f ije = h ije
  where
    e : X ≃ Y
    e = (f , ije)
    p : X ≡ Y
    p = eqtoid ua X Y e
    f' : X → Y
    f' = idtofun X Y p
    h' : is-prop(is-equiv f')
    h' = jip' fe X Y p
    ije' : is-equiv f'
    ije' = idtofun-is-equiv X Y p
    e' : X ≃ Y
    e' = f' , ije'
    q : e' ≡ e
    q = idtoeq-eqtoid ua X Y e
    q₁ : f' ≡ f
    q₁ = ap pr₁ q
    h : is-prop(is-equiv f)
    h = yoneda-nat (λ f → is-prop(is-equiv f)) h' f q₁

\end{code}

The map eqtofun is left-cancellable assuming univalence (and function
extensionality, which is a consequence of univalence, but we don't
bother):

\begin{code}

eqtofun-lc : ∀ {U} → is-univalent U → FunExt U U
           → (X Y : U ̇) → left-cancellable(eqtofun X Y)
eqtofun-lc ua fe X Y (f , jef) (g , jeg) p = go
 where
  q : yoneda-nat is-equiv jef g p ≡ jeg
  q = jip ua fe g (yoneda-nat is-equiv jef g p) jeg
  go : f , jef ≡ g , jeg
  go = to-Σ-Id is-equiv (p , q)

\end{code}

The map idtofun is left-cancellable assuming univalence (and funext):

\begin{code}

is-univalent-idtofun-lc : ∀ {U} → is-univalent U → FunExt U U → (X Y : U ̇)
                       → left-cancellable(idtofun X Y)
is-univalent-idtofun-lc  ua fe X Y =
   lcccomp (idtoeq X Y) (eqtofun X Y) (is-univalent-idtoeq-lc ua X Y) (eqtofun-lc ua fe X Y)

\end{code}

Univalence implies that the function Id_X : X → (X → U) is an embedding.

\begin{code}

UA-Id-embedding-Theorem : ∀ {U} → is-univalent U → FunExt U U → FunExt U (U ′)
                       → {X : U ̇} → is-Embedding(Id {U} {X})
UA-Id-embedding-Theorem {U} ua fe fe' {X} = Id-Embedding-Lemma fe fe'
                                            (λ x y a → is-univalent-idtofun-lc ua fe (Id x y) (a y))

\end{code}

Streicher's K-axiom:

\begin{code}

is-set : ∀ {U} → U ̇ → U ̇
is-set X = {x y : X} → x ≡ y

K : ∀ U → U ′ ̇
K U = (X : U ̇) → is-set X

\end{code}

Implies that istofun is left-cancellable:

\begin{code}

K-idtofun-lc : ∀ {U} → K (U ′)
            → {X : U ̇} (x y : X) (A : X → U ̇) → left-cancellable(idtofun (Id x y) (A y))
K-idtofun-lc {U} k {X} x y A p q r = k (Id (Id x y) (A y))

\end{code}

The K axiom and function extensionality together imply that the
function Id : X → (X → U) is an embedding.

\begin{code}

K-id-embedding-Theorem' : ∀ {U} → K (U ′) → FunExt U U → FunExt U (U ′)
                       → {X : U ̇} → is-Embedding(Id {U} {X})
K-id-embedding-Theorem' {U} k fe fe' {X} = Id-Embedding-Lemma fe fe' (K-idtofun-lc k)

\end{code}

But actually function extensionality is not needed for this: K alone suffices.

\begin{code}

K-lc-e : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y) → left-cancellable f → K V → is-Embedding f
K-lc-e {U} {V} {X} {Y} f f-lc k y (x , p) (x' , p') = to-Σ-Id (λ x → f x ≡ y) (r , q)
 where
   r : x ≡ x'
   r = f-lc x x' (p ∙ (p' ⁻¹))
   q : yoneda-nat (λ x → f x ≡ y) p x' r ≡ p'
   q = k (Id (f x') y)

K-id-embedding-Theorem : ∀ {U} → K (U ′) → {X : U ̇} → is-Embedding(Id {U} {X})
K-id-embedding-Theorem {U} k {X} = K-lc-e Id Id-lc k

\end{code}











Here are the needed precedences for the above code to parse correctly:

\begin{code}

infixl 4  _,_
infixl 5  _∘_
infix  4  _∼_
infix  1  _≡_
infix  3  _⁻¹
infixl 2  _∙_
infix  1  _∎
infixr 0  _≡⟨_⟩_

\end{code}
