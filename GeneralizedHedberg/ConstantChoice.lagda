5 Dec 2012. MHE.

If every type has a constant endomap, then every relation has a
functional sub-relation with the same domain. This is a form of the
axiom of choice that shouldn't hold in type theory.

\begin{code} 

module ConstantChoice where

open import mini-library

Type  = Set

hprop : Type → Type
hprop X = (x y : X) → x ≡ y

_[_] :  {X Y : Type} → (X → Y → Type) → X → Type
A [ x ] = Σ \y → A x y

sub-relation : {X Y : Type} → (X → Y → Type) → (X → Y → Type) → Type
sub-relation {X} {Y} A B = (x : X) (y : Y) → A x y → B x y

functional : {X Y : Type} → (X → Y → Type) → Type
functional {X} {Y} A = (x : X) → hprop(A [ x ])

same-domain : {X Y : Type} → (X → Y → Type) → (X → Y → Type) → Type
same-domain {X} {Y} A B = (x : X) →  A [ x ] ⇔ B [ x ]

chooses : {X Y : Type} → (X → Y → Type) → (X → Y → Type) → Type
chooses A B = sub-relation A B × functional A × same-domain A B

constant : {X Y : Type} → (f : X → Y) → Type
constant {X} {Y} f = (x y : X) → f x ≡ f y

collapsible : Type → Type
collapsible X = Σ \(f : X → X) → constant f

fix : {X : Type} → (f : X → X) → Type
fix f = Σ \x → x ≡ f x

postulate Kraus-Lemma : {X : Type} → (f : X → X) → constant f → hprop(fix f)

postulate all-collapsible : (X : Type) → collapsible X

collapser : (X : Type) → X → X
collapser X = π₀(all-collapsible X)

collapser-constant : (X : Type) → constant(collapser X)
collapser-constant X = π₁(all-collapsible X)

functionalization : {X Y : Type} → (X → Y → Type) → (X → Y → Type)
functionalization A x y = Σ \(a : A x y)  → (y , a) ≡ collapser (A [ x ]) (y , a)

functionalization-is-subrelation : {X Y : Type} → (A : X → Y → Type) → sub-relation (functionalization A) A
functionalization-is-subrelation A x y = π₀

functionalization' : {X Y : Type} (A : X → Y → Type) → X → Type
functionalization' A x = fix(collapser(A [ x ]))

F : (X Y : Type) (A : X → Y → Type) (x : X) → functionalization A [ x ] → functionalization' A x
F _ _ _ _ (y , (a , p)) = ((y , a) , p)

G : (X Y : Type) (A : X → Y → Type) (x : X) → functionalization' A x → functionalization A [ x ] 
G _ _ _ _ ((y , a) , p) = (y , (a , p))

H : {X Y : Type} (A : X → Y → Type) (x : X) → hprop(functionalization' A x)
H A x = Kraus-Lemma (collapser(A [ x ])) (collapser-constant(A [ x ]))

functionalization-is-functional : {X Y : Type} → (A : X → Y → Type) → functional (functionalization A)
functionalization-is-functional {X} {Y} A x u v = q
 where
  p : F X Y A x u ≡ F X Y A x v
  p = H A x (F X Y A x u) (F X Y A x v)

  q : u ≡ v
  q = ap (G X Y A x) p

functionalization-has-same-domain : {X Y : Type} → (A : X → Y → Type) → same-domain (functionalization A) A
functionalization-has-same-domain {X} {Y} A x = f , g
 where
  f : functionalization A [ x ] → A [ x ]
  f (y , (a , p)) = (y , a)

  g :  A [ x ] → functionalization A [ x ]
  g (y , a)  = y' , (a' , p)
   where
    y' : Y
    y' = π₀(collapser (A [ x ]) (y , a))

    a' : A x y'
    a' = π₁(collapser (A [ x ]) (y , a))

    p : (y' , a') ≡ collapser (A [ x ]) (y' , a')
    p = collapser-constant (A [ x ]) (y , a) ((y' , a'))

a-choice-theorem : {X Y : Type} → (A : X → Y → Type) → chooses (functionalization A) A
a-choice-theorem {X} {Y} A = functionalization-is-subrelation A , 
                             functionalization-is-functional A , 
                             functionalization-has-same-domain A

\end{code}

We (Altenkirch, Coquand, Kraus and myself) already knew what
follows. I am recording it here for the moment: under the above axiom
all-collapsible, hpropositional reflection is definable.

\begin{code} 

hinhabited : Type → Type
hinhabited X = fix(collapser X)

hprop-hinhabited : {X : Type} → hprop(hinhabited X)
hprop-hinhabited {X} = Kraus-Lemma (collapser X) (collapser-constant X)

η : {X : Type} → X → hinhabited X
η {X} x = (collapser X x , collapser-constant X x (collapser X x))

hinhabited-elim : {X P : Type} → hprop P → (X → P) → (hinhabited X → P)
hinhabited-elim _ f = f ∘ π₀

\end{code}

Notice that the fact that P is an hprop is not used.

Moreover, we have, under all-collapsible:

\begin{code} 

down : {X : Type} → hinhabited X → X
down = π₀

\end{code}
