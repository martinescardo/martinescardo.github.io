-- File by Andrea Vezzosi (https://github.com/Saizan/cubical-demo)

{-# OPTIONS --cubical #-}
module PathPrelude where

open import Primitives public
open import Primitives public using () renaming (Sub to _[_↦_])

module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  trans' : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans' {y = y} p q i = primComp (λ _ → A) _
                                 (λ { j (i = i0) → p (~ j)
                                    ; j (i = i1) → q j })
                                 y

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = primComp (λ _ → A) _ (λ { j (i = i0) → x
                                                ; j (i = i1) → q j }) (p i)

  cong : ∀ {ℓ'} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f p = λ i → f (p i)

  infix  3 _≡-qed
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 ≡-proof_

  ≡-proof_ : {x y : A} → x ≡ y → x ≡ y
  ≡-proof x≡y = x≡y

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡-qed : (x : A) → x ≡ x
  _ ≡-qed  = refl

fill : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  ((i : I) → Partial (A i) φ) → A i0 → (i : I) → A i
fill A φ u azero i = unsafeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
  (λ j → unsafePOr φ (~ i) (u (i ∧ j)) λ { (i = i0) → azero }) azero

transp : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → A i0 → A i1
transp A x = primComp A i0 (λ _ → empty) x

transp⁻¹ : {ℓ : I → _} → (A : (i : I) → Set (ℓ i)) → A i1 → A i0
transp⁻¹ A = transp (λ i → A (~ i))

toPathP : ∀{ℓ}{A : I → Set ℓ}{x : A i0}{y : A i1} → transp A x ≡ y → PathP A x y
toPathP {ℓ} {A} {x} {y} p i = primComp (λ _ → A i) φ u (xPathP i)
  where φ = ~ i ∨ i
        u : I → PartialP φ (λ z → A i)
        u _ (i = i0) = x
        u j (i = i1) = p j
        xPathP : PathP A x (transp A x )
        xPathP j = fill A _ (λ _ → empty) x j

transp-refl : ∀{ℓb} → {B : Set ℓb} → (x : B) → primComp (λ j → B) i0 (λ j → empty) x ≡ x
transp-refl {B = B} x i = primComp (λ _ → B) i ((λ { j (i = i1) → x })) x

transp-pi : ∀{ℓb} → {B : Set ℓb} → {ℓa : I → _} → (A : (i : I) → Set (ℓa i)) → (f : (B → A i0)) → (λ x → transp A (f x)) ≡ transp (λ i → (B → A i)) f
transp-pi {B = B} A f i x = (primComp A i0 (λ i → empty)) (f (transp-refl x (~ i)))

module _ {ℓa ℓb} {A : Set ℓa} {B : A → Set ℓb} where
  funUnImp : ({x : A} → B x) → (x : A) → B x
  funUnImp f x = f {x}

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p = λ i x → p x i

  funExtImp : {f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) →
                                       {x : A} → f {x} ≡ g {x}
  funExtImp p {x} = λ i → p x i

{-
module _ {ℓ} {A : Set ℓ} where
  singl : (a : A) → Set ℓ
  singl a = Σ[ x ∈ A ] (a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → _≡_ {A = singl a} (a , refl) (b , p)
  contrSingl p = λ i → ((p i) , λ j → p (i ∧ j))


module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x ((λ i → x))) where

  pathJ : (y : A) → (p : x ≡ y) → P y p
  pathJ _ p = transp (λ i → uncurry P (contrSingl p i)) d

  pathJprop : pathJ _ refl ≡ d
  pathJprop i = primComp (λ _ → P x refl) i (λ {j (i = i1) → d}) d


module _ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} where
  subst : {a b : A} (p : Path a b) → P a → P b
  subst {a} {b} p pzero = pathJ {ℓ} {ℓ'} (λ (y : A) → λ _ → P y) pzero b p

  substInv : {a x : A} (p : Path a x) → P x → P a
  substInv p  =  subst (λ i → p (~ i))

injective : ∀ {ℓa ℓb} → {A : Set ℓa} → {B : Set ℓb} → (f : A → B) → Set (ℓ-max ℓa ℓb)
injective {_} {_} {A} f = {azero a1 : A} → f azero ≡ f a1 → azero ≡ a1

module _ {ℓ} {Azero A1 : Set ℓ} (A : Azero ≡ A1) {φ : I} (azero : A i0)
         (p : Partial (Σ A1 λ y → PathP (λ i → A i) azero y) φ) where
  -- primComp using only Path
  compP : A i1
  compP = primComp (λ i → A i) φ (λ i o → p o .snd i) azero

  -- fill using only Path
  fillP : ∀ j → A j
  fillP j = primComp (λ i → A (i ∧ j)) (φ ∨ ~ j)
    (λ { i (φ = i1) → p itIsOne .snd (i ∧ j); i (j = i0) → azero }) azero

transpP : ∀ {ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'} {x y : A} → x ≡ y → B x → B y
transpP {B = B} p = pathJ (λ y _ → B _ → B y) (λ x → x) _ p

transpP≡subst : ∀ {ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'} {x y : A} → (p : x ≡ y) → transpP {B = B} p ≡ subst {P = B} p
transpP≡subst {A = A} {B} {x} {y} p = sym (transp-pi (λ j → uncurry (λ (y : A) → λ _ → B y) (contrSingl p j)) (λ x → x))

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe {A = A} = transpP {B = λ X → X}

module _ {ℓ} (A : Set ℓ) where
  isContr : Set ℓ
  isContr = Σ[ x ∈ A ] (∀ y → x ≡ y)

  isProp  : Set ℓ
  isProp  = (x y : A) → x ≡ y

  isSet   : Set ℓ
  isSet   = (x y : A) → (p q : x ≡ y) → p ≡ q

module _ {ℓ} {A : Set ℓ} where
  contr : isContr A → (φ : I) → (u : Partial A φ) → A
  contr (c , p) φ u = primComp (λ _ → A) φ (λ i o → p (u o) i) c

  lemContr : (contr1 : ∀ φ → Partial A φ → A)
             → (contr2 : ∀ u → u ≡ (contr1 i1 λ { _ → u})) → isContr A
  lemContr contr1 contr2 = x , (λ y → let module M = Aux y in
      trans (contr2 x) (trans (λ i → M.v i) (sym (contr2 y))))
    where x = contr1 i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial A φ
            u = λ { (i = i0) → x ; (i = i1) → y }
            v = contr1 φ u

  contrIsProp : isContr A → isProp A
  contrIsProp h a b i = primComp (λ _ → A) _ (λ j →
    \ { (i = i0) → snd h a j; (i = i1) → snd h b j }) (fst h)

module _ {ℓ ℓ' : I → _} {T : ∀ i → Set (ℓ i)} {A : ∀ i → Set (ℓ' i)}
         (f : ∀ i → T i → A i) (φ : I) (t : ∀ i → Partial (T i) φ)
         (tzero : T i0 {- [ φ ↦ t i0 ] -}) where
  private
    c1 c2 : A i1
    c1 = unsafeComp A φ (λ i → (λ { (φ = i1) → f i (t i itIsOne)})) (f i0 tzero)
    c2 = f i1 (unsafeComp T φ t tzero)

    azero = f i0 tzero

    a : ∀ i → Partial (A i) φ
    a i = (λ { (φ = i1) → f i ((t i) itIsOne)})

    u : ∀ i → A i
    u = fill A φ a azero

    v : ∀ i → T i
    v = fill T φ t tzero

  pres : c1 ≡ c2
  pres j = unsafeComp A (φ ∨ (j ∨ ~ j)) (λ i → primPOr φ (j ∨ ~ j)
    (a i) \ { (j = i1) → f i (v i); (j = i0) → u i}) azero

fiber : ∀ {ℓ ℓ'} {E : Set ℓ} {B : Set ℓ'} (f : E → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {E = E} f y = Σ[ x ∈ E ] y ≡ f x

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  isEquiv : (A → B) → Set (ℓ-max ℓ ℓ')
  isEquiv f = (y : B) → isContr (fiber f y)

  infix 4 _≃_
  _≃_ = Σ _ isEquiv

  module _ (f : _≃_) (φ : I) (t : Partial A φ) (a : B {- [ φ ↦ f t ] -})
           (p : PartialP φ (λ o → a ≡ fst f (t o))) where
    equiv : fiber (fst f) a -- [ φ ↦ (t , λ j → a) ]
    equiv = contr ((snd f) a) φ (λ o → t o , (λ i → p o i))

    equivFunc : A
    equivFunc = fst equiv

    equivProof : a ≡ fst f equivFunc
    equivProof = snd equiv

{-# BUILTIN ISEQUIV isEquiv #-}

idEquiv : ∀ {ℓ} → {A : Set ℓ} → A ≃ A
idEquiv {A = A} = idFun A , (λ y → (y , refl) , contrSingl ∘ snd)

module _ {ℓ} {A B : Set ℓ} (P : A ≡ B) where
  private
    E ~E : I → Set ℓ
    E  = λ i → P i
    ~E = λ i → P (~ i)

    f : A → B
    f = transp E

    g : B → A
    g = transp ~E

    u : PathP (λ i → A → E i) (idFun A) f
    u i x = fill E i0 (λ _ → empty) x i

    v : PathP (λ i → B → E i) g (idFun B)
    v i y = fill ~E i0 (λ _ → empty) y (~ i)

    fiberPath : (y : B) → (xβzero xβ1 : fiber f y) → xβzero ≡ xβ1
    fiberPath y (xzero , βzero) (x1 , β1) k = ω , λ j → δ j where
      module _ (j : I) where
        private
          sys : A → ∀ i → PartialP (~ j ∨ j) (λ _ → E (~ i))
          sys x i = λ {(j = i0) → v (~ i) y ; (j = i1) → u (~ i) x}
        ωzero = primComp ~E _ (sys xzero) (βzero j)
        ω1 = primComp ~E _ (sys x1) (β1 j)
        θzero = fill ~E _ (sys xzero) (βzero j)
        θ1 = fill ~E _ (sys x1) (β1 j)
      sys = λ {j (k = i0) → ωzero j ; j (k = i1) → ω1 j}
      ω = primComp (λ _ → A) _ sys (g y)
      θ = fill (λ _ → A) _ sys (g y)
      δ = λ (j : I) → primComp E ((~ j ∨ j) ∨ (~ k ∨ k))
            (λ i → λ { (j = i0) → v i y ; (k = i0) → θzero j (~ i)
                     ; (j = i1) → u i ω ; (k = i1) → θ1 j (~ i) }) (θ j)

    γ : (y : B) → y ≡ f (g y)
    γ y j = primComp E _ (λ i → λ { (j = i0) → v i y
                                  ; (j = i1) → u i (g y) }) (g y)

  pathToEquiv : A ≃ B
  pathToEquiv = f , (λ y → (g y , γ y) , fiberPath y _)

pathToEquivProof : ∀ {ℓ} (E : I → Set ℓ) → isEquiv (E i0) (E i1) (transp E)
pathToEquivProof E = snd (pathToEquiv P)
  where P : E i0 ≡ E i1
        P i = E i

{-# BUILTIN PATHTOEQUIV pathToEquivProof #-}

module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) (φ : I)
      → (T : Partial (Set ℓ') φ) → (f : PartialP φ (λ o → T o → A))
      → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {f : PartialP φ (λ o → T o → A)}
      → {pf : PartialP φ (λ o → isEquiv (T o) A (f o))}
      → PartialP φ T → A → primGlue A φ T f pf
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {f : PartialP φ (λ o → T o → A)}
      → {pf : PartialP φ (λ o → isEquiv (T o) A (f o))}
      → primGlue A φ T f pf → A

open GluePrims public renaming (prim^glue to glue ; prim^unglue to unglue)

module Unsafe'' (dummy : Set1) = GluePrims
module Unsafe''' = Unsafe'' Set -- using () renaming (prim^glue to unsafeGlue) public

unsafeGlue = Unsafe'''.prim^glue

Glue : ∀ {ℓ ℓ'} (A : Set ℓ) → (φ : I) → (T : Partial (Set ℓ') φ)
  (f : (PartialP φ (λ o → T o ≃ A))) → Set ℓ'
Glue A φ T f = primGlue A φ T (λ o → fst (f o)) (λ o → snd (f o))

equivToPath : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
equivToPath {_} {A} {B} f i = Glue B (~ i ∨ i)
  (λ {(i = i0) → A ; (i = i1) → B})
  (λ {(i = i0) → f ; (i = i1) → idEquiv})

primitive
  primFaceForall : (I → I) → I

module FaceForall (φ : I → I) where
  δ = primFaceForall φ
  postulate
    ∀v : ∀ i → IsOne (φ i) → IsOne ((δ ∨ (φ i0 ∧ ~ i)) ∨ (φ i1 ∧ i))
    ∀e : IsOne δ → ∀ i → IsOne (φ i)

module _ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial (Set ℓ') φ}
           {f : (PartialP φ λ o → T o ≃ A)} where
  fwdGlueIso : PartialP φ (λ o → Glue A φ T f → T o)
  fwdGlueIso (φ = i1) = idFun _

  backGlueIso : PartialP φ (λ o → T o → Glue A φ T f)
  backGlueIso (φ = i1) = idFun _

  lemGlueIso : (b : PartialP φ (λ _ → Glue A φ T f)) → PartialP φ λ o →
                 (unglue {φ = φ} (b o)) ≡ (fst (f o) (fwdGlueIso o (b o)))
  lemGlueIso _ (φ = i1) = refl

module CompGlue {ℓ ℓ' : I → _} (A : ∀ i → Set (ℓ i))
                (φ : I → I) (T : ∀ i → Partial (Set (ℓ' i)) (φ i))
                (f : ∀ i → PartialP (φ i) λ o → T i o ≃ A i)
                where
  B : ∀ i → Set (ℓ' i)
  B = λ i → Glue (A i) (φ i) (T i) (f i)

  module Local (ψ : I) (b : ∀ i → Partial (B i) ψ)
               (bzero : B i0 {- [ ψ ↦ b i0 ] -}) where
    a : ∀ i → Partial (A i) ψ
    a i = λ o → unglue {φ = φ i} (b i o)

    module Forall (δ : I) (∀e : IsOne δ → ∀ i → IsOne (φ i)) where
      azero : A i0
      azero = unglue {φ = φ i0} bzero

      a1' = unsafeComp A ψ a azero

      t1' : PartialP δ (λ o → T i1 (∀e o i1))
      t1' o = unsafeComp (λ i → T i (∀e o i)) ψ
                (λ i o' → fwdGlueIso {φ = φ i} (∀e o i) (b i o'))
                (fwdGlueIso {φ = φ i0} (∀e o i0) bzero)

      ω : PartialP δ _
      ω o = pres (λ i → fst (f i (∀e o i))) ψ
              (λ i x → fwdGlueIso {φ = φ i} (∀e o i) (b i x))
              (fwdGlueIso {φ = φ i0} (∀e o i0) bzero)

      a1'' = unsafeComp (λ _ → A i1) (δ ∨ ψ)
              (λ j → unsafePOr δ ψ (λ o → ω o j) (a i1)) a1'

      g : PartialP (φ i1) _
      g o = (equiv (T i1 _) (A i1) (f i1 o) (δ ∨ ψ)
        (unsafePOr δ ψ t1' (λ o' → fwdGlueIso {φ = φ i1} o (b i1 o'))) a1''
        ((unsafePOr δ ψ (λ {(δ = i1) → refl})
          ((λ{ (ψ = i1) → lemGlueIso {φ = φ i1} (λ _ → b i1 itIsOne) o })))))
      t1 α : PartialP (φ i1) _
      t1 o = fst (g o)
      α o = snd (g o)

      a1 = unsafeComp (λ j → A i1) (φ i1 ∨ ψ)
             (λ j → unsafePOr (φ i1) ψ (λ o → α o j) (a i1)) a1''

      b1 : Glue _ (φ i1) (T i1) (f i1)
      b1 = unsafeGlue {φ = φ i1} t1 a1
    b1 = Forall.b1 (FaceForall.δ φ) (FaceForall.∀e φ)

compGlue : {ℓ ℓ' : I → _} (A : ∀ i → Set (ℓ i)) (φ : I → I)
           (T : ∀ i → Partial (Set (ℓ' i)) (φ i))
           (f : ∀ i → PartialP (φ i) λ o → (T i o) → (A i)) →
           (pf : ∀ i → PartialP (φ i) (λ o → isEquiv (T i o) (A i) (f i o))) →
           let B : ∀ i → Set (ℓ' i)
               B = λ i → primGlue (A i) (φ i) (T i) (f i) (pf i)
           in  (ψ : I) (b : ∀ i → Partial (B i) ψ) (bzero : B i0) → B i1
compGlue A φ T f pf ψ b bzero =
  CompGlue.Local.b1 A φ T (λ i p → (f i p) , (pf i p)) ψ b bzero

{-# BUILTIN COMPGLUE compGlue #-}

-}
