2012. NK.

\begin{code}

{-# OPTIONS --without-K #-}

module KrausLemma where

open import mini-library

Type = Set

hprop : Type → Type
hprop X = (x y : X) → x ≡ y

constant : {X Y : Type} → (f : X → Y) → Type
constant {X} {Y} f = (x y : X) → f x ≡ f y

collapsible : Type → Type
collapsible X = Σ \(f : X → X) → constant f

fix : {X : Type} → (f : X → X) → Type
fix f = Σ \x → x ≡ f x

key-insight-generalized : {X Y : Type} (f : X → Y) (g : constant f) {x y : X} (p : x ≡ y)
                       → ap f p ≡ (g x x)⁻¹ • (g x y)
key-insight-generalized f g {x} {y} =
  J (λ {x} {y} p → ap f p ≡ (g x x)⁻¹ • (g x y)) (λ {x} → sym-is-inverse(g x x))

key-insight : {X Y : Type} (f : X → Y) → constant f → {x : X} (p : x ≡ x) → ap f p ≡ refl
key-insight f g p = (key-insight-generalized f g p) • ((sym-is-inverse(g _ _))⁻¹)

transport-paths-along-paths : {X Y : Type} {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x)
                           → transport p q ≡ (ap h p)⁻¹ • q • (ap k p)
transport-paths-along-paths {X} {Y} {x} p h k q =
 J' x (λ p → transport p q ≡ ((ap h p)⁻¹) • q • (ap k p)) (refl-is-right-id q) p

transport-paths-along-paths' : {X : Type} {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x)
                            → transport {X} {λ z → z ≡ f z} p q ≡ p ⁻¹ • q • (ap f p)
transport-paths-along-paths' {X} {x} p f q =
 (transport-paths-along-paths p (λ z → z) f q) • (ap (λ pr → pr ⁻¹ • q • (ap f p)) ((ap-id-is-id p)⁻¹))

Kraus-Lemma : {X : Type} → (f : X → X) → constant f → hprop(fix f)
Kraus-Lemma {X} f g (x , p) (y , q) =
  -- p : x ≡ f x
  -- q : y ≡ f y
  (x , p)        ≡⟨ Σ-≡ x y p p' r refl ⟩
  (y , p')       ≡⟨ Σ-≡ y y p' q s t ⟩
  (y , q)        ∎
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
         s ⁻¹ • (p' • ap f s)        ≡⟨ ap (λ pr → s ⁻¹ • (p' • pr)) (key-insight f g s) ⟩
         s ⁻¹ • (p' • refl)          ≡⟨ ap (λ pr → s ⁻¹ • pr) ((refl-is-right-id p')⁻¹)  ⟩
         s ⁻¹ • p'                   ≡⟨ refl  ⟩
         ((p' • q ⁻¹ • refl)⁻¹) • p' ≡⟨ ap (λ pr → ((p' • pr)⁻¹) • p') ((refl-is-right-id (q ⁻¹))⁻¹) ⟩
         (p' • (q ⁻¹))⁻¹ • p'        ≡⟨ ap (λ pr → pr • p') ((sym-trans p' (q ⁻¹))⁻¹)  ⟩
         ((q ⁻¹)⁻¹ • (p' ⁻¹)) • p'   ≡⟨ ap (λ pr → (pr • (p' ⁻¹)) • p') ((sym-sym-trivial q)⁻¹) ⟩
         (q • (p' ⁻¹)) • p'          ≡⟨ trans-assoc q (p' ⁻¹) p'  ⟩
         q • ((p' ⁻¹) • p')          ≡⟨ ap (λ pr → q • pr) ((sym-is-inverse p')⁻¹) ⟩
         q • refl                    ≡⟨ (refl-is-right-id q)⁻¹  ⟩
         q                           ∎

from-fix : {X : Type} (f : X → X) → fix f → X
from-fix f = π₀

to-fix : {X : Type} (f : X → X) → constant f → X → fix f
to-fix f g x = (f x , g x (f x))

\end{code}
