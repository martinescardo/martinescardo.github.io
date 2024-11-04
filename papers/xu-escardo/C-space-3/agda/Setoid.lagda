Chuangjie Xu, 2012

\begin{code}

module Setoid where

open import Mini-library


Setoid : Set₁
Setoid = Σ \(A : Set) →
          Σ \(_~_ : A → A → Set) →
             (∀(a : A) → a ~ a)
           ∧ (∀(a a' : A) → a ~ a' → a' ~ a)
           ∧ (∀(a₀ a₁ a₂ : A) → a₀ ~ a₁ → a₁ ~ a₂ → a₀ ~ a₂)

Ũ : Setoid → Set
Ũ (A , _) = A

E : (A : Setoid) → Ũ A → Ũ A → Set
E (_ , _~_ , _) = _~_

Refl : (A : Setoid) → ∀(a : Ũ A) → E A a a
Refl (_ , _ , r , _) = r

Sym : (A : Setoid) → ∀(a a' : Ũ A) → E A a a' → E A a' a
Sym (_ , _ , _ , s , _) = s

Trans : (A : Setoid) → ∀(a₀ a₁ a₂ : Ũ A) → E A a₀ a₁ → E A a₁ a₂ → E A a₀ a₂
Trans (_ , _ , _ , _ , t) = t


E-map : Setoid → Setoid → Set
E-map (A , _~_ , _) (B , _≈_ , _) = Σ \(f : A → B) → ∀(a a' : A) → a ~ a' → f a ≈ f a'

⟨_∣_∣_⟩_◎_ : (A B C : Setoid) → E-map B C → E-map A B → E-map A C
⟨ A ∣ B ∣ C ⟩ (g , eg) ◎ (f , ef) = g ∘ f , (λ a a' z → eg (f a) (f a') (ef a a' z))

E-id : {A : Setoid} → E-map A A
E-id = id , (λ a a' z → z) 


infixl 4 _✻_
infixl 4 _✣_
infixl 4 _➡_

_✻_ : Setoid → Setoid → Setoid
(A , _~_ , rA , sA , tA) ✻ (B , _≈_ , rB , sB , tB) =
            (A × B , _≋_ , rC , sC , tC)
 where
  _≋_ : A × B → A × B → Set
  (a , b) ≋ (a' , b') = (a ~ a') ∧ (b ≈ b')
  rC : ∀(c : A × B) → c ≋ c
  rC (a , b) = rA a , rB b
  sC : ∀(c c' : A × B) → c ≋ c' → c' ≋ c
  sC (a , b) (a' , b') (ea , eb) = sA a a' ea , sB b b' eb
  tC : ∀(c₀ c₁ c₂ : A × B) → c₀ ≋ c₁ → c₁ ≋ c₂ → c₀ ≋ c₂
  tC (a₀ , b₀) (a₁ , b₁) (a₂ , b₂) (ea , eb) (ea' , eb') = tA a₀ a₁ a₂ ea ea' , tB b₀ b₁ b₂ eb eb'

E-π₀ : {A B : Setoid} → E-map (A ✻ B) A
E-π₀ = π₀ , (λ c c' eq → ∧-elim₀ eq)

E-π₁ : {A B : Setoid} → E-map (A ✻ B) B
E-π₁ = π₁ , (λ c c' eq → ∧-elim₁ eq)


_✣_ : Setoid → Setoid → Setoid
(A , _~_ , rA , sA , tA) ✣ (B , _≈_ , rB , sB , tB) =
            (A ⊎ B , _≋_ , rC , sC , tC)
 where
  _≋_ : A ⊎ B → A ⊎ B → Set
  (in₀ a) ≋ (in₀ a') = a ~ a'
  (in₀ a) ≋ (in₁ b') = ∅
  (in₁ b) ≋ (in₀ a') = ∅
  (in₁ b) ≋ (in₁ b') = b ≈ b'
  rC : ∀(c : A ⊎ B) → c ≋ c
  rC (in₀ a) = rA a
  rC (in₁ b) = rB b 
  sC : ∀(c c' : A ⊎ B) → c ≋ c' → c' ≋ c
  sC (in₀ a) (in₀ a') eq = sA a a' eq
  sC (in₀ a) (in₁ b') ()
  sC (in₁ b) (in₀ a') ()
  sC (in₁ b) (in₁ b') eq = sB b b' eq
  tC : ∀(c₀ c₁ c₂ : A ⊎ B) → c₀ ≋ c₁ → c₁ ≋ c₂ → c₀ ≋ c₂
  tC (in₀ a₀) (in₀ a₁) (in₀ a₂) eq eq' = tA a₀ a₁ a₂ eq eq'
  tC (in₀ a₀) (in₀ a₁) (in₁ b₂) _  ()
  tC (in₀ a₀) (in₁ b₁) (in₀ a₂) () ()
  tC (in₀ a₀) (in₁ b₁) (in₁ b₂) () _
  tC (in₁ b₀) (in₀ a₁) (in₀ a₂) () _
  tC (in₁ b₀) (in₀ a₁) (in₁ b₂) () ()
  tC (in₁ b₀) (in₁ b₁) (in₀ a₂) _  ()
  tC (in₁ b₀) (in₁ b₁) (in₁ b₂) eq eq' = tB b₀ b₁ b₂ eq eq'

E-in₀ : {A B : Setoid} → E-map A (A ✣ B)
E-in₀ = in₀ , λ a a' z → z

E-in₁ : {A B : Setoid} → E-map B (A ✣ B)
E-in₁ = in₁ , λ a a' z → z


_➡_ : Setoid → Setoid → Setoid
X ➡ Y = (E-map X Y , _≋_ , rC , sC , tC)
 where
  A : Set
  A = Ũ X
  B : Set
  B = Ũ Y
  _≈_ : B → B → Set
  _≈_ = E Y
  rB : ∀(b : B) → b ≈ b
  rB = π₀ (π₁ (π₁ Y))
  sB : ∀(b b' : B) → b ≈ b' → b' ≈ b
  sB = π₀ (π₁ (π₁ (π₁ Y)))
  tB : ∀(b₀ b₁ b₂ : B) → b₀ ≈ b₁ → b₁ ≈ b₂ → b₀ ≈ b₂
  tB = π₁ (π₁ (π₁ (π₁ Y)))
  _≋_ : E-map X Y → E-map X Y → Set
  (f , _) ≋ (g , _) = ∀(a : A) → f a ≈ g a
  rC : ∀(c : E-map X Y) → c ≋ c
  rC (f , _) = λ a → rB (f a)
  sC : ∀(c c' : E-map X Y) → c ≋ c' → c' ≋ c
  sC (f , _) (f' , _) eq = λ a → sB (f a) (f' a) (eq a)
  tC : ∀(c₀ c₁ c₂ : E-map X Y) → c₀ ≋ c₁ → c₁ ≋ c₂ → c₀ ≋ c₂
  tC (f₀ , _) (f₁ , _) (f₂ , _) eq eq' = λ a → tB (f₀ a) (f₁ a) (f₂ a) (eq a) (eq' a)


E∅ : Setoid
E∅ = ∅ , (λ _ → λ ()) , (λ ()) , (λ x → λ ()) , (λ x x₁ → λ ())

E⒈ : Setoid
E⒈ = ⒈ , _≡_ , (λ _ → refl) , (λ _ _ eq → sym eq) , (λ _ _ _ eq eq' → trans eq eq')

E-unit : {A : Setoid} → E-map A E⒈
E-unit = unit , λ a a' e → refl


Eℕ : Setoid
Eℕ = ℕ , _≡_ , (λ _ → refl) , (λ _ _ eq → sym eq) , (λ _ _ _ eq eq' → trans eq eq')

E-succ : E-map Eℕ Eℕ
E-succ = succ , claim
 where
  claim : ∀(n n' : ℕ) → n ≡ n' → succ n ≡ succ n'
  claim n .n refl = refl


E₂ : Setoid
E₂ = ₂ , _≡_ , (λ _ → refl) , (λ _ _ eq → sym eq) , (λ _ _ _ eq eq' → trans eq eq')


_≣_ : ₂ℕ → ₂ℕ → Set
α ≣ β = ∀(i : ℕ) → α i ≡ β i

E₂ℕ : Setoid
E₂ℕ = ₂ℕ , _≣_ , (λ α i → refl) ,
                 (λ α β f i → sym (f i)) ,
                 (λ α β γ f g i → trans (f i) (g i))

⟨_∣_⟩_◎_ : (B C : Setoid) → E-map B C → E-map E₂ℕ B → E-map E₂ℕ C
⟨_∣_⟩_◎_ B C f p = ⟨ E₂ℕ ∣ B ∣ C ⟩ f ◎ p

⟨_⟩_◎_ : (C : Setoid) → E-map E₂ℕ C → E-map E₂ℕ E₂ℕ → E-map E₂ℕ C
⟨_⟩_◎_ C p t = ⟨ E₂ℕ ∣ E₂ℕ ∣ C ⟩ p ◎ t

infixl 30 _◎_

_◎_ : E-map E₂ℕ E₂ℕ → E-map E₂ℕ E₂ℕ → E-map E₂ℕ E₂ℕ
t ◎ r  = ⟨ E₂ℕ ∣ E₂ℕ ∣ E₂ℕ ⟩ t ◎ r


E-map-₂ℕ : Setoid → Set
E-map-₂ℕ A = E-map E₂ℕ A

E-map-₂ℕ-₂ℕ : Set
E-map-₂ℕ-₂ℕ = E-map E₂ℕ E₂ℕ


Lemma[₂ℕ-E-map] : ∀(α : ₂ℕ) → ∀(i j : ℕ) → i ≡ j → α i ≡ α j
Lemma[₂ℕ-E-map] α i .i refl = refl

\end{code}