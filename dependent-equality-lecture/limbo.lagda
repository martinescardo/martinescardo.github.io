
Later we will generalize the above definition, because it actually has
little to do with vectors and is useful in many other similar
situations (which we will not explore in these notes).

The following generalizes our cong function to this situation, but
here we only consider the situation where the parameter to cong is
the "cons" function λ ws → x ∷ ws, which is what we needed above in
order to prove associativity of list concatenation, and which we will
need again to prove associativity of vector concatenation:

\begin{code}

cong-cons : ∀{X m n} (x : X) {xs : Vec X m} {ys : Vec X n} (p : m ≡ n)
          → xs ≡[ p ] ys → x ∷ xs  ≡[ cong succ p ]  x ∷ ys
cong-cons _ refl refl = refl 

\end{code}

Notice that if p : m ≡ n, then cong succ p : succ m ≡ succ n, and that
if

  xs : Vec X m and ys : Vec X n

then

  x ∷ xs : Vec X (succ m) and x ∷ ys : Vec X (succ n).

This is why from

  xs ≡[ p ] ys

we get

  x ∷ xs ≡[ cong succ p ] x ∷ ys

in the above definition.

So what we want to prove is that

  (xs ++ ys) ++ zs  ≡[ p ]  xs ++ (ys ++ zs)

for a suitable p : (l + m) + n ≡ l + (m + n), which we can take to be
+-assoc l m n. 

This statement does type check, and its proof is essentially the same
as that for the case of lists, recalled above. The crucial thing is
that now we need to use the fact that addition of natural numbers is
associative, as discussed above.

And with these remarks we are done. Here is the formulation and proof
that vector concatenation is associative:

\begin{code}

++-assoc : ∀{X} l m n (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
         → (xs ++ ys) ++ zs  ≡[ +-assoc l m n ]  xs ++ (ys ++ zs)
++-assoc zero     m n []       ys zs = refl
++-assoc (succ l) m n (x ∷ xs) ys zs = goal
 where
  IH : (xs ++ ys) ++ zs  ≡[ +-assoc l m n ]  xs ++ (ys ++ zs)
  IH = ++-assoc l m n xs ys zs
  goal : x ∷ ((xs ++ ys) ++ zs)  ≡[ cong succ (+-assoc l m n) ]
         x ∷ (xs ++ (ys ++ zs))
  goal = cong-cons x (+-assoc l m n) IH

\end{code}

If you have begun to understand these subtleties, then I have achieved
my learning objective.

Dependent equality more generally
=================================

But, to conclude, I am a little bit more ambitious.

We want to briefly generalize the above. Notice that

  Vec X : ℕ → Set.

We replace "Vec X" by an arbitrary "B", and "ℕ" by an arbitrary "A":

  A : Set,
  B : A → Set.

Then B is a family of sets indexed by A. In our main example,

  A = ℕ,
  B = Vec X.

Our generalized dependent equality is

  b₀ ≡⟦ p ⟧ b₁

for

  a₀ a₁ : A,
     p  : a₀ ≡ a₁,
     b₀ : B a₀,
     b₁ : B a₁.

The types are more general, but the definition is the same as in the
particular case:

\begin{code}

_≡⟦_⟧_ : {A : Set} {B : A → Set} {a₀ a₁ : A}
       → B a₀ → a₀ ≡ a₁ → B a₁ → Set
b₀ ≡⟦ refl ⟧ b₁   =   b₀ ≡ b₁

\end{code}

We then generalize cong defined above to a dependent version:

\begin{code}

congd : {A : Set} {B : A → Set} (f : (a : A) → B a) {a₀ a₁ : A}
     → (p : a₀ ≡ a₁) → f a₀ ≡⟦ p ⟧ f a₁
congd f refl = refl

\end{code}

Conclusion
==========

Equality is subtler than it seems at first sight, but with the right
concepts and tools, and with practical experience, it becomes natural.

Of course there is much more to say, and the systematic study of
(dependent or independent) equality in dependent type theory is the
topic of "univalent foundations" or "homotopy type theory", which is
beyond the scope of this module: https://homotopytypetheory.org/book

But in the past we have had successful reading groups and clubs with
undergrad, MSc, and PhD students, as well as with academic staff.

--------------------------------------------------------------------
Notational appendix. To complete our code so that it parses, we list
all fixities together for easy comparison of the operator precedences:

\begin{code}

infixr 5 _≡_
infixr 5 _≡[_]_
infixr 5 _≡⟦_⟧_
infixl 6 _++_
infixl 6 _+_
infixr 7 _∷_

\end{code}
