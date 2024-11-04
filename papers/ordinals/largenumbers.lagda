Martin Escardo, February 2015. 
Comment at the very end updated 11 Mar 2015.

Perhaps just for amusement.

We define the rather large number 

   2^2^2^2^2^2^2^2^2^2 : ℕ 

without using any kind of recursion. 
-----------------------------------

Of course, this can be done with a program of length
2^2^2^2^2^2^2^2^2^2 multiplied by a small factor. 

The program succ(succ(succ(...succ(zero)))) will do, by suitably
expanding the dots.

Our program below is shorter.

If you have problems with unicode, read this here instead:
 http://www.cs.bham.ac.uk/~mhe/papers/ordinals/largenumbers.html
 http://www.cs.bham.ac.uk/~mhe/papers/ordinals/largenumbers.lagda

We use Agda, but what we do takes place in its Gӧdel's system T
fragment. In fact, this works in system T *without* the primitive
recursion (or iteration) combinator.

We need a natural numbers type ℕ with zero and successor and nothing
else, in particular no primitive recursion.

So we may work in the simply typed lambda calculus with a base type ℕ
and constants zero:ℕ and succ:ℕ→ℕ.

The only way to do recursion in Agda is via pattern matching. We
disable it, to be sure:

\begin{code}

{-# OPTIONS --no-pattern-matching #-}

U = Set

data ℕ : U where
 zero : ℕ
 succ : ℕ → ℕ

\end{code}

The idea is to work with Church encodings of natural numbers. But the
goal, as stated above, is to define an element of ℕ. 

Church encodings will help us to avoid recursion in defining such an
element of ℕ.

But we have a problem. Schwichtenberg (1976) showed that the
exponential function is not definable in the simply typed lambda
calculus via Church encodings. 

Only polynomials can be defined.

   Helmut Schwichtenberg. "Functions definable in the simply typed
   lambda calculus". Arch. Math. Logik 17 (1976). English translation
   by RJ Irwin. http://www.cis.syr.edu/~royer/htc96/fdst.ps

We have to side-step this.

Schwichtenberg considers a base type o, and his Church encodings live
in the type (o → o) → (o → o).

We instead consider Church encodings based on an arbitrary type X.

\begin{code}

N : U → U
N X = (X → X) → (X → X)

𝟘 𝟙 𝟚 𝟛 : {X : U} → N X
𝟘 = λ s z → z
𝟙 = λ s z → s z
𝟚 = λ s z → s(s z)
𝟛 = λ s z → s(s(s z))

suc : {X : U} → N X → N X
suc n = λ s z → s(n s z)

add : {X : U} → N X → N X → N X
add m n = λ s z → m s (n s z)

\end{code}

The following codes primitive recursion without using any kind of
recursion:

\begin{code}

N-rec : {X : U} → (X → X) → X → (N X → X)
N-rec s z m = m s z

\end{code}

We live with Schwichtenberg's result by giving different types to
multiplication and exponentiation. The idea is to iterate N when our
definitions don't type check, to make them type check:

\begin{code}

mul : {X : U} → N X → N(N X) → N X
mul m = N-rec (add m) 𝟘

exp : {X : U} → N(N X) → N(N X) → N X
exp n = N-rec (λ m → mul m n) 𝟙 

\end{code}

We defined exp in several steps to try to be understandable. Expanding
the definitions, we get the direct, shorter, equivalent definition,
which we include for the record:

\begin{code}

exp' : {X : U} → N(N X) → N(N X) → N X
exp' n l = l (λ m → n (λ k s z → m s (k s z)) (λ s z → z)) (λ s z → s z)

\end{code}

We can now define our promised large natural number with a short
expression, without using recursion:

\begin{code}

decode : N ℕ → ℕ
decode = N-rec succ zero

large : ℕ
large = decode
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
 (exp 𝟚 
      𝟚)))))))))

\end{code}

Oh, but the above is cheating! There are implicit parameters. In fact,
if I write "?" for them and then I automatically fill them with
ctrl-c-ctrl-a, I get a 28000-line agda file. The implicit parameters
are rather large!

Very big, but still much smaller than 2^2^2^2^2^2^2^2^2^2.

However, we can make the implicit parameters small, 
using our "macro" N:

\begin{code}

large' : ℕ
large' = decode
 (exp{ℕ}                        (𝟚{N ℕ}) 
 (exp{N ℕ}                      (𝟚{N(N ℕ)}) 
 (exp{N(N ℕ)}                   (𝟚{N(N(N ℕ))}) 
 (exp{N(N(N ℕ))}                (𝟚{N(N(N(N ℕ)))}) 
 (exp{N(N(N(N ℕ)))}             (𝟚{N(N(N(N(N ℕ))))}) 
 (exp{N(N(N(N(N ℕ))))}          (𝟚{N(N(N(N(N(N ℕ)))))}) 
 (exp{N(N(N(N(N(N ℕ)))))}       (𝟚{N(N(N(N(N(N(N ℕ))))))}) 
 (exp{N(N(N(N(N(N(N ℕ))))))}    (𝟚{N(N(N(N(N(N(N(N ℕ)))))))}) 
 (exp{N(N(N(N(N(N(N(N ℕ)))))))} (𝟚{N(N(N(N(N(N(N(N(N ℕ))))))))}) 
                                 (𝟚{N(N(N(N(N(N(N(N(N ℕ))))))))}))
 )))))))) 

\end{code}

This illustrates that, when we regard our definitions as taking place
in system T, the definition of exp is not uniform. In the definition
of "large", each occurrence of exp has a different type.

Of course, don't try to run the above. For testing, we need to be more
modest:

\begin{code}

number16 : ℕ
number16 = decode(exp 𝟚 (exp 𝟚 𝟚))

number81 : ℕ
number81 = decode(exp 𝟛 (exp 𝟚 𝟚))

number1296 : ℕ
number1296 = decode(mul(exp 𝟚 (exp 𝟚 𝟚))(exp 𝟛 (exp 𝟚 𝟚)))

{-# BUILTIN NATURAL ℕ #-}

\end{code}

You should get 16, 81, and 1296 when you normalize the above terms
with ctrl-c-ctrl-n.

I decided to write the above because some people were asking me about
ordinals in system T, following
http://www.cs.bham.ac.uk/~mhe/papers/ordinals/ordinals.html

What happens there is similar: we can get as close as we wish to the
ordinal ε₀ in system T without using recursion on ordinals (but this
time using recursion on ℕ). Of course, this is not my own finding.

I thought it would be worthwhile to abstract away from the ordinals,
and show how this works for ℕ, as explained above.

However, the above use of iterations of N may be new (but I can't be
sure).

To the last parenthetical remark, Aaron Stump added the following
comment in the Agda mailing list, Wed Mar 11 02:29:56 CET 2015
https://lists.chalmers.se/pipermail/agda/2015/007591.html

> I believe you can find this (presented quite a bit more densely!) in
> some papers by Daniel Leivant, exploring the computational power of
> predicative polymorphism.  See his CMU tech report "Finitely
> stratified polymorphism" (there is also a LICS '89 paper on the
> topic): http://repository.cmu.edu/compsci/1962/

Indeed, the definition of our N is at the top of page 6. 
