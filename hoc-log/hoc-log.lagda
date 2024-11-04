
H i g h e r -  o r d e r   c o m p u t a t i o n

l e c t u r e   l o g


Martín Hötzel Escardó
Nordic Logic School (NLS), Stockholm, 2017


The original plan and (rather incomplete) bibliographic references:
http://www.cs.bham.ac.uk/~mhe/papers/introduction-to-higher-order-computation-NLS-2017.pdf


The lectures are blackboard based, and here is a summary of what we've
actually covered.


Monday's lecture
----------------

Computation/computability:

(1) What is computable? (Computability.)
(2) But, in the first place, how do we compute it? (Computation.) 

* 1st-order computation is about computation with finite objects
  (strings, trees, graphs, etc.), usually coded as natural
  numbers. Most of you know about that, but we revised the fundamental
  concepts.

* Higher-order computation is about computation with infinite objects
  (infinite sequences, infinite trees, infinite graphs, real numbers
  (such as π), functions ℝ → ℝ (such as e^x), functionals (ℝ → ℝ) ⇀ ℝ
  (such as Riemann integration ∫ from 0 to 1 of continuous functions),
  etc.).

I mentioned Gödel's system T and Platek-Scott-Plotkin PCF as languages
for higher-order computation, but this will be developed in future
lectures (also discussing Martin-Löf type theory if there is enough
time).


* Turing machines, informally.

Definition. A partial function f:ℕ^k ⇀ ℕ is called Turing computable
(or computable for short) if there is a Turing machine t such that
with an initial tape encoding the input x = (x_0,...x_{k-1}), the
machine terminates if and only if x is in the domain of definition of
f, and final tape encodes the number f(x).

To make sure we are on the same page:

Definition. A partial function X ⇀ Y is a function X' → Y, where X'⊆X
is called the domain of definition of the function.

Our notion of function includes the specification of its source X and
its target Y. Our notion of partial function additionally includes its
domain of definition X'⊆X. Such a partial function is called total if
X' is the whole of X.

* Primitive recursive, and μ-recursive functions, more
  rigorously. Their Wikipedia pages can be used as a safe reference.

Theorem. A partial function ℕ^k ⇀ ℕ is μ-recursive if and only if it
is Turing computable.

This gives a more natural mathematical description of the notion of
Turing computable function.

* Examples of non-computable functions.

We enumerate Turing machines t_n, or μ-recursive functions φ_n.

Theorem (Turing 1936). There is no computable (total) function h:ℕ^2 → ℕ
such that

  h(x,y) = 1 iff the Turing machine t_x terminates when given input y.
         
"There is no computer program that decides whether a given program
terminates with a given input or not".

Hints for a proof: If we had such a program, there would be some
μ-recursive function φ_n with h(x,y) = φ_n⟨x,y⟩, where

  ⟨-,-⟩ : ℕ^2 → ℕ

is a (primitive) recursive bijection. Then using this number n we can
"trick" our hypothetical function h, by constructing μ-recursive
function with code k which decides to terminate iff h says that it
doesn't, by a diagonalization argument (giving input n to the function
φ_n). This contradiction then shows that our hypothetical computable
total function h is impossible.

Sample Corollary. There is no computable total function e:ℕ^2 → ℕ such
that

   e(x,y) = 1 iff the functions φ_x and φ_y are equal.

(Why? Or, better, how do we reduce this to the theorem?)

* Moving on to computation with infinite objects.

Our first example are sequences of natural numbers. The set of them is
written ℕ^ω. We want to compute functions ℕ^ω → ℕ^ω.

Modified Turing machines.


    input tape                    output tape
    (read only)   +------------+  (write only)
   -------------> |  machine   | ------------->
                  +------------+
                     |      |
         ----------- + head + ----------- working tape (read and write)
                     |      |             (scratch space)


The machine is like the usual Turing machine, but it can additionally
read from the input and write to the output.

It alternates between reading finitely many input terms, calculating
in the usual way a TM does, outputting finitely many output terms, in
an infinite loop. We don't want such machines to terminate. We want
them not to terminate.

* This defines a notion of computable function ℕ^ω → ℕ^ω.

(But what happens when the machine fails to produce the required
output? We didn't discuss this, but we will.)

* One approach to computation with infinite objects is to reduce to
  the above situation (this approach is called TTE (type two theory
  of effectivity, and can be traced back to "Kleene associates")).

This works like this:

- We consider a set X of infinite objects we want to compute
  with. (E.g. X=ℝ or X the real interval [0,1].)

- We consider a set A⊆ℕ^ω of "codes" for elements of X.

- We consider a "decoding function", namely a surjection q:A ↠ X.

Definition. This is called a representation of X.

An example is decimal representation of real numbers (we will discuss
this in more detail).

Then x∈X is called computable if there is a computable a∈A (we already
know what this means, namely that the element a∈A considered as a
function ℕ → ℕ is computable or μ-recursive).

* These are ℕ^ω-based representations. We also mentioned briefly
  ℕ-based representations, which I will mention again for the sake of
  comparison. But our focus will be on the former.

Tuesday's lecture
-----------------

Computation with infinite objects.


           f              f is the function we want to compute.    
    X ----------→ Y     
    ↑             ↑
    |             |       The up arrows q and r are the decoding functions,
  q |             | r     required to be surjections.
    |             |
    A ··········→ B       A and B are sets of codes for elements of X and Y.
    |      φ      |       The function φ realizes f by acting on codes.
    |             |       
    |             |       The down arrows are nameless inclusion maps.
    ↓             ↓ 
    ℕ^ω -------⇀ ℕ^ω      This is the nameless partial function induced by φ.
        machine
   
The idea is that we reduce computation with infinite objects to
computation with particular infinite objects, namely sequences of
natural numbers.

Definition. f:X→Y is computable (with respect to this coding) if there
is φ:A→B that can be implemented by a machine of the kind discussed on
Monday's lecture.

* We start with "abstract" mathematical sets X and Y.

* We come up with codes for the elements of X and Y, collected in the
  sets A and B.

* Our codes are particular sequences of natural numbers.

* We compute f by computing on codes for the inputs and outpus of f.

Example. Multiply by three using decimal representation.

   - X = Y = [0,1].

   - f(x) = 3x/10.

   - A = B = (infinite sequences of the numbers 0,1,⋯,8,9).

   - q(α) = r(α) = α₀/10 + α₁/100 + α₂/1000 + ⋯ + αₙ/10ⁿ⁺¹ + ⋯

                 =  Σ   αₙ 10⁻ⁿ⁻¹. 
                   n≥0

   - Are there such a realizing function φ and computing machine?

       f(x)=3x/10
  [0,1] ------→ [0,1]     
    ↑             ↑
    |             |       
  q |             | r     
    |             |
  (10)^ω ······→ (10)^ω
    |      φ      |         Is there such a φ
    |             |       
    |             |       
    ↓             ↓ 
    ℕ^ω -------⇀ ℕ^ω      
        machine             computable by such a machine?


Our next task is to answer this question.

* In order to do this, we discuss the notion of continuity.

Intuitively, and this can be proved rigorously, a function g:ℕ^ω → ℕ^ω
that can be computed by a such a machine satisfies the following property:

  - An initial finite segment of the output of g can depend only on an
    initial finite segment of the input of g.

* How do we say this precisely? By saying that g is continuous.

(In the lecture we did this slowly in four stages, in particular
understanding the difference between continuity and uniform
continuity, but in this summary I do it in one stage only.)

Definition. A function g:ℕ^ω → ℕ^ω is continuous iff

   ∀α∈ℕ^ω ∀m∈ℕ ∃k∈ℕ ∀β∈ℕ^ω  α =ₖ β → g(α) =ₘ g(β).

Here the relation (=ₖ) expresses equality of two sequences in the
first k terms: α =ₖ β means ∀i<k, αᵢ = βᵢ.

Of course, we use the same definition when g is a partial function,
but with α and β ranging over the domain of definition of g, rather
than the whole of ℕ^ω.

This is a precise way of saying that finite portions of the output of
g depend only on finite portions of its input.

Why is this called continuity? Compare it to the notion of
continuity of functions g:ℝ → ℝ:

   ∀x∈ℝ ∀ε>0 ∃δ>0 ∀y∈ℝ  |x-y|<δ → |g(x)-g(y)|<ε.
   
Define a distance function d(x,y)=|x-y|. This makes ℝ into a metric
space (I won't repeat the definition given in the lecture), and the
definition of continuity of g:ℝ → ℝ can be rewritten as

   ∀x∈ℝ ∀ε>0 ∃δ>0 ∀y∈ℝ  d(x,y)<δ → d(g(x),g(y))<ε.

Now for ℕ^ω, define a distance

   d(α,β) = 0,       if α = β,
          = 1/(k+1), otherwise, where k is the largest number with α =ₖ β.

Or d(α,β) = infimum { 1/(k+1) | α =ₖ β }.

This makes ℕ^ω into a metric space (in fact even into an ultrametric
space, and again I won't record the definition given in the lecture,
in this summary), called the Baire space.

And we have that a function g:ℕ^ω → ℕ^ω is continuous iff

   ∀α∈ℕ^ω ∀ε>0 ∃δ>0 ∀β∈ℕ^ω  d(α,β)<δ → d(g(α),g(β))<ε.

* Now let's come back to the example and its question. Can we multiply
  by three in decimal notation?

       f(x)=3x/10
  [0,1] ------→ [0,1]     
    ↑             ↑
    |             |       
  q |             | r     
    |             |
  (10)^ω ······→ (10)^ω
    |      φ      |         Is there such a φ
    |             |       
    |             |       
    ↓             ↓ 
    ℕ^ω -------⇀ ℕ^ω      
        machine g           computable by such a machine?


    - Suppose the machine reads 3 to begin with (with an implicit "0."
      prefix).

    - Is this enough to produce the first digit of the output?

    - No, because if the next digit of the input is >=4, then the
      first digit of the output must be 1, whereas if the next digit
      of the input is <=2, the first digits of the output must be 09.

    - So we ask for the next input digit, and if it is >=4 or <=2, we
      know what the first digit of the output must be.

    - The problem is that if the next input digit is =3, it is again
      possible that the first digit of the output is 1 or 0, and so we
      can't output anything yet.

    - And as long as we keep reading digits 3 from the input, it is
      still possible that the first digit of output is either 1 or 0.

    - If the input happens to the the infinite sequence of 3's, we
      will never be able, by looking at a finite prefix of this
      sequence, to produce the first digit of output.

What this means is that there is no continuous φ (or g) making the
above diagram commute. 

Theorem (Attributable to Brouwer 1920's, even though computability as
a mathematical subject didn't yet exist at that time).

    Multiplication by three is not computable in decimal notation.

In the next lecture, we will discuss what Brouwer proposed to do to
solve this problem, and some equivalent variations, and discuss in
which way they do solve the problem, by invoking the notion of
admissible quotient representation.

Wednesday's lecture
-------------------

We discussed admissible quotient representations, and in particular
discussed that binary and decimal notations are not admissible, but
that binary with signed digits is admissible. We also showed that
there is a unique representation of [-1,1], up to (computable)
equivalence, making certain basic functions computable. I may add more
material discussed in the lecture here.

Thursday's lecture
------------------

We are going to exhaustively search an infinite set in finite time in
Gödel's T.  The fragments below within code environments are in the
language Agda, but we only use its T fragment.  I am first going to
write Gödel's T programs, and then explain what Gödel's T is.

For the natural numbers, we have two "constructors", zero and
succ(essor):

\begin{code}

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

\end{code}

Gödel's T doesn't include booleans, but it is harmless to include
them, and this will make our programs much clearer (but below I write
a version using the type ℕ only, to show how this works):

\begin{code}

data 𝟚 : Set where
 ₀ ₁ : 𝟚

\end{code}

Some abbreviations: 

\begin{code}

Baire Cantor : Set
Baire  = ℕ → ℕ
Cantor = ℕ → 𝟚

\end{code}

We are going to write several versions of the same program, and we use
"modules" to keep names local so that we can use them again in
equivalent definitions:

\begin{code}

module version₁ where

 \end{code}

Functions on 𝟚 have to be defined by the two cases ₀ and ₁, and this
is an example:

\begin{code}

 min : 𝟚 → 𝟚 → 𝟚
 min ₀ n = ₀
 min ₁ n = n

\end{code}
 
The natural number n is coded as the sequence 11111⋯10^ω, where we
have n-many 1's and infinitely many 0's. This is done by primitive
recursion on n, using a further, nested, primitive recursion:

\begin{code}

 embed : ℕ → Cantor
 embed zero i = ₀
 embed (succ n) zero = ₁
 embed (succ n) (succ i) = embed n i

\end{code}

I will explain this later, but it is also defined by primitive
recursion:

\begin{code}

 ε : (Cantor → 𝟚) → Cantor 
 ε p zero     = p (embed zero) 
 ε p (succ n) = min (ε p n) (p (embed(succ n))) 

\end{code}

We can write

 ε p n = minimum {p(embed 0), p(embed 1), ⋯ , p(embed n)}

This is supposed to satisfy the following specification, but this
remains to be proved: A(p)=1 ⇔ p(α)=1 for all *decreasing* sequences
α:Cantor. These sequences include 11111⋯10^ω and 1^ω, the sequence of
infinitely many 1's. Using classical logic, these are the only two
possible kinds of decreasing sequences.

\begin{code}

 A : (Cantor → 𝟚) → 𝟚
 A p = p(ε p)

\end{code}

The specification of ε is that p(ε p)=1 → p(α)=1 for all decreasing
sequences α:Cantor, and that ε p is itself a decreasing sequence. But
we still have to prove this.

In summary, without the comments:

\begin{code}
 
module version₂ where

 min : 𝟚 → 𝟚 → 𝟚
 min ₀ n = ₀
 min ₁ n = n

 embed : ℕ → Cantor
 embed zero i = ₀
 embed (succ n) zero = ₁
 embed (succ n) (succ i) = embed n i

 ε : (Cantor → 𝟚) → Cantor 
 ε p zero     = p (embed zero) 
 ε p (succ n) = min (p (embed(succ n))) (ε p n) 

 A : (Cantor → 𝟚) → 𝟚
 A p = p(ε p)

\end{code}

We now rewrite the above definitions in a number of stages, until we
eventually use Gödel's T notation only. First we use λ:

\begin{code}

module version₃ where

 min : 𝟚 → 𝟚 → 𝟚
 min ₀ = λ n → ₀
 min ₁ = λ n → n

 embed : ℕ → Cantor
 embed zero = λ i → ₀
 embed (succ n) zero = ₁
 embed (succ n) (succ i) = embed n i

 ε : (Cantor → 𝟚) → Cantor 
 ε p zero     = p (embed zero) 
 ε p (succ n) = min (p (embed(succ n))) (ε p n) 

 A : (Cantor → 𝟚) → 𝟚
 A = λ p → p(ε p)

\end{code}

Not much has changed. Now we introduce the Gödel's T primitive
"combinators", primitive recursion on the natural numbers (and
definition by cases on the booleans, in our extended version of
Gödel's system T). This is "global", outside any module.

\begin{code}

rec : {X : Set} → X → (ℕ → X → X) → ℕ → X
rec x f zero     = x
rec x f (succ n) = f n (rec x f n)

cases : {X : Set} → X → X → 𝟚 → X
cases x y ₀ = x
cases x y ₁ = y

 \end{code}

Using this we can get closer to T notation.

There are two nested recursions in the definition of embed. Before
using rec, we split them, for use in version₅:

\begin{code}

module version₄ where

 min : 𝟚 → 𝟚 → 𝟚
 min = λ m n → cases ₀ n m

 embed : ℕ → Cantor
 embed zero = λ i → ₀
 embed (succ n) = g n (embed n)
  where
   g : ℕ → Cantor → Cantor
   g _ α = rec ₁ (λ i _ → α i)

 ε : (Cantor → 𝟚) → Cantor 
 ε = λ p → rec (p (embed zero)) (λ n → min (p (embed(succ n)))) 

 A : (Cantor → 𝟚) → 𝟚
 A = λ p → p(ε p)

\end{code}

Now this is almost a system T term:

\begin{code}

module version₅ where

 min : 𝟚 → 𝟚 → 𝟚
 min = λ m n → cases ₀ n m

 embed : ℕ → Cantor
 embed = rec (λ i → ₀) (λ _ α → rec ₁ (λ i _ → α i))

 ε : (Cantor → 𝟚) → Cantor 
 ε = λ p → rec (p (embed zero)) (λ n → min (p (embed(succ n)))) 

 A : (Cantor → 𝟚) → 𝟚
 A = λ p → p(ε p)

\end{code}

What remains to be done, to be strictly formal, is to get a single
term, by expanding the definitions.

\begin{code}

module version₆ where

 A : ((ℕ → 𝟚) → 𝟚) → 𝟚
 A = λ p → p((λ p → rec (p (rec (λ i → ₀) (λ _ α → rec ₁ (λ i _ → α i)) zero))
    (λ n → (λ m n → cases ₀ n m) (p (rec (λ i → ₀) (λ _ α → rec ₁
    (λ i _ → α i))(succ n))))) p)

\end{code}

We can normalize this term by hand, to simplify it, using system T's
equations. Or we can ask Agda to do it, and this is what I have done
to get:

\begin{code}

module version₇ where

 A : ((ℕ → 𝟚) → 𝟚) → 𝟚
 A = λ p → p(rec(p (λ i → ₀))(λ n m → cases ₀ m (p(rec ₁ (λ i _ → rec(λ j → ₀)
     (λ _ α → rec ₁ (λ j _ → α j)) n i)))))

\end{code}

Of course, this is unreadable, and one usually writes the term as in
version₁, knowing that the definition can be mechanically translated
to this last form. Also, for proving the correctness of the program,
it is more convenient to work with version₁.

The last thing we do is to go back to version₁, and rewrite it without
using the type 𝟚, as it is not usually included in the definition of
system T.

\begin{code}

module version₈ where

 min : ℕ → ℕ → ℕ
 min zero n = zero
 min (succ m) zero = zero
 min (succ m) (succ n) = succ(min m n)

 embed : ℕ → Baire
 embed zero i = zero
 embed (succ n) zero = succ zero
 embed (succ n) (succ i) = embed n i

 ε : (Baire → ℕ) → Baire 
 ε p zero     = p (embed zero) 
 ε p (succ n) = min (ε p n) (p (embed(succ n))) 

 A : (Baire → ℕ) → ℕ
 A p = p(ε p)

\end{code}

Theorem. For all p:Baire → ℕ,

  (1) ε p is a decreasing binary sequence.
  (2) If p(ε p)=1 then p(α)=1 for all decreasing binary sequences α:Baire.

Corollary. For all p:Baire → ℕ,

  A(p) = 1 ⇔ p(α)=1 for all decreasing binary sequences α:Baire.
  A(p) = 0 ⇔ p(α)=0 for some decreasing binary sequence α:Baire.


So, what is Gödel's system T?

   (1) Simply typed lambda calculus with a base type ℕ and closed
       under function types X → Y.

   (2) Constants zero:ℕ, succ:ℕ→ℕ, and rec_X : X → (ℕ → X → X) → ℕ → X
       for each type X, subject to the equations:

            rec x f zero     = x
            rec x f (succ n) = f n (rec x f n)

   (3) Regarding the λ-calculus, all we have is λ-abstraction and
       application, and the obvious equation (λ x → t) s = t[x←s]
       using substitution of the free occurrences of x in t by the
       term s (avoiding unintended captures of the free variables of s).

       (The original version of T was based on combinatory logic with
       combinators S and K rather than the λ-calculus.)

   (4) We compute in system T applying these equations.

We can extend system T to get MLTT (Martin-Löf type theory), so that
it becomes possible to formulate and prove the theorem in the same
language we write the program. Moreover, we can define the type of
decreasing binary systems in MLTT, rather than work with them in Baire
as the host space.

In another direction, we can extend system T to a logic called HA^ω,
and the above theorem and corollary can be proved there. In both cases
(MLTT and HA^omega), we have to assume function extensionality, or
else restrict the statement of the theorem to extensional functions p.
I have proofs for both cases in MLTT, written in Agda notation.

I sketched the proof of the above in the lecture. You can find the
proof in the references given in the pdf document.

http://www.cs.bham.ac.uk/~mhe/papers/introduction-to-higher-order-computation-NLS-2017.pdf

And also in an Agda file linked from my publications page.

Friday's lecture
----------------

* We will discuss PCF rather quickly (Gödel's T with fixed-point
  recursion), and formulate two Turing universality results (due to
  Plotkin 1977 and Normann 2000) without proving them.

* Then I will discuss a dictionary relating topology and computation,
  and will transfer some theorems from topology to computation.

  The dictionary starts like this:

     continuous map ~ computable function
     open set       ~ semi-decidable set
     compact set    ~ exhaustibly searchable set
                    ⋮

  One of the theorems in topology is the countable case of Tychonoff
  theorem, which says that a product of countably many compact spaces
  is compact. It translates to: a countable product of searchable sets
  is searchable.  Using the fact that 𝟚 is (trivially) searchable, we
  get that the Cantor space is searchable.

  Another theorem in topology is that among a certain class of nice
  spaces (e.g. metrizable spaces), the compact ones are precisely the
  continuous images of the Cantor space. It translates to: a non-empty
  set is searchable iff it is a computable image of the Cantor space.

Topological "moral"
-------------------

I would like to draw your attention to two points:

(1) Intuitively, it should be possible to compute with decimal (or
    binary) notation of real numbers. But it isn't.

(2) Intuitively, it shouldn't be the case that we can exhaustibly
    search an infinite set. But it is, for many infinite sets.

Intuition doesn't quite work here! Unless you base it on topological
ideas. Which explain (1) and (2), in terms of continuity and
compactness respectively. Debug your intuition using topological
ideas!  Learn topology if you want to perform seemingly impossible
computations.

Further directions
------------------

I hope you have learned something new in these five days.

The above is the tip of the iceberg. Read the book "higher-order
computability" by Longley and Normann if you want to learn more.

An important omission in this crash-course at NLS is the definition of
topological models (of Gödel's T) and domain models (of PCF). I
planned to cover this, but simply there wasn't enough time
(unsurprisingly).
