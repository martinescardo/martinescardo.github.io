Martin Escardo, 31 May 2013.

This is a set of exercises for PhD students at Warsaw University, who
know both topology and Haskell (a rare combination).

In this set of exercises, I ask you to generalize Berger's algorithm,
and other algorithms.

Let's first write a different version of Berger's algorithm for search
over the Cantor space.

> {-# LANGUAGE NPlusKPatterns #-}

> type N = Integer
> type Baire = N -> N

The Baire space is the type of sequences of natural numbers.

The Cantor space is the subset of binary sequences with values 0 and 1. 

> hd :: Baire -> N
> hd a = a 0

> tl :: Baire -> Baire
> tl a = \i -> a(i+1) 

> (#) :: N -> Baire -> Baire
> (n # a)    0  = n
> (n # a) (i+1) = a i

We have 
            hd(x # a) = x 
            tl(x # a) = a 
           (hd a) # (tl a) = a


> findCantor    :: (Baire -> Bool) -> Baire
> forsomeCantor :: (Baire -> Bool) -> Bool

> forsomeCantor p = p(findCantor p)

> findCantor p = if forsomeCantor(\a -> p(0 # a))
>                then 0 # findCantor(\a -> p(0 # a))
>                else 1 # findCantor(\a -> p(1 # a))                    

These functions search and quantify over the Cantor space. 

Q1. Topological exercise.

The Baire space has many other searchable subsets.

We know from the course that searchable sets must be compact. So let's
look at the compact subsets of Baire. Because Baire is Hausdorff, the
compact subsets are closed. Recall that we topologize Baire as
follows: We take the discrete topology on N, and the product topology
on N^N = Baire.

Q1(a) Argue that the compact subsets of Baire are precisely the closed
and bounded subsets, where we work with the pointwise order on
sequences to define boundedness.

Q1(b) Consider finitely branching trees in which each edge is labeled
by a natural number. There are no leaves: the trees are
non-well-founded and we are interested in the infinite paths starting
from the root. For example, the Cantor tree is the full binary tree
with edges labeled 0 on the left and 1 on the right. The paths are the
binary sequences.

Given such a tree, argue that its set of paths forms a compact subset
of Baire.

Q1(c) Conversely, argue that any compact subset arises as the set of
paths of such a tree.


Q2. Programming exercises.

Define in Haskell the type of finitely branching trees as follows:

> data T = Fork [(N,T)]

We consider two restrictions for the lists in the above definition:
(i) they must be nonempty (so that all paths are infinite), and (ii)
they must be finite, so that we get finitely branching trees as
discussed in the previous exercise. These conditions cannot be imposed
in Haskell (they can be imposed and verified in laguages with
dependent types such as e.g. Agda). Here we only promise to produce
correct outputs for correct trees, where the correctness is proved
externally to Haskell. Again, in dependently typed languages one can
prove the correctness in the languages themselves.

For example, the Cantor tree can be defined as follows:

> cantorTree :: T
> cantorTree = Fork [(0, cantorTree), (1, cantorTree)]

A more complicated family of finitely branching tree is this:

> unboundedBreadthTree :: N -> T
> unboundedBreadthTree n = Fork [(i, unboundedBreadthTree(n+1)) | i <- [0..n]]

Although the breadth is unbounded, the set of paths of
unboundedBreadthTree n is bounded by the infinite sequence n,n+1,n+2,
..., that is, the sequence \i -> n+i.

Q2(a) Define a generalization findT of Berger's algorithm to search
the paths of a finitely branching tree:

> findT    :: T -> (Baire -> Bool) -> Baire
> forsomeT :: T -> (Baire -> Bool) -> Bool

> forsomeT t p = p(findT t p)

> findT t p = undefined

You are supposed use the same idea as in Berger's algotithm. Any new
ideas should be reported in Q4 below.

Q2(b) We have seen that Berger's algorithm run-time is exponential in
the modulus of uniform continuity of p. We discussed the following
faster algorithm:

> findBit :: (N -> Bool) -> N
> findBit p = if p 0 then 0 else 1

> findCantor'    :: (Baire -> Bool) -> Baire
> forsomeCantor' :: (Baire -> Bool) -> Bool

> forsomeCantor' p = p(findCantor' p)

> findCantor' p = x # a 
>   where x = findBit(\x -> forsomeCantor'(\a -> p(x # a)))
>         a = findCantor'(\a -> p(x # a)) 

This is exponential in the cardinality of the indices of a that the
computation of p(a) potentially uses for an arbitrary a, and linear in
the largest index.

Define corresponding version:

> findT'    :: T -> (Baire -> Bool) -> Baire
> forsomeT' :: T -> (Baire -> Bool) -> Bool

> forsomeT' t p = p(findT' t p)

> findT' t p = undefined

Again, you are supposed the same idea as in the given algotithm. Any
new ideas should be reports in Q4 below.

Q2(c). There is also the "arboreal" algorithm for searching the Cantor
space, which reduces the above linear factor to its logarithm:

> fork :: N -> Baire -> Baire -> Baire
> fork x l r i   | i == 0    = x
>                | odd i     = l((i-1) `div` 2)
>                | otherwise = r((i-2) `div` 2)

> findCantor''    :: (Baire -> Bool) -> Baire
> forsomeCantor'' :: (Baire -> Bool) -> Bool

> forsomeCantor'' p = p(findCantor'' p)

> findCantor'' p = fork x l r 
>  where x = findBit(\x -> forsomeCantor''(\l -> forsomeCantor''(\r -> p(fork x l r))))
>        l = findCantor''(\l -> forsomeCantor''(\r -> p(fork x l r)))
>        r = findCantor''(\r -> p(fork x l r))

Generalize the arboreal algorithm to search the set of paths of any
finitely branching tree:

> findCantorT''    :: T -> (Baire -> Bool) -> Baire
> forsomeCantorT'' :: T -> (Baire -> Bool) -> Bool

> forsomeCantorT'' t p = p(findCantorT'' t p)

> findCantorT'' t p = undefined


Q3. It turns out that if epsilon : (Baire -> Bool) -> Baire is a
search operator for some undisclosed compact subset K of Baire, one
can reconstruct a finitely branching tree whose paths are the elements
of K. Write such an algorithm:

> undisclose :: ((Baire -> Bool) -> Baire) -> T
> undisclose epsilon = undefined

Hints. In the lectures, we wrote together such an undisclose function

  ((N->Bool)->N) -> [N] 

for subsets of N. This is in the file search.hs. You will need to use
this. Moreover, you may find it useful to use the fact that computable
images of searchable sets are searchable. In particular, there is a map 

  image :: (Baire -> N) -> ((Baire -> Bool) -> Baire) -> ((N->Bool)->N)
that can be used to compute the image of K under the projection 

  pi :: Baire -> N 

defined by pi a = a i.

Q4. Bonus, open ended, research question. (a) Can you find your own
better algorithms, in any suitable sense of "better"? (b) Can you
identify a particular set of predicates p:Baire->Bool which (b1) would
be both potentially useful for applications, and for which (b2) search
can be done in polynomial time?
