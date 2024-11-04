-- Martin Escardo, 13 Feb 2008. 
--
-- Updated 20 Feb 2008 (simplification, reordering and more tests).
-- Updated 22 Feb 2008 (fixed a comment).
--
-- http://www.cs.bham.ac.uk/~mhe/papers/selection-monad.hs
--
-- I define a selection monad in the higher-type language Haskell, 
-- and explain some existing algorithms in terms of it.
-- (Cf. http://www.cs.bham.ac.uk/~mhe/papers/continuation-monad.hs)

-- Any type for the monad, but ground for countable product:
type V = Bool 

-- V-valued predicates, ranged over by p,q.
type P a = a -> V          

-- The monad action on objects, ranged over by epsilon
type S a = P a -> a 

-- A cousin, the "continuation" monad:
type Q a = P(P a)

-- A monad morphism:
forsome :: S a -> Q a
forsome epsilon p = p(epsilon p)

-- Monad structure:

-- Functor (topologically: continuous images of compact sets are
-- compact, LICS 2007 image functional):

s :: (a -> b) -> S a -> S b
s f epsilon = \q -> f(epsilon(\a -> q(f a)))

-- Unit (topologically: singletons are compact):

eta :: a -> S a
eta a = \p -> a

-- Multiplication (topologically: the union of compactly many compact
-- sets is compact):

mu :: S(S a) -> S a
mu bigepsilon p  = bigepsilon (\epsilon -> forsome epsilon p) p

-- That's it regarding the definition of the monad. 

-- Extension operator (standard):

extend :: (a -> S b) -> S a -> S b
extend f = mu.(s f)

-- The monad is strong (standard in a ccc)
-- (a product of a singleton with a compact set is compact):

strength :: (a, S b) -> S(a,b)
strength(a, epsilon) = extend(\b -> eta(a,b))(epsilon)

-- Now the LICS'2007 binary product can be defined as:

times :: (S a, S b) -> S(a,b)
times(epsa, epsb) = extend(\a -> strength(a, epsb)) epsa

-- NB. The strength is clearly not commutative, i.e.
-- the above "times" is one of two distinct symmetric possibilities.
-- The definition of prod below works with this "times" but not
-- with the other. (It diverges with the other.)

-- Now the LICS'2007 countable product functional can be defined as

type N = Integer
type Omega a = N -> a

cons :: (a, Omega a) -> Omega a
cons(a,alpha) = \i -> if i == 0 then a else alpha(i-1)

hd :: Omega a -> a
hd alpha = alpha 0

tl :: Omega a -> Omega a
tl alpha = \i -> alpha(i+1)

constimes :: (S a, S(Omega a)) -> S(Omega a)
constimes = (s cons).times

-- prod could be called timesOmega instead:

prod :: Omega(S a) -> S(Omega a)
prod epsilons = constimes(hd epsilons, prod(tl epsilons))

-- So prod satisfies: prod.cons = constimes.(id x prod)
-- i.e. prod(cons(epsilon,epsilons))=constimes(epsilon,prod epsilons)
--
-- Intuitively:
--
--   prod(eps0 eps1 eps2 ...) = 
--         constimes(eps0, constimes(eps1, constimes(eps2,...)...))
--

-- Now I want to test the above product functional for efficiency.

selectBool :: S Bool
selectBool p = p True

type Cantor = Omega Bool

selectCantor :: S Cantor
selectCantor = prod(\i -> selectBool)

forsomeC, foreveryC :: Q Cantor
forsomeC = forsome selectCantor
foreveryC p = not(forsomeC(not.p))

equal :: Eq y => (Cantor -> y) -> (Cantor -> y) -> Bool
equal f g = foreveryC(\a -> f a == g a)

f a = a(12 + a' 0 + a' 1 + a' 2 + a' 3 + a' 5 + a' 6 + a' 7 + a' 8 + a' 9)
   where a' i = if a i then 1 else 0

g a = a(12 + a' 0 + a' 1 + a' 2 + a' 3 + a' 5 + a' 6 + a' 7 + a' 8 + a' 10)
   where a' i = if a i then 1 else 0

-- Result of test (1.7 GHz Dell D410 laptop):
--
--    *Main> equal f g
--    False
--    (0.54 secs, 26199820 bytes)
--    *Main> equal f f
--    True
--    (0.17 secs, 7919020 bytes)
--    *Main> equal g g
--    True
--    (0.18 secs, 7921160 bytes)
--
-- A harder test:


ff a = a(a' 111 + a' 222 + a' 333 + a' 444 + a' 555)
   where a' i = if a i then 1 else 0

gg a = a(a' 111 + a' 222 + a' 333 + a' 444 + a' 556)
   where a' i = if a i then 1 else 0

-- Result of harder test:
--
--   *Main> equal ff gg
--   False
--   (14.37 secs, 639479176 bytes)
--   *Main> equal ff ff
--   True
--   (7.45 secs, 339209276 bytes)
--   *Main> equal gg gg
--   True
--   (7.44 secs, 339871288 bytes)

-- Now let's do the tree-like algorithm categorically.
-- (The one in the submitted journal version of LICS'2007.)

type Tree a = Omega a

branch :: (a, Tree a, Tree a) -> Tree a
branch (x,l,r) = \n -> if n == 0 then x
                  else if odd n  then l ((n-1) `div` 2)
                                 else r ((n-2) `div` 2)

root :: Tree a -> a
root  t = t 0

left, right :: Tree a -> Tree a
left  t = \n -> t(2 * n + 1)
right t = \n -> t(2 * n + 2)

times3 :: (S a, S b, S c) -> S(a,b,c)
times3 (epsa, epsb, epsc) = s iso (times(epsa, times(epsb, epsc)))
     where iso (a,(b,c)) = (a,b,c)

branchtimes :: (S a, S(Tree a), S(Tree a)) -> S(Tree a)
branchtimes = (s branch).times3

tprod :: Tree(S a) -> S(Tree a)
tprod epsilons = branchtimes(root epsilons, 
                             tprod(left epsilons), 
                             tprod(right epsilons))

-- Let's test this for efficiency:

tselectCantor :: S Cantor
tselectCantor = tprod (\i -> selectBool)

tforsomeC, tforeveryC :: Q Cantor
tforsomeC = forsome tselectCantor
tforeveryC p = not(tforsomeC(not.p))

tequal :: Eq y => (Cantor -> y) -> (Cantor -> y) -> Bool
tequal f g = tforeveryC(\a -> f a == g a)

-- Results of the tests:
--
--   *Main> tequal ff gg
--   False
--   (0.24 secs, 13593092 bytes)
--   *Main> tequal ff ff
--   True
--   (0.22 secs, 11885844 bytes)
--   *Main> tequal gg gg
--   True
--   (0.35 secs, 18620596 bytes)
--   *Main> 

-- To do: proper/perfect maps.

-- Variation.

times3' :: (S a, S b, S c) -> S(a,b,c)
times3' (epsa, epsb, epsc) = s iso (times(times(epsa, epsb), epsc))
     where iso ((a,b),c) = (a,b,c)


branchtimes' :: (S a, S(Tree a), S(Tree a)) -> S(Tree a)
branchtimes' = (s branch).times3'

tprod' :: Tree(S a) -> S(Tree a)
tprod' epsilons = branchtimes'(root epsilons, 
                               tprod'(left epsilons), 
                               tprod'(right epsilons))

tselectCantor' :: S Cantor
tselectCantor' = tprod'(\i -> selectBool)

tforsomeC', tforeveryC' :: Q Cantor
tforsomeC' = forsome tselectCantor'
tforeveryC' p = not(tforsomeC'(not.p))

tequal' :: Eq y => (Cantor -> y) -> (Cantor -> y) -> Bool
tequal' f g = tforeveryC'(\a -> f a == g a)

-- What follows here is tentative:
-- A finite coproduct of compact spaces is compact. 

data Sum a b = Inl a | Inr b

data One = One

data Two = Sum One One

selectOne :: S One
selectOne p = One

-- Here we use the fact that V=Bool. Can we avoid that?

plus :: (S a, S b) -> S (Sum a b)
plus(epsilona, epsilonb) = \p -> if forsome (s Inl epsilona) p 
                                 then s Inl epsilona p 
                                 else s Inr epsilonb p

-- Maybe can do better:
plus' :: (a, S b) -> S (Sum a b)
plus'(a, epsilon) = \p -> if p (Inl a)
                          then Inl a
                          else s Inr epsilon p

plus'':: (S a, S b) -> S (Sum a b)
plus''(epsa, epsb) = extend(\a -> plus'(a, epsb)) epsa

-- Countable sums won't work, but their 
-- one-point compactification do:

data OmegaSum a = Zero a | Succ (OmegaSum a)

-- The infinite stack of Succ's is the point an infinity:

plu :: (S a, S(OmegaSum a)) -> S(OmegaSum a)
plu(epsilon, bigepsilon) = \p -> if forsome (s Zero epsilon) p 
                                 then s Zero epsilon  p 
                                 else s Succ bigepsilon p

summ :: Omega(S a) -> S(OmegaSum a)
summ epsilons = plu(hd epsilons, summ(tl epsilons))

-- Example: the one-point compactification of the natural numbers 
-- is searchable.

type OnePtCompN = OmegaSum One

selectOnePtCompN :: S OnePtCompN
selectOnePtCompN = summ(\i -> selectOne)

-- But there are more complicated examples, e.g.
-- the sequence, index by n, of n-bounded sequences in the Baire space.


-- Are there bigger, computationally accessible, compactifications
-- one can define in general? 
-- Yes, surely, consider e.g.

data ContinuumSum a = Z a | Left (ContinuumSum a) | Right(ContinuumSum a)

-- I'll develop this another day. 


