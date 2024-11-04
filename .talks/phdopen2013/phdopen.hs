-- Martin Escardo. 
-- Some of the Haskell code for phdopen'2012, Warsaw

{-# LANGUAGE NPlusKPatterns #-}

-- Types of selection functions and quantifiers:

type J r x = (x -> r) -> x  -- Selection functions (epsilon, delta).
type K r x = (x -> r) -> r  -- Quantifiers (phi, gamma).

-- Here they are used with r = Bool
-- But in the work with Paulo Oliva we use them with r more general.

-- Type of searchable/exhaustible subsets of the type x:

type Searchable  x = J Bool x
type Exhaustible x = K Bool x

-- Transformation of selection functions into quantifiers:

overline :: J r x -> K r x
overline epsilon p = p(epsilon p)

-- Infinite product of selection functions.  Here I represent
-- sequences functions defined on the type N of natural numbers.

hd :: (N -> x) -> x
hd a = a 0

tl :: (N -> x) -> (N -> x)
tl a = \n -> a(n+1)

(#) :: x -> (N -> x) -> (N -> x) 
(x # a)    0  = x
(x # a) (n+1) = a n

prod :: (N -> J r x) -> J r (N -> x)
prod es p = x # prod(tl es) (\a -> p(x # a))                     
      where x = hd es (\x -> p(x # prod(tl es) (\a -> p(x # a))))

-- Given a sequence of selection functions on x, the algorithm
-- produces one selection function on the space of sequences on x.

-- This product algorithm works in call-by-value languages, after
-- minor syntactical adaptations. But it always evaluates the
-- variable x (which is used twice), whereas in a lazy language
-- such as Haskell, x is evaluated at most once, which
-- significantly (sometimes exponentially) reduces the number of
-- evaluation steps. But we want to be even faster.

-- The following is an arboreal version (found in Section 8 of my
-- LMCS'2008 paper "Exhaustible sets in higher-type computation",
-- and in some posts in Andrej Bauer's blog Mathematics and
-- Computation).

-- We first imagine infinite sequences (N -> x) as infinite binary
-- trees with nodes labeled by elements of x (represented in a
-- breadth-first manner, cf. the heapsort algorithm):

root :: (N -> x) -> x
root a = a 0

left :: (N -> x) -> (N -> x)
left a = \i -> a(2 * i + 1)

right :: (N -> x) -> (N -> x)
right a = \i -> a(2 * i + 2)

branch :: x -> (N -> x) -> (N -> x) -> (N -> x)
branch x u v i | i == 0    = x
               | odd i     = u((i-1) `div` 2)
               | otherwise = v((i-2) `div` 2)

-- branch-product of selection functions:

btimes :: J r x -> J r (N -> x) -> J r (N -> x) -> J r (N -> x)
(btimes ex eu ev) p = branch x0 u0 v0
  where x0 = ex(\x -> overline eu(\u -> overline ev(\v -> p(branch x u v))))
        u0 = eu(\u -> overline ev(\v -> p(branch x0 u v)))
        v0 = ev(\v -> p(branch x0 u0 v))

-- Infinite product of selection functions (arboreal version):

aprod :: (N -> J r x) -> J r (N -> x)
aprod e = btimes (root e) (aprod(left e)) (aprod(right e)) 

-- Some searchable sets of interest:

two :: Searchable N
two = \p -> if p 0 then 0 else 1

type Baire = N -> N

cantor :: Searchable Baire
cantor = aprod(\i -> two)

-- Quantification stuff.

forsome, forevery :: Searchable x -> Exhaustible x
forsome = overline
forevery s p = not(forsome s (\x -> not(p x))) 

-- Equality on a subset specified by a selection function.

equal :: Eq y => Searchable x -> (x -> y) -> (x -> y) -> Bool
equal s f g = forevery s (\a -> f a == g a) 

-- Similar:

isConstant :: Eq y => Searchable x -> (x -> y) -> Bool
isConstant s f = forevery s (\x ->forevery s (\x' -> f x == f x'))

dependsOn :: Eq y => N -> (Baire -> y) -> Bool 
dependsOn i f = forsome cantor (\a -> f a /= f (invertPosition i a))
   where invertPosition i a = \j -> if i == j then 1 - a i else a j

-- Experiments (to be followed by more code):

test1 = equal cantor f g
test2 = equal cantor f h
test3 = equal cantor g h

f,g,h,k,u,v,w :: (N -> N) -> N

f a = 10*a(3^400)+100*a(4^400)+1000*a(5^400)

g a = 10*a(3^400)+100*a(4^400)+1000*a(6^400)

h a = 10 + if a(4^400) == 1 then j+100 else j
    where i = if even(a(5^400)) then 0 else 1000
          j = if  odd(a(3^400)) then i else i-10

k a = 100 + if a(4^400) == 0 then j-100 else j 
    where i = if a(5^400) == 0 then 0 else 1000
          j = if a(3^400) == 1 then 10+i else i
  
        
u a = a(10*a(3^40)+100*a(4^40)+1000*a(5^40))

v a = a(10*a(3^40)+100*a(4^40)+1000*a(6^40))

w a = a k 
    where i = if a(5^40) == 0 then 0    else 1000
          j = if a(3^40) == 1 then 10+i else i
          k = if a(4^40) == 0 then j    else 100+j 

-- Modulus of continuity on a searchable set

modulus :: Eq y => Searchable Baire -> (Baire -> y) -> N
modulus s f = least (\n -> 
                forevery s (\a ->
                forevery s (\b -> eq n a b ==> (f a == f b))))

least :: (N -> Bool) -> N
least p = if p 0 then 0 else 1 + least(\n -> p(n+1))

(==>) :: Bool -> Bool -> Bool
False ==> p = True
True  ==> p = p

-- Equality with precision n:

eq :: Eq y => N -> (N -> y) -> (N -> y) -> Bool
eq 0 a b = True
eq (n+1) a b = eq n a b && a n == b n

-- Experiments (the computation is exponential in the modulus!):

test4 = modulus cantor (\a -> a 5)
test5 = modulus cantor (\a -> 17)

-- Contrived examples to illustrate nesting of quantifiers.

test6 :: Integer -> Bool
test6 k = 
  forevery cantor (\a ->
   forsome cantor (\b ->
         f (a 10) (a  100) (a  1000) == k - f (b  2000) (b  200) (b  20)))
    where f n2 n1 n0 = 4 * n2 + 2 * n1 + n0

test7 = 
    forevery cantor (\u ->
     forsome cantor (\v ->
      forevery cantor (\a ->
       forsome cantor (\b ->
        u  (2^333) + a  17000 == v  3000 * b (2^100)))))
    
-- Pretend (why on earth there isn't a builtin type of
-- (arbitrarily large) natural numbers in Haskell?):

type N = Integer
