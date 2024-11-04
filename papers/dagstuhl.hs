-------------------------------------------------------------------
--                                                               --
-- Fast exhaustive search over infinite search spaces.           --
--                                                               --
-- This file contains most of the Haskell program fragments      --
-- discussed in the Dagstuhl seminar 06341, 20-25 Aug 2006,      --
-- by Martin Escardo.                                            --
--                                                               --
-- I'll include a pointer to the slides after the talk is given. --
-- This program may make little sense without them!              --
--                                                               --
-------------------------------------------------------------------

type N = Integer

-- Realizers for exhaustively searchable subspaces:

type Subspace x = (x -> Bool) -> x

-- Basic examples.
--
-- Realizers for exhaustive searchability are named after
-- the subspaces they search over:

bool :: Subspace Bool
bit  :: Subspace N
z    :: N -> Subspace N

bool = \p -> p True
bit  = \p -> if p 0 then 0 else 1

z 0 = undefined
z 1 = \p -> 0
z n = \p -> if p (n-1) then n-1 else z(n-1) p

-- Boolean-valued quantifiers:

exists, forall :: Subspace x -> (x -> Bool) -> Bool
exists s p = p(s p)
forall s p = not(exists s(\x -> not(p x)))

-- Function equality on subspaces:

equal :: Eq y => Subspace x -> (x -> y) -> (x -> y) -> Bool
equal s f g = forall s(\x -> f x == g x)

-- Example factory of exhaustively searchable subspaces:

image :: (x -> y) -> Subspace x -> Subspace y
image f s = \q -> f(s(q.f))

times :: Subspace x -> Subspace y -> Subspace(x,y)
(s `times` t) p = (a,b)
                where a = s(\x -> p(x,t(\y -> p(x,y))))
                      b = t(\y -> p(a,y))

prod :: (N -> Subspace x) -> Subspace (N -> x)
prod e p = b
  where b = id'(\n->e n (\x->q x n(prod(\i->e(i+n+1))(q x n))))
        q x n a = p(\i -> if i  < n then b i
                     else if i == n then x
                                    else a(i-n-1))

-- More interesting examples of exhaustively searchable subspaces:

cantor :: Subspace (N -> Bool)
cantor = prod(\i -> bool)

bcantor, tcantor, qcantor :: Subspace (N -> N)
bcantor = prod(\i -> bit)
tcantor = prod(\i -> z 3)
qcantor = prod(\i -> z 4)

factorial :: Subspace (N -> N)
factorial = prod(\i -> z(i+1))

-- Function memoization.
-- Amounts to convoluted implementation of the identity.
-- Adds logarithmic time overhead.

data T x = B x (T x) (T x)

code :: (N -> x) -> T x
code f = B (f 0) (code(\n -> f(2*n+1))) 
                 (code(\n -> f(2*n+2)))

decode :: T x -> (N -> x)
decode (B x l r) n |  n == 0    = x
                   |  odd n     = decode l ((n-1) `div` 2)
                   |  otherwise = decode r ((n-2) `div` 2)

id' :: (N -> a) -> (N -> a)
id' = decode.code

-- Concluding examples.
-- Much slower if we instead set id' = id.
-- But still can compare the following functions.

f,g,h :: (N -> N) -> N

f a = 10*a(3^400)+100*a(4^400)+1000*a(5^400)

g a = 10*a(3^400)+100*a(4^400)+1000*a(6^400)

h a = 10 + if a(4^400) == 1 then j+100 else j
    where i = if even(a(5^400)) then 0 else 1000
          j = if  odd(a(3^400)) then i else i-10

hh a = 100 + if a(4^400) == 0 then j-100 else j 
    where i = if a(5^400) == 0 then 0 else 1000
          j = if a(3^400) == 1 then 10+i else i
  
false0 = equal bcantor f g
true0  = equal bcantor f h


-- More:

f',g',h' :: (N -> N) -> N

        
f' a = a(10*a(3^40)+100*a(4^40)+1000*a(5^40))

g' a = a(10*a(3^40)+100*a(4^40)+1000*a(6^40))

h' a = a k 
    where i = if a(5^40) == 0 then 0    else 1000
          j = if a(3^40) == 1 then 10+i else i
          k = if a(4^40) == 0 then j    else 100+j 

false1 = equal bcantor f g
true1  = equal bcantor f h



false2 = exists bcantor (\a->a(5^500)+a(6^600)+a(7^700)+a(8^800)+a(9^900)>=4^400)

false3 = exists tcantor (\a->a(5^500)+a(6^600)+a(7^700)+a(8^800)+a(9^900)>=4^400)

false5 = exists tcantor (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) > 2^5)

w = [a(5^500),a(6^600),a(7^700),a(8^800),a(9^900)]
  where a = tcantor (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) == 2^3)

w' = [a(5^500),a(6^600),a(7^700),a(8^800),a(9^900)]
  where a = qcantor (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) == 2*3)

-- This is too slow, of course:

w'' = [a(5^500),a(6^600),a(7^700),a(8^800),a(9^900)]
  where a = factorial (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) == 2*3*5*7)


-- But this is ok:

example = [a 2, a 3, a 4, a 5]
  where a = factorial (\a->a 2 * a 3 * a 4 * a 5== 2*2*3*4)


-- Set equality.

proj :: N -> (N -> Bool) -> Bool
proj n = \a -> a n

eqnat :: N -> N -> Bool
eqnat m n = equal cantor (proj m) (proj n)

projset :: [N] -> ((N -> Bool) -> Bool)
projset [] = \a -> True
projset (n:l) = \a -> (a n) && (projset l a)

eqset :: [N] -> [N] -> Bool
eqset k l = equal cantor (projset k) (projset l)

-- End of file.
