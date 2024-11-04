-------------------------------------------------------------------
--                                                               --
-- Infinite sets that admit fast exhaustive search               --
--                                                               --
-- Companion Haskell program for the paper with same title.      --
--                                                               --
-- Martin Escardo, Summer 2006.                                  --
--                                                               --
-- This will be rewritten to perfectly match the paper           --
--                                                               --
-------------------------------------------------------------------

type N = Integer
type Bit = Int
type Cantor = N -> Bit

-- Realizers for exhaustively searchable sets:

type Searcher d = (d -> Bool) -> d

-- Universal and existential quantifiers:

type Quantifier d = (d -> Bool) -> Bool

-- Basic examples.
--
-- Realizers for searchability are named after
-- the sets they search over:

bool :: Searcher Bool
bit  :: Searcher N
z    :: N -> Searcher N
l    :: [N] -> Searcher N

bool = \p -> p True
bit  = \p -> if p 0 then 0 else 1

z 0 = undefined
z 1 = \p -> 0
z n = \p -> if p (n-1) then n-1 else z(n-1) p

l [] = undefined
l [a] = \p -> a
l (a:s) = \p -> if p a then a else l s p

-- Boolean-valued quantifiers:

forsome, forevery :: Searcher d -> Quantifier d
forsome s p = p(s p)
forevery s p = not(forsome s(\x -> not(p x)))

-- Function equality:

equal :: Eq e => Searcher d -> (d -> e) -> (d -> e) -> Bool
equal s f g = forevery s(\x -> f x == g x)

-- Factory of exhaustively searchable sets:

image :: (d -> e) -> Searcher d -> Searcher e
image f s = \q -> f(s(\x -> q(f x)))

times :: Searcher d -> Searcher d' -> Searcher(d,d')
(s `times` s') p = (x,x')
     where x = s (\x -> forsome s'(\x' -> p(x,x')))
           x'= s'(\x'-> p(x,x'))


-- Without memoization (the name doesn't match the paper):

prod' :: (N -> Searcher d) -> Searcher(N -> d)
prod' e p n = e n (\x->q n x(prod'(\i->e(i+n+1))(q n x)))
  where q n x a = p(\i -> if i  < n then prod' e p i
                     else if i == n then x
                                    else a(i-n-1))

-- With:

prod :: (N -> Searcher d) -> Searcher(N -> d)
prod e p = b
  where b = id'(\n->e n (\x->q n x(prod(\i->e(i+n+1))(q n x))))
        q n x a = p(\i -> if i  < n then b i
                     else if i == n then x
                                    else a(i-n-1))

-- More interesting examples of exhaustively searchable subspaces:

bcantor :: Searcher (N -> Bool)
bcantor = prod(\i -> bool)

cantor, tcantor, qcantor :: Searcher (N -> N)
cantor = prod(\i -> bit)
tcantor = prod(\i -> z 3)
qcantor = prod(\i -> z 4)

factorial :: Searcher (N -> N)
factorial = prod(\i -> z(i+1))

cantorw :: Searcher(N -> N -> Bool)
cantorw = prod(\i -> bcantor)

-- Function memoization.
-- Amounts to convoluted implementation of the identity.
-- Adds logarithmic time overhead, but avoids re-evaluation.

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

-- Modulus of continuity on the Cantor space.

fan :: Eq y => ((N -> Bool) -> y) -> N
fan f = mu(\n->foreveryC(\a->foreveryC(\b->eq n a b ==> (f a == f b))))

mu :: (N -> Bool) -> N
mu p = if p 0 then 0 else 1 + mu(p.(1+))

foreveryC = forevery bcantor
foreveryZ n = forevery (z(n+1))

False==>p=True
True ==>p=p

eq n a b = foreveryZ n(\i -> a i == b i)

-- Another product functional

(x # a)(i) = if i == 0 then x else a(i-1)
tl a = \i -> a(i+1) 

prod'' e p = 
  let x = e 0(\x->p(x#(prod''(tl e)(\a->p(x#a)))))
  in x#(prod''(tl e)(\a->p(x#a)))

-- berger

berger :: (Cantor  -> Bool) -> Cantor
berger p = if p(0 # berger(\a -> p(0 # a)))
           then 0 # berger(\a -> p(0 # a))
           else 1 # berger(\a -> p(1 # a))


-- Set equality.

proj :: N -> (N -> Bool) -> Bool
proj n = \a -> a n

eqnat :: N -> N -> Bool
eqnat m n = equal bcantor (proj m) (proj n)

projset :: [N] -> ((N -> Bool) -> Bool)
projset [] = \a -> True
projset (n:l) = \a -> (a n) && (projset l a)

eqset :: [N] -> [N] -> Bool
eqset k l = equal bcantor (projset k) (projset l)

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
  
-- More:

f',g',h' :: (N -> N) -> N

        
f' a = a(10*a(3^80)+100*a(4^80)+1000*a(5^80))

g' a = a(10*a(3^80)+100*a(4^80)+1000*a(6^80))

h' a = a k 
    where i = if a(5^80) == 0 then 0    else 1000
          j = if a(3^80) == 1 then 10+i else i
          k = if a(4^80) == 0 then j    else 100+j 

false2 = forsome cantor (\a->a(5^500)+a(6^600)+a(7^700)+a(8^800)+a(9^900)>=4^400)

false3 = forsome tcantor (\a->a(5^500)+a(6^600)+a(7^700)+a(8^800)+a(9^900)>=4^400)

false5 = forsome tcantor (\a->a(5^500)*a(6^600)*a(7^700)*a(8^800)*a(9^900) > 2^5)

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


-- End of file.
