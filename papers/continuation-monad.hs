-- Martin Escardo, 18 Feb 2008.
--
-- I do the same as I did for the selection monad on 15 Feb,
-- with the continuation monad. 
-- As I suspected, the countable product functional doesn't converge.

type V = Bool
type O a = a -> V          -- ranged over by p,q,r
type S a = O a -> V        -- ranged over by phi, gamma

s :: (a -> b) -> S a -> S b
s f phi = \p -> phi(p.f)

eta :: a -> S a
eta a = \p -> p a

box :: O a -> O(S a)
box p = \phi -> phi p

mu :: S(S a) -> S a
mu bigphi = bigphi.box

extend :: (a -> S b) -> S a -> S b
extend f = mu.(s f)

strength :: (a, S b) -> S(a,b)
strength(a, phi) = \p -> phi(\b -> p(a,b))

times :: (S a, S b) -> S(a,b)
times(phia, phib) = extend(\a -> strength(a, phib)) phia

type N = Integer
type Omega a = N -> a

mul :: (S a,S(Omega a)) -> S(Omega a)
mul = (s cons).times

prod :: Omega(S a) -> S(Omega a)
prod phis = mul(hd phis, prod(tl phis))

cons :: (a,Omega a) -> Omega a
cons(a,alpha) = \i -> if i == 0 then a else alpha(i-1)

hd :: Omega a -> a
hd alpha = alpha 0

tl :: Omega a -> Omega a
tl alpha = \i -> alpha(i+1)


foreveryBool, forsomeBool :: S Bool
foreveryBool p = p True && p False
forsomeBool p = p True || p False

type Cantor = Omega Bool

foreveryCantor, forsomeCantor :: S Cantor
foreveryCantor = prod (\i -> foreveryBool)
forsomeCantor = prod (\i -> forsomeBool)

equal :: Eq y => (Cantor -> y) -> (Cantor -> y) -> Bool
equal f g = foreveryCantor(\a -> f a == g a)

f a = a(12 + a' 0 + a' 1 + a' 2 + a' 3 + a' 5 + a' 6 + a' 7 + a' 8 + a' 9)
   where a' i = if a i then 1 else 0

g a = a(12 + a' 0 + a' 1 + a' 2 + a' 3 + a' 5 + a' 6 + a' 7 + a' 8 + a' 10)
   where a' i = if a i then 1 else 0

-- It seems to be equally efficient (compared to the corresponding one)

-- Now let's do the tree-like algorithm categorically:

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
times3 (phia, phib, phic) = s iso(times(phia, times(phib, phic)))
     where iso (a,(b,c)) = (a,b,c)


branchmul :: (S a, S(Tree a), S(Tree a)) -> S(Tree a)
branchmul = (s branch).times3

tprod :: Tree(S a) -> S(Tree a)
tprod phis = branchmul(root phis, 
                           tprod(left phis), 
                           tprod(right phis))

-- Let's test this for efficiency:

tforeveryCantor, tforsomeCantor :: S Cantor
tforeveryCantor = tprod (\i -> foreveryBool)
tforsomeCantor = tprod (\i -> forsomeBool)

tequal :: Eq y => (Cantor -> y) -> (Cantor -> y) -> Bool
tequal f g = tforeveryCantor(\a -> f a == g a)

ff a = a(a' 111 + a' 222 + a' 333 + a' 444 + a' 555)
   where a' i = if a i then 1 else 0

gg a = a(a' 111 + a' 222 + a' 333 + a' 444 + a' 556)
   where a' i = if a i then 1 else 0

main = print(equal ff gg)

