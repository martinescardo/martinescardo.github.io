-- File experimental set-up for LMCS journal version of LICS'2007 paper

type N = Integer
type Cantor = N -> Bool

type Searcher d = (d -> Bool) -> d
type Quantifier d = (d -> Bool) -> Bool

-- The three product functionals developed in the paper:

prod, prod', prod'' :: (N -> Searcher d) -> Searcher(N -> d)

prod e p n = e n (\x->q n x(prod(\i->e(i+n+1))(q n x)))
 where q n x a = p(\i -> if i  < n then prod e p i
                    else if i == n then x
                                   else a(i-n-1))


(x # a)(i) = if i == 0 then x else a(i-1)
tl a = \i -> a(i+1) 

prod' e p = x#(prod'(tl e)(\a->p(x#a))) 
 where x = e 0(\x->p(x#(prod'(tl e)(\a->p(x#a)))))


branch x l r n = if n == 0 then x
            else if odd n  then l ((n-1) `div` 2)
                           else r ((n-2) `div` 2)

root  t = t 0
left  t = \n -> t(2 * n + 1)
right t = \n -> t(2 * n + 2)

prod'' t p = branch x l r
 where findx = root t
       findl = prod''(left t)
       findr = prod''(right t)
       forsomel p = p(findl p)
       forsomer p = p(findr p)
       x = findx(\x -> forsomel(\l -> forsomer(\r -> p(branch x l r))))
       l = findl(\l -> forsomer(\r -> p(branch x l r)))
       r = findr(\r -> p(branch x l r))

-- Berger's functional and an immediate variation:

berger, berger' :: Searcher Cantor

berger p = if p(True  # berger(\a -> p(True  # a)))
           then True  # berger(\a -> p(True  # a))
           else False # berger(\a -> p(False # a))

berger' p = if p l then l else r
 where l = True  # berger'(\a -> p(True  # a))
       r = False # berger'(\a -> p(False # a))

-- Some search operators

findbool :: Searcher Bool
findbool p = p True

-- The version of the chosen algorithm is ranged over by v

type Version = Int 

-- We have five versions of search operators for the Cantor space

find :: Version -> Searcher Cantor

find 0 = berger
find 1 = berger'
find 2 = prod  (\i -> findbool) 
find 3 = prod' (\i -> findbool) 
find 4 = prod''(\i -> findbool) 

-- Again five versions of each quantifier:

forsome, forevery :: Version -> Quantifier Cantor

forsome n p = p(find n p)
forevery v p = not(forsome v (not.p))

-- Function equality again comes in five versions

equal :: Eq y => Version -> (Cantor -> y) -> (Cantor -> y) -> Bool
equal v f g = forevery v(\x -> f x == g x)

-- Experiment 0

coerce :: Bool -> N
coerce x = if x then 1 else 0

u,v,w :: Cantor -> Bool

        
u a = a(19*a'(2^20)+399*a'(5^20)+9177*a'(3^20)) 
 where a' i = coerce(a i)

v a = a(19*a'(2^20)+399*a'(6^20)+9177*a'(3^20))
 where a' i = coerce(a i)

w a = a k 
 where i = if a(3^20) then 483 else 0
       j = 19 * if a(2^20) then 1+i else i
       k = j + 19 * if a(5^20) then 21 else 0 

-- More experiments (five versions of each)
-- They are not in the same order as in the journal paper. 

-- Experiment 1

-- nth projection

proj :: N -> (Cantor -> Bool)
proj n = \a -> a n

experiment1 :: Version -> N -> Bool
experiment1 v n = forsome v (proj n)

-- Experiment 1'

experiment1' :: Version -> N -> Bool
experiment1' v n = forevery v (proj n)

-- Experiment 2

projlist :: [N] -> (Cantor -> Bool)
projlist [] = \a -> True
projlist (n:l) = \a -> (a n) && (projlist l a)

experiment2 :: Version -> [N] -> Bool
experiment2 v l = forsome v (projlist l)

-- Experiment 3

experiment3 :: Version -> [N] -> Bool
experiment3 v l = forevery v (projlist l)


-- Experiment 4 (changes number of uses)

experiment4 v l n = experiment3 v (take (n * length l) l')
 where l' = l ++ l'

-- Experiment 4' (changes number of uses)

experiment4' v l n = experiment2 v (take (n * length l) l')
 where l' = l ++ l'

-- Experiment 5

experiment5 :: Version -> [N] -> N -> Bool
experiment5 v l n = forsome v (projlist (map (*n) l))


-- Experiment 6

experiment6 :: Version -> [N] -> [N] -> Bool
experiment6 v l m = equal v (projlist l) (projlist m)

-- Experiment 6'

experiment6' v l = experiment6 v l l -- (l++[0])

-- Experiment7 

experiment7 v l = experiment6 v l (reverse l)


-- main = print(equal 4 u w)

