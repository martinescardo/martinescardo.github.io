-- Haskell implementation of abstract data type for MAP'2011. Martin Escardo.
-- Based on joit work with Alex Simpson.

type I = [Int]  -- Represents [-1,1] in binary using digits -1,0,1.

minusOne, one :: I
minusOne  = repeat (-1)
one       = repeat 1

type J = [Int]  -- Represents [-n,n] using digits |d| < n, for any n.

divideBy :: Int -> J -> I
divideBy n (a:b:x) = let d = 2*a+b
  in if      d < -n then -1 : divideBy n (d+2*n:x)
     else if d >  n then  1 : divideBy n (d-2*n:x)
                    else  0 : divideBy n (d:x)               

mid :: I -> I -> I
mid x y = divideBy 2 (zipWith (+) x y)

bigMid :: [I] -> I 
bigMid = (divideBy 4).bigMid'
 where bigMid'((a:b:x):(c:y):zs) = 2*a+b+c : bigMid'((mid x y):zs)

affine :: I -> I -> I -> I
affine a b x = bigMid [h d | d <- x]
  where h (-1) = a
        h   0  = mid a b
        h   1  = b

-- Use the term algebra of M.

data I' = MinusOne | One | M [I']

affine' :: I' -> I' -> I' -> I'
affine' x y = h
 where h MinusOne = x
       h One      = y
       h (M zs)   = M [h z | z <- zs] 

-- Translations

zero :: I'
zero = M(MinusOne : repeat One)

inclusion :: I -> I'
inclusion x = M [h d | d <- x]
 where h (-1) = MinusOne
       h   0  = zero
       h   1  = One
 
eval :: I' -> I
eval MinusOne = minusOne
eval One      = one
eval (M xs)   = bigMid [eval x | x <- xs]


