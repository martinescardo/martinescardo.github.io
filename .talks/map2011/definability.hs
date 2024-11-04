-- Haskell implementation of abstract data type for MAP'2011. Martin Escardo.
-- Based on joit work with Alex Simpson.

type N = Int

-- Types of interval spaces [-1,1], [-2,2], [-4,4], and [-n,n]:

type I  = [Digit]  -- uses digits         -1,0,1   
type I2 = [Digit]  -- uses digits       2,-1,0,1,2
type I4 = [Digit]  -- uses digits 4,-3,-2,-1,0,1,2,3,4
type In = [Digit]  -- uses digits |d| < n  

minusOne, one :: I
minusOne  = repeat (-1)
zero      = repeat 0
one       = repeat 1

type Digit = Int

-- The following is a representation conversion.
-- No optimizations are considered here (see Fun'2011).

divideBy :: Int -> In -> I
divideBy n (a:b:x) = 
  let d = 2 * a + b
  in if      d < -n then -1 : divideBy n (d+2*n:x)
     else if d >  n then  1 : divideBy n (d-2*n:x)
                    else  0 : divideBy n (d:x)               

-- Addition as a function [-1,1] x [-1,1] -> [-2,2]:

add2 :: I -> I -> I2
add2 = zipWith (+)

-- Midpoint (x+y)/2 as a function [-1,1] x [-1,1] -> [-1,1]:

mid :: I -> I -> I
mid x y = divideBy 2 (add2 x y)

-- Infinitely interated midpoint:

bigMid :: [I] -> I 
bigMid = (divideBy 4).bigMid'
 where bigMid'((a:b:x):(c:y):zs) = 2*a + b + c : bigMid'((mid x y):zs)

-- Affine maps:

affine :: I -> I -> I -> I
affine a b x = bigMid [h d | d <- x]
  where h (-1) = a
        h   0  = mid a b
        h   1  = b

-------------------------------- E N D -----------------------------
--------------------------------------------------------------------
-- This implements our four system T+I primitive constants -1, 1, --
-- affine and M.                                                  --
--------------------------------------------------------------------
--------------------------------------------------------------------

-- Some examples follow (representation independent):

-- Complement:

compl :: I -> I
compl = affine one minusOne

-- Multiplication:

mul :: I -> I -> I
mul x = affine (compl x) x

sqr :: I -> I
sqr x = mul x x

-- Rational numbers:
--
-- The function is total, but gives garbage if the inputs are garbage.

rational :: Int -> N -> I
rational m n = bigMid(f m)
 where f m   | 2 * m < -n = minusOne : f(2*m + n) 
             | 2 * m >  n = one      : f(2*m - n) 
             | otherwise  = zero     : f(2*m)

divByInt :: I -> Int -> I
divByInt x n = mul x (rational 1 n)


-- Number pi.
--
-- Using Bailey, Borwein & Plouffe 1997, we get:
--
-- pi/8 = M_k 8^{-k} (1/(8k+1) - 1/2(8k+4) - 1/4(8k+5) - 1/4(8k+6))
--
-- http://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula

piDividedBy32 :: I
piDividedBy32 = 
 bigMid [f k (mid (mid (g1 k) (g2 k))(mid (g3 k) (g4 k))) | k <- [0..]]
 where f k x = if k == 0 then x else 0:0:0: f (k-1) x
       g1 k = rational   1  (8*k+1)
       g2 k = rational (-1) (16*k+8)
       g3 k = rational (-1) (32*k+20)
       g4 k = rational (-1) (32*k+24)

-- Conversion to and from double for testing purposes:

toDouble :: I -> Double
toDouble = f 54
 where f 0 x = 0.0
       f k (-1 : x) = (-1.0 + f (k-1) x)/2.0
       f k ( 0 : x) = (       f (k-1) x)/2.0
       f k ( 1 : x) = ( 1.0 + f (k-1) x)/2.0

fromDouble :: Double -> I
fromDouble = f 54
 where f 0 x   = zero
       f k x   = if x  < 0.0 then -1 : f (k-1) (2.0 * x + 1)
                             else  1 : f (k-1) (2.0 * x - 1)

example1 = (toDouble piDividedBy32) * 32
example2 = example1 - pi
main = print example1

mexp :: I -> I
mexp x = bigMid(series one 1)
    where series y n = y : series (divByInt (mul x y) n) (n+1)

msin :: I -> I
msin x = bigMid(series x 2)
 where x2 = compl(sqr x)
       series y n = zero : y : 
                    series(divByInt(mul x2 y)(n*(n+1)))(n+2)

mcos :: I -> I
mcos x = bigMid(series one 1)
 where x2 = compl(sqr x)
       series y n = y : zero : 
                    series(divByInt(mul x2 y)(n*(n+1)))(n+2)

marctan :: I -> I
marctan x = bigMid(series x 1)
 where x2 = compl(sqr x)
       series y n = zero : divByInt y n : 
                    series (mul x2 y) (n+2)

-- Logarithmic function ln(1+x/2)/x.
-- When x = 0 we get the limit, namely 1/2.

mlni :: I -> I
mlni x = bigMid(series one 1)
 where x2 = compl x
       series y n = divByInt y n : series (mul x2 y) (n+1)

-- ln(1+x/2)/x

mln :: I -> I
mln x = mul x (mlni x)

-- The inverse function 1 / (2 - x):

inv :: I -> I
inv x = bigMid(series one)
     where series y = y : series (mul x y)

-- Etc.
