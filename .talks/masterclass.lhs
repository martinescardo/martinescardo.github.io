
    Computing with numbers coded as finite lists of digits
    ------------------------------------------------------

    (Abridged version of http://www.cs.bham.ac.uk/~mhe/papers/fun2011.lhs)

    3.1415926535897932384626433832795028841971693993751058209749445923078164
      0628620899862803482534211706798214808651328230664709384460955058223172
      5359408128481117450284102701938521105559644622948954930381964428810975
      6659334461284756482337867831652712019091456485669234603486104543266482
      1339360726024914127372458700660631...

    Martin Escardo & Achim Jung

    School of Computer Science
    University of Birmingham, UK
    28th February 2015
    
    Royal Institution Master Classes
    http://www.rigb.org/education/masterclasses

Learning objectives
-------------------

   * Understand that computer calculation with numbers can give wrong
     and unreliable results.

   * Learn basic functional programming with finite and infinite lists.

   * Apply this to get correct and reliable numerical results.


Suggested complementary reading:
Miran Lipovaca. Learn you a Haskell for great good. A beginner's guide.
http://learnyouahaskell.com/


This is both a handout and a computer program
---------------------------------------------

This file is literate code in the programming language Haskell.

  https://en.wikipedia.org/wiki/Literate_programming
  https://wiki.haskell.org/Haskell

You can run it with 

  > ghci masterclass.lhs

from the command prompt, or from the "Haskell" menu in the text editor
emacs if the Haskell mode is installed.

Program code starts with "> ". Everything else is a "comment". In
literate programming, the comments matter as much as the programs
themselves, and sometimes more. 

Wrong results, very fast
------------------------

A floating-point number is a finite approximation of a real number. 
https://en.wikipedia.org/wiki/Floating_point

If you write "pi" at the ghci prompt, you get 3.141592653589793. But
pi has got infinitely many digits. The floating-point approximation,
when printed, actually has all the printed digits correct. Good!

*Main> pi
3.141592653589793

Now try at the Haskell prompt, to compute the square root of 2 and
square it. We should get 2 back. But do we?

*Main> sqrt(2)
1.4142135623730951
*Main> sqrt(2) ^ 2
2.0000000000000004

Almost correct, but not quite. The reason is that sqrt(2) has
infinitely many digits. It is irrational.

The ancient Greeks already knew that.
https://en.wikipedia.org/wiki/Square_root_of_2

When we compute sqrt(2) in floating-point, we chop the infinite result
to a finite one. Then of course when we square it back we don't get
the same number back. 

Pocket calculators also do that. All the usual programming languages
do that.

Does this matter?

Look at the following innocent function, which comes under the fancy
name "logistic map". 
https://en.wikipedia.org/wiki/Logistic_map

> f :: Double -> Double
> f(x) = 4*x*(1-x)

We use double-precision floating point numbers, to try to avoid errors
as much as possible. 
https://en.wikipedia.org/wiki/Double-precision_floating-point_format

This function f is a simple model of population growth, say of fish in
a lake. We use x=0 when there are no fish, and x=1 when the lake has
the maximum capacity.

    * If at some point the fish count is x, then in the next
      generation it is f(x).

    * So if the count of the starting generation is x, after three
      generations the count is f(f(f(x))).

    * For example f(f(f(0.3))=0.99434496.

    * When x=0, we have f(x)=0 again, meaning that there is no
      spontaneous generation of fish.

    * When x=1, there aren't enough resources, and all fish die out,
      and we have f(x)=0 again.

    * If the lake is at half of its fish capacity, we get that in the
      next generation we have f(0.5)=1. Then in the next generation
      they die out: f(f(0.5))=f(1)=0.

We are not claiming that the model is good or sufficiently
realistic. But let's see what happens when we try to compute with it.

Let's suppose our starting generation is the following:

> x0 = 0.671875

Now we want to know what the count is after 60 generations. So we
write a program to repeat f several times:

> fRepeated :: Integer -> Double -> Double
> fRepeated 0 x = x
> fRepeated n x = f(fRepeated (n-1) x)

*Main> fRepeated 60 x0
0.7571538798784869

However, the true result, with that amount of digits, is
0.31544514951466496

In the double-floating-point computation, the errors are small at
first, but they grow each time we apply f, to a point when the result
is completely wrong.

How do we know that 0.31544514951466496 is the right answer? We wrote
a program (below) that computes without ever producing any error at
all. This is what we want to discuss in this lecture.


Idea: compute with the infinite list of digits
----------------------------------------------

In this way we don't ever introduce errors by truncanting an infinite
sequence of digits to a finite one.

But can computers work with infinite data? Yes. With certain
limitations, but yes, they can. These limitations don't get in our way
in the above example and many other useful ones.

A list computation primer
-------------------------

Here are some list computations in Haskell at the ghci prompt. Try them.

*Main> ["Achim","Martin","Kat"]
["Achim","Martin","Kat"]

*Main> map length ["Achim","Martin","Kat"]
[5,6,3]

*Main> [1..20]
[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]

*Main> map odd [1..20]
[True,False,True,False,True,False,True,False,True,False,True,False,True,False,True,False,True,False,True,False]

*Main> filter odd [1..20]
[1,3,5,7,9,11,13,15,17,19]

*Main> 1000 : map length ["Achim","Martin","Kat"]
[1000,5,6,3]

*Main> reverse(1000 : map length ["Achim","Martin","Kat"])
[3,6,5,1000]

*Main> [1..10] ++ [20..30]
[1,2,3,4,5,6,7,8,9,10,20,21,22,23,24,25,26,27,28,29,30]

*Main> [1..]
[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20^CInterrupted

The last one never stops. The following does:

*Main> take 9 [1..]
[1,2,3,4,5,6,7,8,9

Now we write our own function that produces an infinite list

> from :: Integer -> [Integer]
> from n = n : from(n+1)

Read: the list of integers from n is n followed by the list of
integers from n+1.

*Main> take 17 (from 13)
[13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]

*Main> take 20 (repeat 3)
[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3]

*Main> take 20 (zipWith (+) (from 13) (from 17))
[30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68]

We have already reversed a list. Let's write our own reverse function:

> rev :: [a] -> [a]
> rev [] = []
> rev (x:xs) = rev xs ++ [x]

If a list has a head x and a tail xs, to reverse it, first reverse the
tail, and then append the head at the end. Test our function.

This is how the computer computes with this definition.

Firstly, there is no difference between, say, 

  [1,2,3] and 1:[2,3] and 1:2:[3] and 1:2:3:[].

Read: [1,2,3] is the same as 1 followed by [2,3].

So

  rev [1,2,3] = rev(1:[2,3]) 
              = rev [2,3] ++ [1]
              = rev (2:[3]) ++ [1]
              = (rev ([3]) ++ [2]) ++ [1]
              = (rev (3:[]) ++ [2]) ++ [1]
              = ((rev [] ++ [3]) ++ [2]) ++ [1]
              = (([] ++ [3]) ++ [2]) ++ [1]
              = ([3] ++ [2]) ++ [1]
              = [3,2] ++ [1]
              = [3,2,1]
 
The above is a definition by "pattern matching" and "recursion".

Here is another example, which works for infinite lists but not so
well for finite lists (because we didn't say what happens to the empty
list):

> neg :: [Bool] -> [Bool]
> neg (x:xs) = not x : neg xs

*Main> neg (map odd [1,2,3,4])
[False,True,False,True*** Exception: masterclass.lhs:256:3-29: Non-exhaustive patterns in function neg

*Main> take 20 (neg (map odd [1..]))
[False,True,False,True,False,True,False,True,False,True,False,True,False,True,False,True,False,True,False,True]

Now let's go back to numerical computation.

Decimal notation is problematic
--------------------------------

A mathematician called Brouwer observed, in the 1920's, that decimal
notation is not suitable for computation with infinitely many digits.

Consider

   3 x 0.33333...,

where we don't know yet what the next digit will be.  What should be
the first digit of the result?

If we eventually see a digit >3, the output must be

   1.0...

If we eventually see a digit <3, the output must be

   0.9...

Hence while we read a digit =3 again and again, we can't decide the
first digit of the result. We need a crystal ball to compute the first
digit.

     Finiteness property of computation with infinitely many digits:
     ***********************************************************
     * Finitely many digits of the output can depend only on   *
     * finitely many digits of the input.                      *
     ***********************************************************
     Could be called the "no crystal ball" principle.

This is not possible in the case of multiplication by three with
decimal notation, as we have seen. In this case a crystal ball to
predict the whole infinite sequence would be needed, and hence the
function cannot be computed.

To regain the finiteness property, alternative notations are used.

Signed-digit decimal notation
-----------------------------

In addition to the usual digits 0,1,2,3,4,5,6,7,8,9, we allow the
negative digits -9,-8,-7,-6,-5,-4,-3,-2,-1 
https://en.wikipedia.org/wiki/Signed-digit_representation

There is a mathematical reason why this overcomes the problem. Here we
content ourselves by pointing out that in the above example we can
safely output "1." to begin with, and if at some point we read a digit
<3, we can use a negative digit in the output to correct the result.

Signed-digit binary notation
-----------------------------

Decimal notation is good for people because we have 10 fingers. But
computers have only two fingers, and hence they use binary notation.
https://en.wikipedia.org/wiki/Binary_number

We will use binary notation with digits -1, 0, 1.

For simplicity, we will confine our attention to numbers in the line,
or interval, [-1,1] of numbers between -1 and 1, inclusive.

        --------------------------------
       -1                              1         


They can be written in the form

        x = 0 . d0 d1 d2 d3 d4 d5 d6 ...

and hence we drop "0." and write [d0, d1, d2, d3, d4, d5, d6, ...] in Haskell.

Binary notation can be understood in many ways. A geometrical
understanding is useful.

        --------------------------------
       -1      -1/2     0      1/2     1         



       If d0 = -1, then x is in the interval [-1,0].

        -----------------
       -1               0


       If d0 = 0, then x is in the interval [-1/2,1/2].

                 ----------------
               -1/2            1/2

       If d0 = 1, then x is in the interval [0,1].

                        ----------------
                        0              1         

Now, using the next digit d1, we look at a subinterval of the first
subinterval as above. And so on.

An infinite sequence of signed digits is an "address" (or postcode) of
a point in the line. 

      -1 means go to the left sub-interval
       0 means go to the centre sub-interval
       1 means go to the right sub-interval

If the postman travels infinitely long, he will reach the desired
point and deliver the letter. But if he travels for a finite amount of
time, quickly he will get a very small interval containing the point,
and he can safely leave the letter with a neighbour.

Computing with infinite signed-digit binary notation
----------------------------------------------------

We work with the signed unit interval I=[-1,1], using binary notation
with signed digits.

We use the "type" Int of integers to hold our digits -1,0,1. For
emphasis, we give it the name Digit.

> type Digit = Int

We code the line segment I=[-1,1] with infinite sequences of digits.

> type I = [Digit]   

A sequence ds = [d0, d1, ..., dn, ...] codes the number

    x = d0 / 2 + d1 / 4 + d2 / 8 + ... + dn / 2^{n+1} + ...

Some constants
---------------

> one, zero, minusOne, half, half', minusHalf :: I
> minusOne  = repeat (-1)
> minusHalf = -1 : repeat 0
> zero      = repeat 0
> half      = 1 : zero
> half'     = 0 : repeat 1
> one       = repeat 1

Both half and half' code the same number 1/2 = 0.5. Draw a picture to
see that.

Auxiliary codings of numbers
----------------------------

Although the main coding we consider is the above, it is convenient to
use auxiliary intermediate codings to simplify the algorithms.

We still use base 2, but allow more digits, and then convert back to
the three digits -1,0,1.

Type of digits -2,-1,0,1,2: 

> type Digit2  = Int  

Type of digits -4,-3,-2,-1,0,1,2,3,4:

> type Digit4  = Int  

More generally, type of digits from -n to n:

> type Digitn = Int

Type of intervals [-2,2], [-4,4], and [-n,n]:

> type I2 = [Digit2]  
> type I4 = [Digit4]  
> type In = [Digitn]     

The following converts back to our standard representation.  It
amounts to division by n as a function [-n,n] -> [-1,1] for n>=2.  

We use n = 2 and n = 4 in the programs contained in this file.

The first two cases of the following definition can be omitted, as
they are taken care by they last case. They are optimizations that
give a significant speed-up (by reducing the "lookahead complexity").

> divideBy :: Int -> In -> I
> divideBy n (0:x) = 0 : divideBy n x
> divideBy n (a:x) | abs a == n 
>   = (a `div` n) : divideBy n x
> divideBy n (a:b:x) = 
>   let d = 2*a+b
>   in if      d < -n then -1 : divideBy n (d+2*n:x)
>      else if d >  n then  1 : divideBy n (d-2*n:x)
>                     else  0 : divideBy n (d:x)               

> divideBy2 :: I2 -> I
> divideBy2 ( 0:x) =  0 : divideBy2 x
> divideBy2 ( 2:x) =  1 : divideBy2 x 
> divideBy2 (-2:x) = -1 : divideBy2 x 
> divideBy2 (a:b:x) = 
>   let d = 2*a+b
>   in if      d < -2 then -1 : divideBy2 (d+4:x)
>      else if d >  2 then  1 : divideBy2 (d-4:x)
>                     else  0 : divideBy2 (d:x)               

Some very basic operations on I=[-1,1]
--------------------------------------

Addition as a function [-1,1] x [-1,1] -> [-2,2]. This is our first
example where we use an auxiliary coding:

> add2 :: I -> I -> I2
> add2 = zipWith (+)

Midpoint (x+y)/2 as a function [-1,1] x [-1,1] -> [-1,1]:

> mid :: I -> I -> I
> mid x y = divideBy2 (add2 x y)

Proceeding in this way, we have avoided a myriad of cases in the
definition of addition and mid points that one often sees in the
literature, while still being time and space efficient.

(There would normally be in fact 3^4 cases, because we need to look at
two digits of each argument to produce one output digit.)

Complement x |-> -x as a function [-1,1] -> [-1,1]:

> compl :: I -> I
> compl = map (\d -> -d)

Division by a positive integer:

> divByInt :: I -> Int -> I
> divByInt x n = f x 0
>    where f (a:x) s = let t = a+2*s 
>                      in if t >=  n then  1 : f x (t-n)
>                    else if t <= -n then -1 : f x (t+n)
>                                    else  0 : f x t


Infinitary operations
---------------------

Given a sequence x0,x1,x2,...,xn,... of points of [-1,1], 
compute 

            x0 / 2 + x1 / 4 + x2 / 8 + ... +  xn / 2^(n+1) + ...
          = mid(x0, mid(x1, mid(x2, ...)))

We write this as 

            bigMid xs

The Haskell definition

  (*) bigMig(x:xs) = mid x (bigMid xs)

doesn't work, because mid needs two digits of input from each argument
to produce one digit of output, and hence (*) cannot produce any
digit.

We use the following algorithm, which uses the auxiliary coding I4 to
compute bigMid' :: [I] -> I4, and then converts back to I by division
by 4:

> bigMid :: [I] -> I 
> bigMid = (divideBy 4) . bigMid'
>  where bigMid'((a:b:x):(c:y):z) = 2*a+b+c : bigMid'((mid x y):z)

Although bigMid cannot be defined using (*), it does satisfy the
equation (*).

Truncated operations
--------------------

Some truncated operations are also useful. The truncation operation
truncate: R -> [-1,1] from arbitrary numbers in the whole line R to
the line segment [-1,1] is mathematically defined as:

      truncate(x) = max(-1,min(x,1))

                     /
                     |    -1 if x <= -1,
                  = <      x if      -1 <= x <= 1,
                     |     1 if                 1 <= x.
                     \

Draw a picture of the function. 

Truncated x+1 as a function [-1,1] -> [-1,1], that is, 
x |-> min(x+1,1):

> addOne :: I -> I
> addOne ( 1 : x) = one
> addOne ( 0 : x) = 1 : addOne x
> addOne (-1 : x) = 1 : x

Truncated x-1 as a function [-1,1] -> [-1,1], that is, 
x |-> max(-1,x-1)

> subOne :: I -> I
> subOne ( 1 : x) = -1 : x
> subOne ( 0 : x) = -1 : subOne x
> subOne (-1 : x) = minusOne

Truncated x |-> 1-x as a function [-1,1] -> [-1,1].

> oneMinus :: I -> I
> oneMinus = addOne.compl

Truncated multiplication by 2 as a function [-1,1] -> [-1,1], that is,
x |-> max(-1,min(2x,1)).

2(1 : x) = 2(1/2 + x/2) = 1 + x

> mulBy2 :: I -> I
> mulBy2 ( 1 : x)  = addOne x
> mulBy2 ( 0 : x)  = x
> mulBy2 (-1 : x)  = subOne x

Truncated addition as a function [-1,1] x [-1,1] -> [-1,1],
that is, (x,y) |-> max(-1,min(x+y,1))

> add :: I -> I -> I
> add x y = mulBy2(mid x y)

Truncated multiplication by 4:

> mulBy4 :: I -> I
> mulBy4 = mulBy2.mulBy2

Truncated multiplication of a number by non-negative integer:

> tMulByInt :: I -> Int -> I
> tMulByInt x 0 = zero
> tMulByInt x 1 = x
> tMulByInt x n = if even n 
>                 then mulBy2(tMulByInt x (n `div` 2)) 
>                 else add x (mulBy2(tMulByInt x (n `div` 2)))


Summary so far
--------------

We have

   one, zero, minusOne, half, minusHalf :: I
   divideBy :: Int -> In -> I
   add2 :: I -> I -> I2
   mid :: I -> I -> I
   bigMid :: [I] -> I 
   compl :: I -> I
   divByInt :: I -> Int -> I

with truncated operations

   addOne :: I -> I
   subOne :: I -> I
   oneMinus :: I -> I
   mulBy2 :: I -> I
   mulBy4 :: I -> I
   add :: I -> I -> I
   tMulByInt :: I -> Int -> I

Conversion to and from Double
-----------------------------

We now want to print the results in human-readable form. The easiest
kind of conversion is to/from Double. This can be done without
round-off errors, but of course the conversion to Double will involve
a truncation error, and the last digit cannot be guaranteed to be
correct.

Doubles have 54 significant binary digits.

> toDouble :: I -> Double
> toDouble = f 55
>  where f 0 x = 0.0
>        f k (-1 : x) = (-1.0 + f (k-1) x)/2.0
>        f k ( 0 : x) = (       f (k-1) x)/2.0
>        f k ( 1 : x) = ( 1.0 + f (k-1) x)/2.0


> fromDouble :: Double -> I
> fromDouble = f 55
>  where f 0 x   = zero
>        f k x   = if x  < 0.0 then -1 : f (k-1) (2.0 * x + 1)
>                              else  1 : f (k-1) (2.0 * x - 1)

Example: Computation of the constant pi
---------------------------------------

There are many ways of computing the number pi. Here is one that
doesn't use multiplication of numbers other than rational numbers.

Using Bailey, Borwein & Plouffe's formula, we get

  pi/8 = bigMid xs

where xn = n * 8^(-n) (1/(8n+1) - 1/2(8n+4) - 1/4(8n+5) - 1/4(8n+6)).

http://en.wikipedia.org/wiki/Bailey%E2%80%93Borwein%E2%80%93Plouffe_formula

> piDividedBy32 :: I
> piDividedBy32 = 
>  bigMid 
>   [f n (mid (mid (g1 n) (g2 n))(mid (g3 n) (g4 n))) | n <- [0..]]
>  where f n x = if n == 0 then x else 0:0:0: f (n-1) x
>        g1 n = divByInt one              (8*n+1)
>        g2 n = divByInt (-1 : zero)      (8*n+4)
>        g3 n = divByInt ( 0 : -1 : zero) (8*n+5)
>        g4 n = divByInt ( 0 : -1 : zero) (8*n+6)

*Main> (toDouble piDividedBy32) * 32
3.141592653589793
*Main> pi
3.141592653589793

This confirms that Haskell correctly computes pi in Double. Or that
our algorithms so far are not completely wrong.

Multiplication by an integer
----------------------------

We multiply a number in [-1,1] by a positive integer, producing
integer and fractional parts. In particular we will be able to
multiply by 10, and hence convert to decimal (with a caveat - see
below).

> mulByInt :: I -> Int -> (Int,I)
> mulByInt x n = f n
>  where f 1 = (0, x)
>        f n = let (a,u) = f (n `div` 2)
>                  d:y = u
>                  b = 2*a+d
>              in if even n 
>                 then (b,y)
>                 else let e:t = mid x y
>                      in (b+e,t)

Suggestion by Tomas Jakl (13 Feb 2015).

> mulByInt' :: I -> Int -> (Int,I)
> mulByInt' x n = f n
>  where f 1 = (0, x)
>        f n = let (a,d:y) = f (n `div` 2)
>                  b = 2*a+d
>              in if even n 
>                 then (b,y)
>                 else let e:t = mid x y
>                      in (b+e,t)


Conversion to decimal
---------------------

Cannot be done without crystal balls. However, there is a conversion
to decimal that fails, by looping for ever without giving any answer,
if the input is of the form m/10^n with m and n integers (10-adic
numbers). This is the best that can be done without crystal balls.

We consider conversion using negative decimal digits first. 

> type Decimal = [Int] 

The conversion allowing negative decimal digits is defined by:

> signedDecimal :: I -> Decimal
> signedDecimal x = let (d,y) = mulByInt x 10 
>                   in d : signedDecimal y

This always works.

We now get rid of negative decimal digits. This works for positive,
non-10-adic numbers, only, as discussed above. We use a "finite state
automaton" with states "f" and "g", using a positiveness test as
an auxiliary function:

> normalize :: Decimal -> Decimal
> normalize x = f x
>  where f(d:x) = if positive x then d : f x else d-1 : g x
>        g(0:x) = 9 : g(x)
>        g(d:x) = if positive x then 10+d : f x else 10+d-1 : g x
>        positive (d:x) = d > 0 || (d == 0 && positive x)

Here || means "or" and && means "and".

We now convert a positive, non 10-adic, number to decimal 
notation using only non-negative digits:

> decimal :: I -> Decimal
> decimal = normalize.signedDecimal

> decimalString :: I -> String
> decimalString = concat.(map show).decimal

The decimal expansion of pi can be computed as follows:

> piInDecimal = let (m,x) = mulByInt piDividedBy32 32 
>               in show m ++ "." ++ decimalString x

*Main> piInDecimal 
"3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446^CInterrupted.


Full multiplication algorithm
-----------------------------

We first consider an algorithm that is less difficult to understand
but slower than other known algorithms.

We first need multiplication of a signed digit by a number
in [-1,1]:

> digitMul :: Digit -> I -> I
> digitMul (-1) x = compl x
> digitMul   0  x = zero
> digitMul   1  x = x

The easiest multiplication algorithm uses the bigMid function.

> mul :: I -> I -> I
> mul x y = bigMid (zipWith digitMul x (repeat y))

Right result, not so fast
-------------------------

We now try to compute the logistic map exactly. 

> f0 :: I -> I
> f0 x = mulBy4 (mul x (oneMinus x))    

> f0Repeated :: Integer -> I -> I
> f0Repeated 0 x = x
> f0Repeated n x = f0(f0Repeated (n-1) x)

The number x0 = 0.671875 defined above as has an exact binary
representation (not all numbers with a finite decimal representation
have a finite binary representation):

> x0' :: I
> x0' = [1,0,1,0,1,1] ++ zero

*Main> x0
0.671875
*Main> toDouble x0'
0.671875
*Main> fRepeated 60 x0
0.7571538798784869
*Main> f0Repeated 60 x0'

... never gets back to us.

If we compile the program with optimizations -O2, we get the following
in a core i5 machine running at 3.40GHz with ghci version 7.6.3:

$ time ./masterclass 
Stack space overflow: current size 8388608 bytes.
Use `+RTS -Ksize -RTS' to increase it.

real	102m21.835s
user	102m3.948s
sys	0m16.168s

Let's be more modest just to see whether things are working. The
option ":set +s" asks Haskell to print run time and memory usage.

*Main> :set +s
*Main> fRepeated 3 x0
0.9723145458265208
(0.00 secs, 2582884 bytes)
*Main> toDouble (f0Repeated 3 x0')
0.9723145458265208
(0.88 secs, 231936144 bytes)
*Main> fRepeated 4 x0
0.10767587920274964
(0.00 secs, 519028 bytes)
*Main> toDouble (f0Repeated 4 x0')
0.10767587920274962
(8.34 secs, 2163082944 bytes)

No pain, no gain
----------------

Our multiplication algorithm is neat, but very slow. (Because it has a
bad "lookahead" complexity.)

Here is a slightly messier, but considerably faster multiplication
algorithm:

> mul1 :: I -> I -> I
> mul1 (a0 : a1 : x) (b0 : b1 : y) = mid p q
>  where p = mid u v
>        u = a0*b1 : mid (digitMul b1 x) (digitMul a1 y)
>        v = mid (digitMul b0 x) (digitMul a0 y)
>        q = a0*b0 : a1*b0 : a1*b1 : mul1 x y

This is based on simple algebraic laws relating multiplication and
midpoint.

> f1 :: I -> I
> f1 x = mulBy4 (mul1 x (oneMinus x))    

> f1Repeated :: Integer -> I -> I
> f1Repeated 0 x = x
> f1Repeated n x = f1(f1Repeated (n-1) x)

*Main> toDouble (f1Repeated 4 x0')
0.10767587920274962
(0.04 secs, 9341488 bytes)

This is encouraging. And we can finally get our desired correct result:

*Main> toDouble (f1Repeated 60 x0')
0.31544514951466496
(8.38 secs, 1790523516 bytes)

We can get even faster, by considering special cases in the previous
algorithm and handling them in a cleverer way:

> mul2 :: I -> I -> I
> mul2 (0:x) y = 0 : mul2 x y
> mul2 x (0:y) = 0 : mul2 x y
> mul2 (a0 : 0 : x) (b0 : 0 : y) = mid p q
>   where p  = 0 : mid (digitMul b0 x) (digitMul a0 y)
>         q = a0*b0 : 0 : 0 : mul2 x y
> mul2 (a0 : 0 : x) (b0 : b1 : y) = mid p q
>   where p  = mid u v
>         u = a0*b1 : 0 : digitMul b1 x
>         v = mid (digitMul b0 x) (digitMul a0 y)
>         q = a0*b0 : 0 : 0 : mul2 x y
> mul2 (a0 : a1 : x) (b0 : 0 : y) = mid p q
>   where p  = mid u v
>         u = 0 : 0 : digitMul a1 y
>         v = mid (digitMul b0 x) (digitMul a0 y)
>         q = a0*b0 : a1*b0 : 0 : mul2 x y
> mul2 (a0 : a1 : x) (b0 : b1 : y) = mid p q
>   where p  = mid u v
>         u = a0*b1 : mid (digitMul b1 x) (digitMul a1 y)
>         v = mid (digitMul b0 x) (digitMul a0 y)
>         q = a0*b0 : a1*b0 : a1*b1 : mul2 x y

> f2 :: I -> I
> f2 x = mulBy4 (mul2 x (oneMinus x))    

We could now define f2Repeated, but we got tired of that.

> repeatFunction :: (a -> a) -> Integer -> a -> a
> repeatFunction g 0 x = x
> repeatFunction g n x = g(repeatFunction g (n-1) x)

*Main> toDouble (repeatFunction f2 60 x0')
0.31544514951466496
(1.68 secs, 363367516 bytes)

Now that's 5 times faster, and so worth the pain. We can make it still
a bit faster.

The squaring function sqr(x) = x^2 can be defined as mul x x, or 
mul1 x x, or mul2 x x, but a direct definition gives a faster algorithm:

> sqr :: I -> I
> sqr (0:x) = 0 : 0 : sqr x
> sqr (a0 : 0 : x) = mid p q
>  where p = 0 : digitMul a0 x
>        q = a0*a0 : 0 : 0 : sqr x
> sqr (a0 : a1 : x) = mid p q
>  where p = mid u v
>        u = a0*a1 : digitMul a1 x
>        v = digitMul a0 x
>        q = a0*a0 : a1*a0 : a1*a1 : sqr x


Now notice that 

  4x(1-x) = 1-(2x-1)^2

and so we can define

> f3 x = oneMinus(sqr(g x))       
>       where g ( 1 : x) = x              
>             g ( 0 : x) = subOne x
>             g (-1 : x) = minusOne

where we have g(x)= max(-1,2x-1) 

Now we can compute our desired result in under a second:

*Main> toDouble (repeatFunction f3 60 x0')
0.31544514951466496
(0.37 secs, 81187348 bytes)

This is 22 times faster than the first version that works.

Let's see how far we can get.

*Main> toDouble (repeatFunction f3 100 x0')
0.18232766833466935
(1.49 secs, 324698688 bytes)

*Main> toDouble (repeatFunction f3 200 x0')
0.3101443546894904
(10.24 secs, 2366637788 bytes)

*Main> toDouble (repeatFunction f3 300 x0')
0.5259209461477587
(35.44 secs, 8017381188 bytes)

But why would any one need to know the population of the lake with so
many correct decimal digits? Usually, two or three digits are enough
in practice in such situations.

A decimal digit needs 4 binary digits

> chop :: Int -> I -> I
> chop n x = take (4 * n) x ++ repeat 0

We get faster if we require fewer digits:

*Main> toDouble (chop 3 (repeatFunction f3 300 x0'))
0.52587890625
(31.20 secs, 7045049620 bytes)

But not much faster in this example. And the following isn't much
faster either:

*Main> toDouble (chop 2 (repeatFunction f3 300 x0'))
0.5234375
(30.34 secs, 6883336664 bytes)

*Main> toDouble (chop 1 (repeatFunction f3 300 x0'))
0.5
(30.32 secs, 6879675584 bytes)

*Main> take 4 (repeatFunction f3 300 x0')
[1,0,0,0]
(30.34 secs, 6879915800 bytes)

*Main> take 55 (repeatFunction f3 300 x0')
[1,0,0,0,1,0,-1,0,1,0,1,0,0,0,1,1,0,-1,0,0,0,0,1,0,
-1,-1,0,1,0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,1,-1,0,1,
 1,-1,0,1,-1,0,0]
(35.53 secs, 8013619836 bytes)

But there is a way of getting faster - we compile the program with
optimizations:

> main = putStr(show(toDouble (repeatFunction f3 300 x0')))

$ ghc -O2 --make masterclass.lhs
$ time ./masterclass
time ./masterclass
0.5259209461477587
real	0m3.893s
user	0m3.844s
sys	0m0.012s

Now, 3.8sec is a long time for such a "simple" calculation, which can
be done in a fraction of a second in floating point arithmetic.  But
the given result is reliable, as opposed to that coming from the
floating point computation, where we get a number, but we can't see
how many digits, if any, are correct by just looking at the number.

Here every printed digit is guaranteed to be correct. The price is
that sometimes no digit at all is printed, as we have seen, because we
run out of time or computer memory. But then we don't get spurious
results.

Our implementation is not a professional one. There are much faster
implementations by various people, using different codings of
numbers. Here we have chosen a simple coding to illustrate the main
concepts.

To close this section, in 2min 19sec we can compute a thousand
iterations with the compiled version using

 main = putStr(show(toDouble (repeatFunction f3 1000 x0')))

instead.

$ time ./masterclass 
0.5097669825386573
real	2m19.067s
user	2m18.492s
sys	0m0.524s

And for 2000 we get 0.9467552627300043 in 19min.

More
----

You are invited to look at the full version of this program to see
more techniques and examples.
http://www.cs.bham.ac.uk/~mhe/papers/fun2011.lhs)
