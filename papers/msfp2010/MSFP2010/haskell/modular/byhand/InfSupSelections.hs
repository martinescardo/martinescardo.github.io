module InfSupSelections (Three, epsilonInf, epsilonSup,
                         epsilonInfZ, epsilonSupZ) 
where

-- 3 = {-1,0,1}, represented by the type Int. 

type Three = Int

-- We try to minimize the number of evaluations of p.

epsilonInf, epsilonSup :: [x] -> (x -> Three) -> x

epsilonInf       [] p = undefined
epsilonInf (x : xs) p = f xs x (p x)
   where f           xs  a(-1)= a 
         f           []  a  r = a
         f     (x : xs)  a  1 = f xs x (p x) 
         f          xs   a  0 = g xs
            where g (x : xs) = if p x == -1 then x else g xs
                  g       [] = a


epsilonSup       [] p = undefined
epsilonSup (x : xs) p = f xs x (p x)
   where f           xs  a  1 = a 
         f           []  a  r = a
         f     (x : xs)  a(-1)= f xs x (p x) 
         f          xs   a  0 = g xs
            where g (x : xs) = if p x == 1 then x else g xs
                  g       [] = a

-- The unrestricted case is more inefficient but easier:
-- N is the set of natural numbers.

epsilonInfZ, epsilonSupZ :: [x] -> (x -> Int) -> x

epsilonInfZ [] p = undefined
epsilonInfZ (x : xs) p = f xs x (p x)
   where f       [] a pa = a
         f (x : xs) a pa = let px = p x 
                     in if px < pa 
                        then f xs x px 
                        else f xs a pa

epsilonSupZ [] p = undefined
epsilonSupZ (x : xs) p = f xs x (p x)
   where f       [] a pa = a
         f (x : xs) a pa = let px = p x 
                     in if px > pa 
                        then f xs x px 
                        else f xs a pa
