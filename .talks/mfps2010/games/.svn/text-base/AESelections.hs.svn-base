module AESelections (epsilonAll, epsilonSome) where

-- We try to minimize the number of evaluations of p.

epsilonAll, epsilonSome :: [x] -> (x -> Bool) -> x

epsilonAll       [] p = undefined
epsilonAll (x : xs) p = f xs x (p x)
  where f      xs  a False = a 
        f      []  a r     = a
        f (x : xs) a True  = f xs x (p x) 

epsilonSome       [] p = undefined
epsilonSome (x : xs) p = f xs x (p x)
   where f      xs  a True  = a 
         f      []  a r     = a
         f (x : xs) a False = f xs x (p x) 

