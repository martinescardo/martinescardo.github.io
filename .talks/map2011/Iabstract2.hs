-- Haskell implementation of abstract data type for MAP'2011. Martin Escardo.
-- Based on joit work with Alex Simpson.

-- Use the term algebra of M.
data I = MinusOne | One | M [I]

affine :: I -> I -> I -> I
affine x y = h
 where h MinusOne = x
       h One      = y
       h (M zs)   = M [h z | z <- zs] 
