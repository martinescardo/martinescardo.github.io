module K where

data K r x = K {quantifier :: (x -> r) -> r}

instance Functor (K r) where
    fmap f phi = K (\p -> quantifier phi $ p . f)

instance Applicative (K r) where
    pure x = K (\p -> p x)
    fs <*> phis = do
        f <- fs
        x <- phis
        return (f x)

instance Monad (K r) where
    return = pure
    phi >>= f = K (\p -> quantifier phi (\x -> quantifier (f x) p))

-- sequence for quantifiers that depend on the moves played so far
hsequence :: Monad m => [[x] -> m x] -> m [x]
hsequence = h []
  where
    h _ []       = return []
    h s (f : fs) = do
      x  <- f s
      xs <- h (s ++ [x]) fs
      return (x : xs)
