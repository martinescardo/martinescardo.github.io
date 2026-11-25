module Utils where

takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil _ [] = []
takeUntil p (x:xs) = x : if p x then [] else takeUntil p xs

pickMax :: (Ord a) => [(a, b)] -> (a, b)
pickMax [v] = v
pickMax ((v, x) : (w, y) : zs) = 
  if v >= w then pickMax ((v, x) : zs) else pickMax ((w, y) : zs)

pickMin :: (Ord a) => [(a, b)] -> (a, b)
pickMin [v] = v
pickMin ((v, x) : (w, y) : zs) = 
  if v <= w then pickMin ((v, x) : zs) else pickMin ((w, y) : zs)

some, every  :: [a] -> (a -> Bool) -> Bool
some  xs p = any p xs
every xs p = all p xs

contained :: Eq x => [x] -> [x] -> Bool
contained xs ys = every xs (\x -> elem x ys)

minus :: Eq x => [x] -> [x] -> [x]
minus xs ys = [x | x<-xs, not(elem x ys)]    
