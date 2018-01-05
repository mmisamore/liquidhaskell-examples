import Prelude hiding (head,null,foldr,foldr1,sum,map)

{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty []    = False
notEmpty (x:_) = True

{-@ type NEList a = {v:[a] | notEmpty v} @-}

{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
size :: [a] -> Int
size []     = 0
size (_:xs) = 1 + size xs

{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ die :: {v:String | false} -> a @-}
die :: String -> a
die = error 

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "Unreachable"
divide n d = n `div` d

-- Safe averaging function on non-empty lists
{-@ average :: NEList Int -> Int @-}
average :: [Int] -> Int
average xs = divide total count
  where
    total  = sum xs
    count  = size xs

{-@ type Pos = {v:Int | v > 0} @-}

{-@ head :: NEList a -> a @-}
head :: [a] -> a 
head []    = die "Unreachable"
head (x:_) = x

{-@ tail :: NEList a -> [a] @-}
tail :: [a] -> [a]
tail []     = die "Unreachable"
tail (_:xs) = xs

-- Exercise
safeHead :: [a] -> Maybe a
safeHead xs
  | null xs   = Nothing
  | otherwise = Just $ head xs

{-@ null :: xs:[a] -> {v:Bool | v <=> not (notEmpty xs)} @-}
null []     = True
null (_:xs) = False

-- Seems like chapters should be reordered so this goes before refined datatypes 

{-@ groupEq :: [a] -> [NEList a] @-}
groupEq :: Eq a => [a] -> [[a]]
groupEq [] = []
groupEq (x:xs) = (x:ys) : groupEq zs
  where
    (ys,zs) = span (== x) xs

-- Safely remove consecutive repeated items from a list
eliminateStutter :: Eq a => [a] -> [a]
eliminateStutter = map head . groupEq

-- Usual foldr definition. Works on empty lists
foldr              :: (a -> b -> b) -> b -> [a] -> b 
foldr _ acc []     = acc
foldr f acc (x:xs) = f x (foldr f acc xs)

{-@ foldr1 :: (a -> a -> a) -> NEList a -> a @-}
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 f [] = die "Unreachable"
foldr1 f (x:xs) = foldr f x xs 

{-@ sum :: NEList a -> a @-}
sum :: Num a => [a] -> a
sum [] = die "Unreachable"
sum xs = foldr1 (+) xs

-- Now we can call sum on non-empty lists only
okSum = sum [1,2,3]

-- Bad sum - list is empty
-- badSum = sum []

{-@ map :: (a -> b) -> xs:[a] -> {ys:[b] | notEmpty ys <=> notEmpty xs} @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage wxs = divide totElems totWeight 
  where
    elems     = map (\(w, x) -> w * x) wxs
    weights   = map (\(w, _) -> w    ) wxs
    totElems  = sum elems
    totWeight = sum weights
    sum       = foldr1 (+)

-- A beautiful function!
{-@ risers :: xs:[a] -> {ys:[[a]] | notEmpty ys <=> notEmpty xs} @-}
risers           :: Ord a => [a] -> [[a]]
risers []        = []
risers [x]       = [[x]]
risers (x:y:etc)
  | x <= y       = (x:s) : ss
  | otherwise    = [x] : (s : ss)
    where
      (s, ss)    = safeSplit $ risers (y:etc)

{-@ safeSplit    :: NEList a -> (a, [a]) @-}
safeSplit (x:xs) = (x,xs)
safeSplit _      = die "don't worry, be happy"

