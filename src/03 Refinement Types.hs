import Prelude hiding (abs)


{-@ type Zero = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ zero :: Zero @-}
zero = 0 :: Int

{-@ one, two, three :: NonZero @-}
one = 1 :: Int
two = 2 :: Int
three = 3 :: Int

{-@ type Nat  = {v:Int | v >= 0} @-}
{-@ type Even = {v:Int | v mod 2 == 0} @-}
{-@ type Lt100 = {v:Int | v < 100} @-}

{-@ zero' :: Nat @-}
zero' = zero

{-@ zero'' :: Even @-}
zero'' = zero

-- To assert that code is unreachable 
{-@ die :: {v:String | false} -> a @-}
die msg = error msg

-- Assert that branch is unreachable
cannotDie = if 1 + 1 == 3 
              then die "Whoops!" 
              else () 

-- LiquidHaskell can assert whether or not this function is safe. Example of a precondition on an input
{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "Unreachable branch"
divide n d = n `div` d

-- Example
avg :: [Int] -> Int
avg xs = case n of
           0 -> 1 -- without knowing how to write down NEList type yet
           _ -> divide total n
  where
    total = sum xs
    n     = length xs

-- Example of a postcondition on an output
{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs n | n < 0     = -n
      | otherwise = n 

-- Example of postcondition on a boolean output
{-@ isPositive :: x:Int -> {v:Bool | v <=> x > 0} @-}
isPositive :: Int -> Bool
isPositive x = x > 0

-- Add refinement type of Bool so we can use it with lAssert below
{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> a -> a @-}
lAssert :: Bool -> a -> a
lAssert True x  = x
lAssert False x = die "This should be unreachable"

yes = lAssert (1 + 1 == 2) ()
-- no  = lAssert (1 + 1 == 3) ()  -- rejected by SMT solver as desired

-- Final example for chapter
truncate :: Int -> Int -> Int
truncate i max
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
  where
    i'   = abs i
    max' = abs max


