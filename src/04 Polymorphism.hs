import Prelude hiding (length)
import Data.Vector 
import Data.List

-- Refinement type for vectors of specified length
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}

-- Example
{-@ twoLangs :: VectorN String 2 @-}
twoLangs = fromList ["haskell", "javascript"]

-- Refinement type for non-empty vectors
{-@ type NEVector a = {v:Vector a | vlen v > 0} @-}

-- Safe version of head on vectors - require them to be non-empty
{-@ head :: NEVector a -> a @-}
head :: Vector a -> a
head xs = xs ! 0

-- LiquidHaskell ensures that (!) is used safely here
safeLookup :: Vector a -> Int -> Maybe a
safeLookup v i 
  | ok        = Just (v ! i)
  | otherwise = Nothing
  where
    ok = i >= 0 && i < Data.Vector.length v

-- Refinement type for integers in a given range
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

-- Refinement type for sparse vectors
{-@ type SparseN a N = [(Btwn 0 N, a)] @-}

-- Example of taking a dot product with a sparse vector
{-@ sparseProduct :: xs:Vector a -> SparseN a (vlen xs) -> a @-}
sparseProduct :: (Num a) => Vector a -> [(Int,a)] -> a
sparseProduct xs ys = Data.List.foldl' step 0 ys
  where
    step acc (i,a) = acc + (xs ! i) * a


