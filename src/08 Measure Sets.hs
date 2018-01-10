import Prelude hiding (reverse,elem,filter)

import Data.Set hiding (insert,size,filter) -- Spec file from LH Prelude embeds Data.Set into SMT set theory solver

{-@ type True  = {v:Bool | v} @-}
{-@ type False = {v:Bool | not v} @-}
{-@ type Implies P Q = {v:Bool | v <=> (P => Q)} @-}

-- Logical implication as a function, verified by SMT
{-@ implies        :: p:Bool -> q:Bool -> Implies p q @-}
implies            :: Bool -> Bool -> Bool
implies False _    =  True
implies True False =  False
implies True True  =  True

-- Prove a simple proposition
{-@ prop_oneplusone_equals_two :: Int -> True @-}
prop_oneplusone_equals_two :: Int -> Bool
prop_oneplusone_equals_two x = (x == 1 + 1) `implies` (x == 2)

-- The SMT solver knows about basic arithmetic
{-@ prop_xplusy_lessthan200 :: Int -> Int -> True @-} 
prop_xplusy_lessthan200 :: Int -> Int -> Bool 
prop_xplusy_lessthan200 x y = ((x < 100) && (y < 100)) `implies` (x + y < 200)

-- Set intersection is commutative. This magic works since LH knows that Data.Set provides sets
{-@ prop_intersection_comm :: xs:Set a -> ys:Set a -> True @-}
prop_intersection_comm xs ys = (xs `intersection` ys) == (ys `intersection` xs) 

-- Set union is associative
{-@ prop_union_assoc :: xs:Set a -> ys:Set a -> zs:Set a -> True @-}
prop_union_assoc xs ys zs = (xs `union` ys) `union` zs == xs `union` (ys `union` zs)

-- Example of something that fails, just to ensure not everything passes 
-- {-@ prop_cup_diff_bad :: xs:Set a -> ys:Set a -> True @-}
{-prop_cup_diff_bad xs ys = pre `implies` (xs == (xs `union` ys) `difference` ys)-}
  {-where-}
    {-pre = True -}

-- Corrected precondition
{-@ prop_cup_diff_good :: xs:Set a -> ys:Set a -> True @-}
prop_cup_diff_good xs ys = pre `implies` (xs == (xs `union` ys) `difference` ys)
  where
    pre = xs `intersection` ys == empty

-- Measure the elements of a list as a Set that the SMT can reason about
{-@ measure elts @-}
elts :: Ord a => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

-- Type alias for ordinary lists, for symmetry
{-@ type List a = [a] @-}

-- A list whose element set equals S
{-@ type ListS a S = {v:[a] | elts v == S} @-}

-- The empty list
{-@ type ListEmp a = ListS a empty @-}

-- A list whose element set equals that of another list 
{-@ type ListEq a X = ListS a {elts X} @-}

-- A list whose element set is a subset of that of another list 
{-@ type ListSub a X = {v:[a] | Set_sub (elts v) (elts X)} @-}

-- A list whose element set is a union of those of two other lists
{-@ type ListUnion a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}

-- A list whose element set is exactly the element X together with the elements of the set Y
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

-- Statically verify that appending lists results in a list whose element set is the set union of the inputs
{-@ append       :: xs:[a] -> ys:[a] -> ListUnion a xs ys @-}
append           :: [a] -> [a] -> [a]
append [] ys     =  ys
append (x:xs) ys =  x : append xs ys

-- Reversing a list preserves the underlying set of elements. 
-- Note that we don't check that it's length-preserving here.
{-@ reverse :: xs:[a] -> ListEq a xs @-}
reverse     :: [a] -> [a]
reverse []     = []
reverse (x:xs) = append (reverse xs) [x]

-- Assert that one list is half the size of another
{-@ predicate IsHalfSize X Y = size X <= ((size Y)/2)+1 @-}

-- Assert that element set of one list is the union of two others
{-@ predicate IsUnion X Y Z = elts xs == Set_cup (elts X) (elts Y) @-}

-- Split a list in half by taking every other element. Ensures that the set union of the resulting
-- pair gives back the original list and that the sizes of the resulting lists are halved
{-@ halve :: xs:[a] -> {v:([a],[a]) | IsHalfSize (fst v) xs && IsHalfSize (snd v) xs && IsUnion (fst v) (snd v) xs} @-}
halve     :: [a] -> ([a],[a])
halve (x:y:xs) = (x : ys, y : zs) where (ys,zs) = halve xs
halve xs       = (xs, [])

-- Element membership on lists checked by element membership on the underlying sets
{-@ elem :: x:a -> xs:[a] -> {v:Bool | v <=> member x (elts xs)} @-}
elem :: Eq a => a -> [a] -> Bool
elem x []     = False
elem x (y:xs) = (x == y) || (elem x xs) 

{-@ test1 :: True @-}
test1     =  elem 2 [1, 2, 3]

{-@ test2 :: False @-}
test2     =  elem 2 [1, 3]

-- Insertion sort maintains the underlying set
{-@ insertSort :: xs:[a] -> ListEq a xs @-}
insertSort []       = []
insertSort (x : xs) = insert x (insertSort xs)
  where
    {-@ insert :: Ord a => x:a -> xs:[a] -> ListUn1 a x xs @-}
    insert     :: Ord a => a -> [a] -> [a]
    insert x []     = [x]
    insert x (y:ys) = if x <= y
                      then x : y : ys 
                      else y : insert x ys

-- Measure the size of any list
{-@ measure size @-}
{-@ size    :: xs:List a -> Nat @-}
size        :: [a] -> Int
size []     =  0
size (x:xs) =  1 + size xs

-- Merge operation with proof that it unions the underlying sets 
{-@ merge :: Ord a => xs:List a -> ys:List a -> ListUnion a xs ys / [size xs + size ys] @-}
merge     :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = if x <= y
                      then x : merge xs (y : ys)
                      else y : merge (x : xs) ys

-- Verify that appending gives the same underlying set as merging
{-@ prop_append_merge   :: xs:List a -> ys:List a -> True @-}
prop_append_merge xs ys = elts zs == elts zs'
  where
    zs  = merge xs ys
    zs' = append xs ys

-- A merge sort with proof that element set of output agrees with the input
{-@ mergeSort :: xs:List a -> ListEq a xs @-}
mergeSort xs  =  go (size xs) xs
  where
    {-@ go :: Ord a => n:Nat -> xs:List a -> ListEq a xs @-}
    go     :: Ord a => Int -> [a] -> [a]
    go 0 xs = xs
    go _ [] = []
    go n xs = merge mys mzs
      where
        (ys,zs) = halve xs
        mys     = if size ys <= 1 then ys else go (n-1) ys
        mzs     = if size zs <= 1 then zs else go (n-1) zs

-- Assert that a list contains unique set of elements
{-@ measure unique @-}
unique        :: Ord a => [a] -> Bool
unique []     =  True
unique (x:xs) =  unique xs && not (x `member` elts (xs))

-- Refinement type of lists with unique elements
{-@ type UniqueList a = {v:List a | unique v} @-}

-- Verified unique list
{-@ isUnique :: UniqueList Int @-}
isUnique :: [Int]
isUnique = [1,2,3]

-- Demo a list that is not unique
-- {-@ isNotUnique :: UniqueList Int @-}
{-isNotUnique :: [Int]-}
{-isNotUnique = [1,2,3,1]-}

-- Refined filter function
{-@ filter      :: (a -> Bool) -> xs:UniqueList a -> ListSub a xs @-}
filter          :: (a -> Bool) -> [a] -> [a]
filter f []     =  []
filter f (x:xs) =  if f x then x : filter f xs else filter f xs

-- Produce a unique list from any list by removing duplicates
{-@ nub :: Ord a => List a -> UniqueList a @-}
nub     :: Ord a => [a] -> [a]
nub xs  =  go [] xs
  where
    {-@ go :: Ord a => acc:UniqueList a -> xs:List a -> UniqueList a @-}
    go     :: Ord a => [a] -> [a] -> [a]
    go acc []                       = acc
    go acc (x:xs)
      | not (x `member` (elts acc)) = x:acc
      | otherwise                   = acc

-- This is what we would need as a lemma: asserting that taking a tail preserves uniqueness
{-@ prop_tail :: xs:{v:UniqueList a | size v > 0} -> True @-}
prop_tail (_:xs) = unique xs 

-- Version of tail that respects uniqueness
{-@ uniqueTail :: xs:{v:UniqueList a | size v > 0} -> UniqueList a @-}
uniqueTail (_:xs) = xs 

-- Append gives a unique list when the unique lists are disjoint
{-@ append' :: 
  xs:UniqueList a 
  -> {ys:UniqueList a | Set_cap (elts xs) (elts ys) = empty} 
  -> {v:UniqueList a  | (Set_cup (elts xs) (elts ys) = elts v)
                        && (size v = size xs + size ys)} @-}
append'     :: [a] -> [a] -> [a]
append' [] ys     = ys
append' (x:xs) ys = x : append' xs ys

-- Naturals between I and J 
{-@ type Btwn I J = {v:Nat | I < J && I <= v && v < J} @-}

-- Safe head function on unique lists, which is also a measure
{-@ measure head' @-}
{-@ head'   :: {xs:UniqueList a | size xs > 0} -> a @-}
head'       :: [a] -> a
head' (x:_) =  x

-- Safe tail for unique lists, which is also a measure
{-@ measure tail' @-}
{-@ tail'    :: {xs:UniqueList a | size xs > 0} -> UniqueList a @-}
tail'        :: [a] -> [a]
tail' (_:xs) =  xs

-- Seems we need Reflection to easily prove this for unique lists
{-@ range :: i:Nat -> j:Nat -> [Btwn i j] / [j - i] @-}
range     :: Int -> Int -> [Int]
range i j
  | i < j     = i : range (i+1) j
  | otherwise = [] 

-- List reverse as a terminating uniqueness and set-preserving function 
{-@ reverse'    :: xs:UniqueList a -> {v:UniqueList a | elts v = elts xs} @-}
reverse'        :: [a] -> [a]
reverse' []     =  []
reverse' (x:xs) =  append' (reverse' xs) [x]

-- Test set membership on lists
{-@ predicate In X XS = member X (elts XS) @-}

-- Test disjointness on lists
{-@ predicate Disjoint XS YS = Set_cap (elts XS) (elts YS) = empty @-} 

-- List Zippers
{-@ 
  data Zipper a = Zipper { 
    focus :: a,
    left  :: {v:UniqueList a | not (In focus v)},
    right :: {v:UniqueList a | not (In focus v) && Disjoint v left}
  } 
@-}
data Zipper a = Zipper { focus :: a, left :: [a], right :: [a] } deriving (Show)

-- Measure the set of elements of a list zipper 
{-@ measure zipElts @-}
zipElts :: Ord a => Zipper a -> Set a 
zipElts (Zipper x left right) = singleton x `union` (elts left) `union` (elts right)

-- Zipper size as a measure
{-@ measure zipSize @-}
{-@ zipSize :: Zipper a -> Nat @-}
zipSize :: Zipper a -> Int
zipSize (Zipper x left right) = 1 + size left + size right

-- Create a valid list zipper on a non-empty unique list, ensuring that all elements are preserved 
{-@ differentiate    :: {xs:UniqueList a | size xs > 0} -> {v:Zipper a | zipElts v = elts xs} @-}
differentiate        :: [a] -> Zipper a
differentiate (x:xs) =  Zipper x [] xs

-- Recreate a non-empty unique list from the corresponding list zipper, ensuring all elements are preserved
{-@ integrate :: xs:Zipper a -> {v:UniqueList a | size v > 0 && elts v = zipElts xs} @-}
integrate     :: Zipper a -> [a]
integrate (Zipper x left right) = append' (reverse' left) (x : right)

-- Shift the zipper to the left, preserving zipper invariants and the underlying set. Note: we don't enforce
-- preservation of relative positions here, so this could still be more precise
{-@ focusLeft :: xs:Zipper a -> {v:Zipper a | zipElts v = zipElts xs} @-}
focusLeft     :: Zipper a -> Zipper a
focusLeft (Zipper x [] right) 
  = Zipper lastElt rest [] -- Wrap around to the end of the list so we have a total function
      where (lastElt : rest) = reverse' (x:right) 
focusLeft (Zipper x (l:ls) right) 
  = Zipper l ls (x : right)

-- Reverse a zipper
{-@ reverseZipper :: xs:Zipper a -> {v:Zipper a | zipElts v = zipElts xs} @-}
reverseZipper     :: Zipper a -> Zipper a
reverseZipper (Zipper x left right) = Zipper x right left  

-- Filter on unique lists. Filter always produces a subset
{-@ filter' :: (a -> Bool) -> xs:UniqueList a -> {v:UniqueList a | Set_sub (elts v) (elts xs)} @-}
filter' :: (a -> Bool) -> [a] -> [a]
filter' f [] = []
filter' f xs = if f y then y : filter' f ys else filter' f ys
  where (y, ys) = (head' xs, tail' xs)

-- Filter *unfocused* elements of a zipper - this is total
filterZipper :: (a -> Bool) -> Zipper a -> Zipper a 
filterZipper f (Zipper x left right) = Zipper x (filter' f left) (filter' f right)


