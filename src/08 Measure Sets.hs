import Prelude hiding (reverse,elem)

import Data.Set hiding (insert,size) -- Spec file from LH Prelude embeds Data.Set into SMT set theory solver

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
{-@ type ListSub a X = {v:[a] | Set_sub (elts v) X} @-}

-- A list whose element set is a union of those of two other lists
{-@ type ListUnion a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}

-- A list whose element set is exactly the element X together with the elements of the set Y
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

-- Statically verify that appending lists results in a list whose element set is the set union of the inputs
{-@ append :: xs:[a] -> ys:[a] -> ListUnion a xs ys @-} 
append           :: [a] -> [a] -> [a]
append [] ys     =  ys
append (x:xs) ys =  x : append xs ys

-- Reversing a list preserves the underlying set of elements. 
-- Note that we don't check that it's length-preserving here.
{-@ reverse :: xs:[a] -> ListEq a xs @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = append (reverse xs) [x]

-- Assert that one list is half the size of another
{-@ predicate IsHalfSize X Y = size X <= ((size Y)/2)+1 @-}

-- Assert that element set of one list is the union of two others
{-@ predicate IsUnion X Y Z = elts xs == Set_cup (elts X) (elts Y) @-}

-- Split a list in half by taking every other element. Ensures that the set union of the resulting
-- pair gives back the original list and that the sizes of the resulting lists are halved
{-@ halve      :: xs:[a] -> {v:([a],[a]) | IsHalfSize (fst v) xs && IsHalfSize (snd v) xs && IsUnion (fst v) (snd v) xs} @-}
halve          :: [a] -> ([a],[a])
halve (x:y:xs) =  (x : ys, y : zs) where (ys,zs) = halve xs
halve xs       =  (xs, [])

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
    {-@ insert :: x:a -> xs:[a] -> ListUn1 a x xs @-}
    insert :: Ord a => a -> [a] -> [a]
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
{-@ merge :: xs:List a -> ys:List a -> ListUnion a xs ys / [size xs + size ys] @-} 
merge :: Ord a => [a] -> [a] -> [a]
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
mergeSort xs = go (size xs) xs
  where
    {-@ go :: n:Nat -> xs:List a -> ListEq a xs @-}
    go    :: Ord a => Int -> [a] -> [a]
    go 0 xs = xs
    go _ [] = []
    go n xs = merge mys mzs
      where
        (ys,zs) = halve xs
        mys     = if size ys < 2 then ys else go (n-1) ys
        mzs     = if size zs < 2 then zs else go (n-1) zs

