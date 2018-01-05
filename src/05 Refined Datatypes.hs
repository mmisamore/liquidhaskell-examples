{-# language DeriveFoldable #-}
import Data.Ord
import Data.List hiding (insert)
import Data.Maybe 
import Data.Function
import Data.Foldable

-- Refinement type of Natural numbers
{-@ type Nat = {v:Int | v >= 0} @-}

-- Refinement type of integers between Lo and Hi (excluding Hi)
{-@ type Btwn Lo Hi = {v:Int | v >= Lo && v < Hi} @-}

-- Ensure that dimension is a Natural and every sparse element is at a valid index
-- Observe what we don't check: that each index occurs *at most* once
{-@ data Sparse a = SP { spDim :: Nat, spElems :: [(Btwn 0 spDim, a)] } @-}
data Sparse a = SP { spDim :: Int, spElems :: [(Int, a)] } deriving (Show)

okSP :: Sparse String
okSP = SP 5 [(0, "cat"), (2, "dog")]

{-badSP :: Sparse String-}
{-badSP = SP 5 [(0, "cat"), (6, "dog")]-}

-- Example of input validation to get data from the real world:
-- Seems we have to define the fold step manually for this to work instead of using "all" 
fromList :: Int -> [(Int, a)] -> Maybe (Sparse a)
fromList dim xs = 
  if dim >= 0 then foldl' step (Just (SP dim [])) xs
  else Nothing
  where 
    step Nothing _                  = Nothing
    step (Just (SP dim elts)) (i,e) = 
      if i >= 0 && i < dim then Just (SP dim ((i,e) : elts))
      else Nothing

-- Test it out
{-@ test1 :: Sparse String @-}
test1 = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]

-- Refinement type for Sparse vectors of bounded length N
{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

-- Safely add two sparse vectors if they have the same length
-- This assumes that groupBy and head are safe in this case, which is established in separate specifications
-- for those functions
{-@ plus :: x:Sparse a -> SparseN a (spDim x) -> SparseN a (spDim x) @-}
plus :: Num a => Sparse a -> Sparse a -> Sparse a
plus (SP dim elts1) (SP _ elts2) = SP dim elts3 
  where
    elts3        = map summarize . groupBy ((==) `on` fst) . sortBy (comparing fst) $ elts1 ++ elts2 
    summarize xs = (fst (head xs), sum (map snd xs))

-- Test it out
{-@ test2 :: SparseN Int 3 @-}
test2 :: Sparse Int
test2 = plus vec1 vec2
  where
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]

-- Refinement type of ordered lists
{-@ data IncList [incLen] a = Emp | (:<) { hd :: a, tl :: IncList {v:a | hd <= v } } @-}
{-@ LIQUID "--exact-data-con" @-}
data IncList a = Emp | (:<) { hd :: a, tl :: IncList a } deriving (Foldable)
infixr 9 :<

-- Nice display for IncLists
instance Show a => Show (IncList a) 
  where show = show . toList

-- Demonstrate that it works
okList :: IncList Int
okList = 1 :< 2 :< 3 :< Emp
{-notOkList :: IncList Int-}
{-notOkList = 1 :< 3 :< 2 :< Emp-}

-- Insertion sort that provably terminates with a sorted list
insertSort :: Ord a => [a] -> IncList a
insertSort xs = foldr insert Emp xs
  where
    insert :: Ord a => a -> IncList a -> IncList a
    insert x Emp       = x :< Emp 
    insert x (y :< ys) = if x <= y
                         then x :< y :< ys
                         else y :< insert x ys

-- Splitting function to support merge sort
{-@ split :: xs:[a] -> {p:([a],[a]) | len (fst p) + len (snd p) == len xs} @-}
split :: [a] -> ([a],[a])
split (x : y : zs) = (x : xs, y : ys)
  where (xs, ys) = split zs
split xs = (xs, [])

-- Given two lists that are already sorted, merge them and automatically prove that the result is sorted
{-@ merge :: xs:IncList a -> ys:IncList a -> IncList a / [incLen xs + incLen ys] @-}
merge :: Ord a => IncList a -> IncList a -> IncList a
merge xs Emp = xs
merge Emp ys = ys
merge (x :< xs) (y :< ys)
  | x <= y    = x :< merge xs (y :< ys)
  | otherwise = y :< merge (x :< xs) ys

-- A merge sort that provably terminates with a sorted list 
{-@ mergeSort :: [a] -> IncList a @-}
mergeSort :: Ord a => [a] -> IncList a
mergeSort xs = go (length xs) xs where
  {-@ go :: Nat -> [a] -> IncList a @-}
  go :: Ord a => Int -> [a] -> IncList a 
  go 0 [x] = x :< Emp
  go 0 _   = Emp
  go n xs  = merge (go (n-1) ys) (go (n-1) zs) 
               where (ys,zs) = split xs
 
{-@ measure incLen @-}
{-@ incLen :: IncList a -> Nat @-}
incLen :: IncList a -> Int
incLen Emp       = 0
incLen (_ :< xs) = 1 + incLen xs

{-@ measure incHd @-}
{-@ incHd :: {xs:IncList a | incLen xs > 0} -> a @-}
incHd :: IncList a -> a
incHd (x :< _) = x 

{-@ measure incLast @-}
{-@ incLast :: {xs:IncList a | incLen xs > 0} -> a @-}
incLast :: IncList a -> a
incLast (x :< Emp) = x
incLast (_ :< xs)  = incLast xs

{-@ measure lessThanEqHd @-}
lessThanEqHd :: Ord a => a -> IncList a -> Bool
lessThanEqHd _ Emp      = True
lessThanEqHd x (y :< _) = x <= y

{-@ measure greaterThanLast @-}
greaterThanLast :: Ord a => a -> IncList a -> Bool
greaterThanLast _ Emp        = True
greaterThanLast x (y :< Emp) = x > y
greaterThanLast x (_ :< ys)  = greaterThanLast x ys

-- Refined type for append guaranteeing that the pivot is in the correct place
{-@ append :: pivot:a 
             -> {xs:IncList a | greaterThanLast pivot xs}
             -> {ys:IncList a | lessThanEqHd pivot ys}
             -> IncList a @-}
append :: Ord a => a -> IncList a -> IncList a -> IncList a
append pivot Emp Emp             = pivot :< Emp
append pivot Emp (y :< ys)       = pivot :< y :< ys 
append pivot (x :< xs) Emp       = -- Implied by the precondition but we cannot (yet) prove it 
                                   if x < pivot 
                                   then x :< append pivot xs Emp 
                                   else Emp
append pivot (x :< xs) (y :< ys) = -- Implied by the precondition but we cannot (yet) prove it 
                                   if (greaterThanLast pivot xs && x < pivot)
                                   then x :< append pivot xs (y :< ys) 
                                   else Emp

-- A quicksort that provably terminates with a sorted list
quickSort :: Ord a => [a] -> IncList a
quickSort []     = Emp
quickSort (x:xs) = append x lessers' greaters'
  where 
    lessers   = quickSort [y | y <- xs, y < x]
    lessers'  = if greaterThanLast x lessers then lessers else Emp
    greaters  = quickSort [z | z <- xs, z >= x]
    greaters' = if lessThanEqHd x greaters then greaters else Emp 


-- Refinement type for binary search trees. These trees could be infinite
{-@ type BSTL a X = BST {v:a | v < X} @-}
{-@ type BSTR a X = BST {v:a | X < v} @-}
{-@ data BST a = Leaf | Node { root :: a, left :: BSTL a root, right :: BSTR a root } @-}
data BST a = Leaf | Node { root :: a, left :: BST a, right :: BST a } deriving (Foldable)

-- Example of what should be a valid tree. This is validated as safe by LH
okBST :: BST Int
okBST =  Node 6
             (Node 2
                 (Node 1 Leaf Leaf)
                 (Node 4 Leaf Leaf))
             (Node 9
                 (Node 7 Leaf Leaf)
                 Leaf)

-- Example of an invalid BST 
{-badBST =  Node 66-}
             {-(Node 4-}
                 {-(Node 1 Leaf Leaf)-}
                 {-(Node 69 Leaf Leaf))  -- Out of order, rejected-}
             {-(Node 99-}
                 {-(Node 77 Leaf Leaf)-}
                 {-Leaf)-}

-- Test membership in a binary search tree. This isn't guaranteed to terminate since the tree may be infinite
{-@ lazy member @-}
member :: Ord a => a -> BST a -> Bool
member x Leaf = False
member x (Node root left right)
  | x == root = True
  | x < root  = member x left
  | x > root  = member x right

-- Create a singleton tree. Terminates since there is one element 
singleton :: a -> BST a
singleton x = Node x Leaf Leaf

-- Insert an element into a tree. This isn't guaranteed to terminate since the tree may be infinite: we may
-- search for the correct location forever
{-@ lazy insert @-}
insert :: Ord a => a -> BST a -> BST a
insert x Leaf = singleton x
insert x t@(Node root left right)
  | x < root  = insert x left
  | x > root  = insert x right
  | otherwise = t

-- A refinement type specifying a minimum element and a tree consisting of elements greater than that element
{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt } @-}
data MinPair a = MP { mElt :: a, rest :: BST a }

{-@ measure bstEmpty @-}
bstEmpty :: BST a -> Bool
bstEmpty Leaf = True
bstEmpty _    = False
 
-- Delete the minimum element from any non-empty BST. This may not terminate since the tree may be infinite and
-- have no minimum element
{-@ lazy delMin @-}
{-@ delMin :: {t:BST a | not (bstEmpty t)} -> MinPair a @-}
delMin :: BST a -> MinPair a
delMin (Node root Leaf right) = -- Subtree to the left is empty so the min elt is the root 
                                MP root right 
delMin (Node root left right) = -- Subtree to the left is nonempty: the minimum is that of the left subtree and
                                -- a recursive call returns the rest of the left subtree
                                MP leftMin (Node root leftRest right) where
                                  MP leftMin leftRest = delMin left

-- Convert any list of totally ordered elements into a binary search tree
toBST :: (Ord a, Foldable t) => t a -> BST a
toBST = foldr insert Leaf

-- Claim to LH that code is unreachable
{-@ die :: {v:String | false} -> a @-}
die = error 

-- Convert any binary search tree to a sorted list. This may not terminate since the BST could be infinite.
{-@ lazy toIncList @-}
toIncList :: BST a -> IncList a
toIncList Leaf                   = Emp
toIncList (Node root left right) =
  case left of
    Leaf -> root :< (toIncList right)
    ls   -> leftMin :< (toIncList (Node root leftRest right)) 
              where MP leftMin leftRest = delMin left 

-- Sort by inserting elements into a binary search tree and then in-order traversing the tree
treeSort :: (Ord a, Foldable t) => t a -> IncList a
treeSort = toIncList . toBST

