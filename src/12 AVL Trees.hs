import Prelude hiding (max)

-- A Tree is either a Leaf or an Internal node with some data
{-@ data AVL a =
  Leaf
  | Node {
    key    :: a,
    left   :: AVLL a key,
    right  :: {v:AVLR a key | isBalanced left v 1},
    height :: {v:Nat | isRealHeight v left right}
  }
@-}
data AVL a = Leaf | Node { key :: a, left :: AVL a, right :: AVL a, height :: Int } deriving (Show)

-- Trees containing values less than X
{-@ type AVLL a X = AVL {v:a | v < X} @-}

-- Trees containing values greater than X
{-@ type AVLR a X = AVL {v:a | v > X} @-}

-- Baseline measure of the real height of a tree
{-@ measure realHeight @-}
{-@ lazy realHeight @-}
{-@ realHeight                   :: AVL a -> Nat @-}
realHeight                       :: AVL a -> Int
realHeight Leaf                  =  0
realHeight (Node _ left right _) =  nodeHeight left right

-- Compute the height of a Node from its left and right subtrees
{-@ inline nodeHeight @-}
{-@ nodeHeight        :: AVL a -> AVL a -> Nat @-}
nodeHeight            :: AVL a -> AVL a -> Int
nodeHeight left right =  1 + max (realHeight left) (realHeight right)

-- The max of two naturals. We have to inline this function so the above measure can see it
{-@ inline max @-}
{-@ max :: Nat -> Nat -> Nat @-}
max     :: Int -> Int -> Int
max x y =  if x > y then x else y

-- Test if the stored height of a Node equals its real height
{-@ inline isRealHeight @-}
{-@ isRealHeight          :: h:Nat -> left:AVL a -> right:AVL a -> Bool @-}
isRealHeight              :: Int -> AVL a -> AVL a -> Bool
isRealHeight h left right =  h == nodeHeight left right

-- Test if a tree is balanced to within a height difference of n
{-@ inline isBalanced @-}
{-@ isBalanced          :: left:AVL a -> right:AVL a -> n:Nat -> Bool @-}
isBalanced              :: AVL a -> AVL a -> Int -> Bool
isBalanced left right n =  (0 - n) <= d && d <= n
  where d               =  (realHeight left) - (realHeight right)

-- Refinement type of trees of a given height
{-@ type AVLN a N = {v:AVL a | realHeight v = N} @-}

-- Refinement type of trees whose height matches another tree
{-@ type AVLT a T = AVLN a {realHeight T} @-}

-- The empty AVL tree
{-@ empty :: AVLN a 0 @-}
empty     :: AVL a
empty     =  Leaf

-- Build an AVL tree from a single value 
{-@ singleton :: a -> AVLN a 1 @-}
singleton     :: a -> AVL a
singleton x   =  Node x empty empty 1

-- Build an AVL tree from a key sandwiched between two existing ones, assuming they are mutually balanced
{-@ mkNode          :: key:a -> left:AVLL a key -> {right:AVLR a key | isBalanced left right 1} -> {v:AVL a | realHeight v = nodeHeight left right} @-}
mkNode              :: a -> AVL a -> AVL a -> AVL a
mkNode x left right =  Node x left right h
  where h           =  nodeHeight left right

-- Get the height of an AVL tree, which is guaranteed to be the real height due to the above refinement type
{-@ measure getHeight @-}
{-@ getHeight            :: t:AVL a -> {v:Nat | v = realHeight t} @-}
getHeight Leaf           =  0
getHeight (Node _ _ _ h) =  h

-- Left subtree is 2 bigger in height. This is a case requiring rebalancing assuming a tolerance of 1
{-@ inline leftBig @-}
{-@ leftBig        :: left:AVL a -> right:AVL a -> Bool @-}
leftBig            :: AVL a -> AVL a -> Bool
leftBig left right =  getHeight left - getHeight right == 2

-- Right subtree is 2 bigger in height. This is the other case requiring rebalancing assuming a tolerance of 1
{-@ inline rightBig @-}
{-@ rightBig        :: left:AVL a -> right:AVL a -> Bool @-}
rightBig            :: AVL a -> AVL a -> Bool
rightBig left right =  getHeight right - getHeight left == 2

-- Define the Balance Factor for any subtree
{-@ measure balanceFactor @-}
balanceFactor                       :: AVL a -> Int
balanceFactor Leaf                  =  0
balanceFactor (Node _ left right _) =  getHeight left - getHeight right

-- Define the three Balance Factor cases of interest
{-@ inline leftHeavy @-}
leftHeavy t = balanceFactor t > 0

{-@ inline rightHeavy @-}
rightHeavy t = balanceFactor t < 0

{-@ inline noHeavy @-}
noHeavy t = balanceFactor t == 0

-- Ensure code is unreachable
{-@ die :: {s:String | false} -> a @-}
die :: String -> a
die = error

-- For use with Lemmas 
assert _ y = y

-- Measure to distinguish Leafs from Nodes
{-@ measure isNode @-}
isNode      :: AVL a -> Bool
isNode Leaf =  False
isNode _    =  True

-- This definition from the tutorial doesn't pass the SMT solver:
-- {-@ balL0 :: x:a
--           -> l:{AVLL a x | noHeavy l}
--           -> r:{AVLR a x | leftBig l r}
--           -> AVLN a {realHeight l + 1}
-- @-}
-- balL0 v (Node lv ll lr _) r = mkNode lv ll (mkNode v lr r)

