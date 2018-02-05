import Prelude hiding (max)
import qualified Data.Set as S 

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

-- The empty AVL tree. It has an empty set of elements.
{-@ empty :: {t:AVLN a 0 | Set_emp (elems t)} @-}
empty     :: AVL a
empty     =  Leaf

-- Build an AVL tree from a single value. The set of elements is just a singleton.
{-@ singleton :: x:a -> {t:AVLN a 1 | elems t = Set_sng x} @-}
singleton     :: a -> AVL a
singleton x   =  Node x empty empty 1

-- Build an AVL tree from a key sandwiched between two existing ones, assuming they are mutually balanced
{-@ mkNode          :: key:a -> left:AVLL a key -> {right:AVLR a key | isBalanced left right 1} -> 
                       {v:AVL a | realHeight v = nodeHeight left right && NodeAdd v key left right} @-}
mkNode              :: a -> AVL a -> AVL a -> AVL a
mkNode x left right =  Node x left right h
  where h           =  nodeHeight left right

-- Get the height of an AVL tree, which is guaranteed to be the real height due to the above refinement type
{-@ measure getHeight @-}
{-@ getHeight            :: t:AVL a -> {v:Nat | v = realHeight t} @-}
getHeight Leaf           =  0
getHeight (Node _ _ _ h) =  h

-- Ensure the invariant is satisfied - this is required due to a bug in LH 
{-@ invariant {v:AVL a | getHeight v = realHeight v} @-}

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

-- Rebalance the LeftBig, NoHeavy case. Total height of l + 1 remains the same.
{-@ balL0 :: x:a -> l:{AVLL a x | noHeavy l} -> r:{AVLR a x | leftBig l r} -> 
             {t:AVLN a {realHeight l + 1} | NodeAdd t x l r} @-}
balL0 x l@(Node lv ll lr _) r = mkNode lv ll (mkNode x lr r)

-- Rebalance the RightBig, NoHeavy case. Total height of r + 1 remains the same.
{-@ balR0 :: x:a -> l:AVLL a x -> r:{AVLR a x | noHeavy r && rightBig l r} -> 
             {t:AVLN a {realHeight r + 1} | NodeAdd t x l r} @-}
balR0 x l r@(Node rv rl rr _) = mkNode rv (mkNode x l rl) rr 

-- Rebalance the LeftBig, LeftHeavy case. Total height of l + 1 goes to new height l.
{-@ balLL :: x:a -> l:{AVLL a x | leftHeavy l} -> r:{AVLR a x | leftBig l r} -> 
             {t:AVLT a l | NodeAdd t x l r} @-}
balLL x l@(Node lv ll lr _) r = mkNode lv ll (mkNode x lr r)

-- Rebalance the RightBig, RightHeavy case. Total height of r + 1 goes to new height r.
{-@ balRR :: x:a -> l:AVLL a x -> r:{AVLR a x | rightHeavy r && rightBig l r} ->
             {t:AVLT a r | NodeAdd t x l r} @-}
balRR x l r@(Node rv rl rr _) = mkNode rv (mkNode x l rl) rr 

-- Rebalance the LeftBig, RightHeavy case. Total height of l + 1 goes to new height l.
{-@ balLR :: x:a -> l:{AVLL a x | rightHeavy l} -> r:{AVLR a x | leftBig l r} -> 
             {t:AVLT a l | NodeAdd t x l r} @-}
balLR x l@(Node lv ll (Node lrv lrl lrr _) _) r = mkNode lrv (mkNode lv ll lrl) (mkNode x lrr r)

-- Rebalance the RightBig, LeftHeavy case. Total height of r + 1 goes to new height r.
{-@ balRL :: x:a -> l:AVLL a x -> r:{AVLR a x | leftHeavy r && rightBig l r} -> 
             {t:AVLT a r | NodeAdd t x l r} @-}
balRL x l r@(Node rv (Node rlv rll rlr _) rr _) = mkNode rlv (mkNode x l rll) (mkNode rv rlr rr)

-- T is the same height as S or one more than S
{-@ predicate EqOrUp T S = (realHeight T = realHeight S) || (realHeight T = realHeight S + 1) @-}

-- First version of inserting an element into an AVL tree, with guaranteed termination
{-@ insert                :: {z:Nat | z = 1} -> x:a -> s:AVL a -> {t:AVL a | EqOrUp t s} / [realHeight s, z] @-}
insert                    :: Ord a => Int -> a -> AVL a -> AVL a
insert _ x Leaf           =  singleton x
insert _ x s@(Node y _ _ _)
  | x < y                 =  insL 0 x s
  | x > y                 =  insR 0 x s
  | otherwise             =  s 

-- Helper for inserting on the left, with guaranteed termination
{-@ insL :: {z:Nat | z = 0} -> x:a -> {l:AVL a | x < key l && realHeight l > 0} -> 
            {t:AVL a | EqOrUp t l} / [realHeight l, z] @-}
insL :: Ord a => Int -> a -> AVL a -> AVL a
insL _ x (Node y l r _) 
  | leftBig l' r && leftHeavy l'  = balLL y l' r
  | leftBig l' r && rightHeavy l' = balLR y l' r
  | leftBig l' r                  = balL0 y l' r
  | otherwise                     = mkNode y l' r 
  where
    l' = insert 1 x l

-- Helper for inserting on the right, with guaranteed termination
{-@ insR :: {z:Nat | z = 0} -> x:a -> {r:AVL a | x > key r && realHeight r > 0} -> 
            {t:AVL a | EqOrUp t r} / [realHeight r, z] @-}
insR     :: Ord a => Int -> a -> AVL a -> AVL a
insR _ x (Node y l r _)
  | rightBig l r' && leftHeavy r'  = balRL y l r'
  | rightBig l r' && rightHeavy r' = balRR y l r'
  | rightBig l r'                  = balR0 y l r'
  | otherwise                      = mkNode y l r'
  where
    r' = insert 1 x r

-- Combined postcondition for all rebalancing cases 
{-@ predicate UpMax T L R = (realHeight T = max (realHeight L) (realHeight R)) ||
                            (realHeight T = 1 + max (realHeight L) (realHeight R)) @-}

 
-- If the subtrees were aleady balanced, T should just be the join of them
{-@ predicate IdemBal T L R = (isBalanced L R 1 ==> realHeight T = nodeHeight L R) @-}

-- Generic rebalancing helper: assuming a tree is out of balance after insert/delete, correct the imbalance
{-@ bal :: x:a -> l:AVLL a x -> {r:AVLR a x | isBalanced l r 2} -> 
           {t:AVL a | UpMax t l r && IdemBal t l r && NodeAdd t x l r} @-}
bal     :: a -> AVL a -> AVL a -> AVL a
bal x l r
  | leftBig  l r && leftHeavy l  =  balLL x l r
  | leftBig  l r && rightHeavy l =  balLR x l r
  | leftBig  l r                 =  balL0 x l r
  | rightBig l r && leftHeavy r  =  balRL x l r
  | rightBig l r && rightHeavy r =  balRR x l r
  | rightBig l r                 =  balR0 x l r
  | otherwise                    =  mkNode x l r

-- A cleaner version of insert that makes use of the generic rebalancing function above
{-@ insert' :: Ord a => x:a -> s:AVL a -> {t:AVL a | EqOrUp t s && Add t x s} / [realHeight s] @-}
insert'     :: Ord a => a -> AVL a -> AVL a
insert' x Leaf             = singleton x
insert' x s@(Node y l r _)
  | x < y                  = bal y (insert' x l) r
  | x > y                  = bal y l (insert' x r)
  | otherwise              = s

-- T is the same height as S or one less than S
{-@ predicate EqOrDown T S = EqOrUp S T @-}

-- Lemma: If x < y and s is an AVLR for y then x cannot be an element of s
{-@ lemNotEltRight :: x:a -> {y:a | x < y} -> s:AVLR a y -> {v:Bool | not (Set_mem x (elems s))} / [realHeight s] @-}
lemNotEltRight     :: a -> a -> AVL a -> Bool
lemNotEltRight x y Leaf           = True 
lemNotEltRight x y (Node z l r _) = assert (lemNotEltRight x y l) $ assert (lemNotEltRight x y r) $ True 

-- Lemma: If x > y and s is an AVLL for y then x cannot be an element of s
{-@ lemNotEltLeft :: x:a -> {y:a | x > y} -> s:AVLL a y -> {v:Bool | not (Set_mem x (elems s))} / [realHeight s] @-}
lemNotEltLeft     :: a -> a -> AVL a -> Bool
lemNotEltLeft x y Leaf           = True 
lemNotEltLeft x y (Node z l r _) = assert (lemNotEltLeft x y l) $ assert (lemNotEltLeft x y r) $ True 

-- Delete a value from an AVL tree
{-@ delete              :: Ord a => x:a -> s:AVL a -> {t:AVL a | EqOrDown t s && not (Set_mem x (elems t))} / [realHeight s] @-}
delete                  :: Ord a => a -> AVL a -> AVL a
delete x Leaf           =  Leaf
delete x (Node y l r _)
  | x < y               =  assert (lemNotEltRight x y r) $ bal y (delete x l) r
  | x > y               =  assert (lemNotEltLeft x y l)  $ bal y l (delete x r)
  | otherwise           =  merge x l r

-- Lemma: If r is an AVLR for x, then x is not an element of r
{-@ lemAVLR              :: x:a -> r:AVLR a x -> {v:Bool | not (Set_mem x (elems r))} / [realHeight r] @-}
lemAVLR                  :: a -> AVL a -> Bool
lemAVLR x Leaf           =  True
lemAVLR x (Node y l r _) =  assert (lemAVLR x l) $ assert (lemAVLR x r) $ True

-- Lemma: If l is an AVLL for x, then x is not an element of l
{-@ lemAVLL              :: x:a -> l:AVLL a x -> {v:Bool | not (Set_mem x (elems l))} / [realHeight l] @-}
lemAVLL                  :: a -> AVL a -> Bool
lemAVLL x Leaf           =  True
lemAVLL x (Node y l r _) =  assert (lemAVLL x l) $ assert (lemAVLL x r) $ True

-- Merge function to support delete: make the min element of the right subtree the new root
{-@ merge      :: x:a -> l:AVLL a x -> {r:AVLR a x | isBalanced l r 1} -> {t:AVL a | UpMax t l r && not (Set_mem x (elems t))} @-}
merge          :: a -> AVL a -> AVL a -> AVL a
merge x Leaf r =  assert (lemAVLR x r) $ r
merge x l Leaf =  assert (lemAVLL x l) $ l
merge x l r    =  assert (lemAVLL x l) $ assert (lemAVLR x r) $ bal y l r'
  where
    (y,r')     =  getMin r

-- Get the minimum element of any nonempty AVL tree, together with the rest of the tree
{-@ getMin :: {t:AVL a | realHeight t > 0} -> 
              (y::a, {t':AVL {x:a | x > y} | EqOrDown t' t && Add t y t'}) / [realHeight t] @-}
getMin                     :: AVL a -> (a, AVL a)
getMin t@(Node y Leaf r _) =  (y,r)
getMin t@(Node y l r _)    =  (y', bal y l' r)
  where
    (y',l')                =  getMin l

-- Get the set of elements of any AVL tree in the SMT logic 
{-@ measure elems @-}
{-@ lazy elems @-}
{-@ elems            :: s:AVL a -> S.Set a @-}
elems                :: Ord a => AVL a -> S.Set a
elems Leaf           =  S.empty
elems (Node x l r _) =  S.singleton x `S.union` elems l `S.union` elems r

-- Test for membership in an AVL tree. The SMT logic guarantees that we do the right thing here
{-@ member :: Eq a  => x:a -> t:AVL a -> {v:Bool | v  <=> Set_mem x (elems t)} / [realHeight t] @-}
member     :: Eq a  => a -> AVL a -> Bool
member x Leaf           = False
member x (Node y l r _) = (x == y) || member x l || member x r

-- Assert that T has the same elements as S together with X
{-@ predicate Add T X S = (elems T = Set_cup (Set_sng X) (elems S)) @-}

-- Assert that T has the same elements as S except X
{-@ predicate Del T S X = (elems T = Set_dif (elems S) (Set_sng X)) @-}

-- Assert that T has the same elements as the union of L and R, possibly with one more
{-@ predicate NodeAdd T X L R = (elems T = Set_cup (Set_sng X) (Set_cup (elems L) (elems R))) @-}


