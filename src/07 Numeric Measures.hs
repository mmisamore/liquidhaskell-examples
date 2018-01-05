import Prelude hiding (map,take,fst,snd,partition,concat)

{-@ data Vector a = V { vDim :: Nat, vElts :: ListN a vDim } @-}
{-@ vDim :: xs:Vector a -> {v:Nat | v == vDim xs} @-}
data Vector a = V { vDim :: Int, vElts :: [a] } deriving (Eq)

-- Show any vector containing showable elements
instance Show a => Show (Vector a) 
  where
    show (V _ xs) = show xs

-- Measure the size of finite lists. Note that this diverges on infinite lists even though it
-- passes the termination checker: the checker seems to assume that values under constructors are
-- smaller
{-@ measure size @-}
{-@ size :: xs:[a] -> {v:Nat | v == size xs} @-}
size        :: [a] -> Int
size []     =  0
size (x:xs) =  1 + size xs

-- Example of something that diverges on "size" since the structure is infinite
example = size (repeat 1)

{-@ measure notEmpty @-}
notEmpty    :: [a] -> Bool
notEmpty [] =  False
notEmpty _  =  True

-- Type alias for symmetry purposes
type List a = [a]

-- Lists of a fixed length
{-@ type ListN a N = {v:List a | size v = N} @-}

-- Lists whose lengths match that of some specified list
{-@ type ListX a X = ListN a (size X) @-}

-- Refinement type for map that says that it preserves the size of the input list
{-@ map :: (a -> b) -> xs:List a -> ListX b xs @-}
map          :: (a -> b) -> [a] -> [b]
map _ []     =  []
map f (x:xs) =  f x : map f xs

-- Refinement type of True booleans
{-@ type TRUE = {v:Bool | v} @-}

-- Verify that map preserves size
{-@ prop_map :: List a -> TRUE @-}
prop_map xs = size ys == size xs
  where ys = map id xs

-- Define a reverse function for lists that verifiably preserves size
{-@ reverse :: xs:List a -> ListX a xs @-}
reverse xs = go [] xs
  where
    {-@ go :: xs:List a -> ys:List a -> ListN a {size xs + size ys} / [size ys] @-}
    go            :: List a -> List a -> List a
    go acc []     =  acc
    go acc (x:xs) =  go (x:acc) xs

-- Flag code as unreachable
{-@ die :: {v:String | false} -> a @-}
die = error

-- Safe zipWith function: forces inputs to be the same length
{-@ zipWith' :: (a -> b -> c) -> xs:List a -> ys:ListX b xs -> ListX c xs @-}
zipWith'                 :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' f [] []         =  []
zipWith' f (x:xs) (y:ys) =  (f x y) : zipWith' f xs ys
zipWith' _ _ _           =  die "zipWith'"

-- Assert that the size of the first list equals the minimum size of the second and third list
{-@ predicate Smaller X Y Z = if (size Y) <= (size Z) then (size X) = (size Y) else (size X) = (size Z) @-}
 
-- A more permissive zip. Silently truncates elements when one list is longer than the other
{-@ unsafeZip :: xs:[a] -> ys:[b] -> {v:[(a,b)] | Smaller v xs ys} @-}
unsafeZip               :: [a] -> [b] -> [(a,b)]
unsafeZip [] _          =  []
unsafeZip _ []          =  []
unsafeZip (x:xs) (y:ys) =  (x,y) : unsafeZip xs ys

-- Middle ground: require that lists are the same length unless at least one of the two is empty 
{-@ zipOrNull :: 
    xs:[a] 
    -> {ys:[b] | (size xs > 0) && (size ys > 0) => size xs == size ys} 
    -> {v:[(a,b)] | Smaller v xs ys} @-}
zipOrNull       :: [a] -> [b] -> [(a, b)]
zipOrNull [] _  =  []
zipOrNull _ []  =  []
zipOrNull xs ys =  zipWith' (,) xs ys

{-@ test1 :: {v: _ | size v = 2} @-}
test1 = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | size v = 0} @-}
test2 = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | size v = 0} @-}
test3 = zipOrNull ["cat", "dog"] []

-- Refinement Type of lists whose lengths are at least N
{-@ type ListGE a N = {v:List a | size v >= N} @-}

-- Safe version of "take"
{-@ take' :: n:Nat -> ListGE a n -> ListN a n @-}
take'          :: Int -> [a] -> [a]
take' 0 _      =  []
take' n (x:xs) =  x : take' (n-1) xs
take' _ _      =  die "take'"

-- Safe version of "drop"
{-@ drop' :: n:Nat -> xs:ListGE a n -> ListN a {size xs - n} @-}
drop'          :: Int -> [a] -> [a]
drop' 0 xs     =  xs
drop' n (_:xs) =  drop' (n-1) xs
drop' _ _      =  die "drop'"

-- Try it out. It works!
{-@ test4 :: ListN String 2 @-}
test4 = drop' 1 ["cat", "dog", "mouse"]

-- Refinement Type of lists whose lengths are at most N
{-@ type ListLE a N = {v:List a | size v <= N} @-} 

-- Less safe version of take: may take fewer elements than requested 
{-@ take :: n:Nat -> xs:List a -> {v:List a | ((n <= size xs) => size v == n)
                                           && ((n > size xs)  => size v == size xs)} @-}
take :: Int -> [a] -> [a]
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ test5 :: [ListN String 2] @-}
test5 = [ take 2  ["cat", "dog", "mouse"]
        , take 20 ["cow", "goat"]        ]


{-@ predicate Sum2 X N = size (fst X) + size (snd X) = N @-}

-- Sample partition function
{-@ partition :: _ -> xs:_ -> {v:_ | Sum2 v (size xs)} @-}
partition          :: (a -> Bool) -> [a] -> ([a], [a])
partition _ []     =  ([], [])
partition f (x:xs)
  | f x            =  (x:ys, zs)
  | otherwise      =  (ys, x:zs)
  where
    (ys, zs)       =  partition f xs

{-@ measure fst' @-} 
fst' :: (a,b) -> a 
fst' (x, _) = x

{-@ measure snd' @-}
snd' :: (a, b) -> b
snd' (_, y) = y

-- The list append function is guaranteed to add the sizes together 
{-@ append :: xs:List a -> ys:List a -> ListN a {size xs + size ys} @-}
append           :: [a] -> [a] -> [a]
append [] ys     =  ys
append (x:xs) ys =  x : append xs ys

-- Specify a length-preserving quicksort
{-@ quickSort :: xs:List a -> ListX a xs @-}
{-@ lazy quickSort @-}
quickSort        :: Ord a => [a] -> [a]
quickSort []     =  []
quickSort (x:xs) =  append (quickSort lessers) (quickSort greaters)
  where 
    (lessers, greaters) = partition (<= x) (x:xs)

{-@ test10 :: ListN String 2 @-}
test10 = quickSort test4

okVect = V 2 [10,20]
-- badVect = V 2 [10, 20, 30]


-- Non-empty vectors
{-@ type VectorNE a = {v:Vector a | vDim v > 0} @-}

-- Vectors of fixed size
{-@ type VectorN a N = {v:Vector a | vDim v == N} @-}

-- Vectors with same size as another vector
{-@ type VectorX a X = {v:Vector a | vDim v == vDim X} @-}

-- The empty vector
{-@ vEmpty :: VectorN a 0 @-}
vEmpty     :: Vector a
vEmpty     =  V 0 []

-- Length-respecting cons for sized vectors
{-@ vCons        :: a -> xs:Vector a -> VectorN a {vDim xs + 1} @-}
vCons            :: a -> Vector a -> Vector a
vCons x (V n xs) =  V (n+1) (x:xs)

-- Safe head for non-empty vectors
{-@ vHead          :: VectorNE a -> a @-}
vHead              :: Vector a -> a
vHead (V _ (x:xs)) =  x
vHead _            =  die "vHead"

-- Safe tail for non-empty vectors. Records the change in length.
{-@ vTail          :: xs:VectorNE a -> {v:Vector a | vDim v = vDim xs - 1} @-}
vTail              :: Vector a -> Vector a
vTail (V n (_:xs)) =  V (n-1) xs
vTail _            =  die "vTail"

-- Size-preserving flip map for vectors
{-@ for        :: xs:Vector a -> (a -> b) -> {v:Vector b | vDim v == vDim xs} @-}
for            :: Vector a -> (a -> b) -> Vector b
for (V n xs) f =  V n (map f xs)

-- Binary pointwise operations. Requires that inputs are compatible dimensions
{-@ vBin                  :: (a -> b -> c) -> xs:Vector a -> ys:VectorX b xs -> VectorX c xs @-}
vBin                      :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
vBin op (V n xs) (V _ ys) =  V n (zipWith' op xs ys)

-- Safe dot product of vectors
{-@ dotProduct :: xs:Vector a -> ys:VectorX a xs -> a @-}
dotProduct :: Num a => Vector a -> Vector a -> a
dotProduct xs ys = sum (vElts (vBin (*) xs ys))

-- Safely create a vector from a list
{-@ vecFromList :: xs:[a] -> {v:Vector a | vDim v == size xs} @-}
vecFromList     :: [a] -> Vector a
vecFromList xs  =  V (size xs) xs

-- Concatenate a sized list of sized lists together using size-preserving append
{-@ concat          :: m:Nat -> n:Nat -> ListN (ListN a m) n -> ListN a {m * n} / [n] @-}
concat              :: Int -> Int -> [[a]] -> [a]
concat m 0 []       =  []
concat m n ([]:xss) =  concat m (n-1) xss
concat m n (xs:xss) =  append xs (concat m (n-1) xss)

-- Dimension-safe flattening function
{-@ flatten          :: m:Nat -> n:Nat -> VectorN (VectorN a m) n -> VectorN a {m * n} @-}
flatten              :: Int -> Int -> Vector (Vector a) -> Vector a
flatten m n (V _ cs) =  V (n * m) (concat m n rss)
  where
    -- Extract the row entries for each column into a list of lists
    rss = [rs | (V _ rs) <- cs]

-- The (flattened) outer product of two vectors
{-@ outer :: xs:Vector a -> ys:Vector a -> VectorN a {vDim xs * vDim ys} @-}
outer :: Num a => Vector a -> Vector a -> Vector a 
outer xs ys = flatten (vDim xs) (vDim ys) vss
  where
    vss = for ys $ \y ->
            for xs $ \x ->
              x * y

-- The refinement type of positive integers
{-@ type Pos = {v:Nat | v > 0} @-}

-- Dimension-safe matrices without full dependent types
{-@ data Matrix a = M { mRow :: Pos, mCol :: Pos, mElts :: VectorN (VectorN a mRow) mCol } @-}
data Matrix a = M { mRow :: Int, mCol :: Int, mElts :: Vector (Vector a) } deriving (Eq, Show)

-- Matrices with fixed dimensions
{-@ type MatrixN a R C = {v:Matrix a | (mRow v == R) && (mCol v == C)} @-}

-- Demo manually building a sized matrix
{-@ ok23 :: MatrixN Int 2 3 @-}
ok23 :: Matrix Int
ok23 = M 2 3 (V 3 [
                (V 2 [1,4]),
                (V 2 [2,5]),
                (V 2 [3,6])
               ]
             )

-- Guaranteed-safe constructor for matrices as sized lists of sized lists
{-@ matFromList :: m:Pos -> n:Pos -> ListN (ListN a m) n -> MatrixN a m n @-}
matFromList :: Int -> Int -> [[a]] -> Matrix a
matFromList m n cols = M m n (vecFromList (map vecFromList cols))

-- Demo building a sized matrix from a list
{-@ ok23' :: MatrixN Int 2 3 @-}
ok23' :: Matrix Int
ok23' = matFromList 2 3 [[1,4],[2,5],[3,6]]

-- Construct a sized matrix from a sized vector as a single column
{-@ singleCol :: m:Pos -> VectorN a m -> MatrixN a {m} 1 @-}
singleCol :: Int -> Vector a -> Matrix a
singleCol m xs = M m 1 (V 1 [xs]) 

-- Cons a sized column onto the front of a sized matrix assuming compatible dimensions
{-@ consCol :: m:Pos -> k:Pos -> VectorN a m -> MatrixN a m k -> MatrixN a {m} {k+1} @-}
consCol :: Int -> Int -> Vector a -> Matrix a -> Matrix a
consCol m k col (M _ _ xs) = M m (k+1) (vCons col xs)

{-@ unconsRow :: m:Pos -> n:Pos -> VectorN (VectorN a m) n -> (VectorN a n, VectorN (VectorN a {m-1}) n) @-}
unconsRow :: Int -> Int -> Vector (Vector a) -> (Vector a, Vector (Vector a))
unconsRow m n (V _ css) = (vHeads m n css, vTails m n css)
  where
    {-@ vHeads :: m:Pos -> n:Pos -> ListN (VectorN a m) n -> VectorN a n @-}
    vHeads :: Int -> Int -> [Vector a] -> Vector a
    vHeads _ _ xs = vecFromList (map vHead xs)

    {-@ vTails :: m:Pos -> n:Pos -> ListN (VectorN a m) n -> VectorN (VectorN a {m-1}) n @-}
    vTails :: Int -> Int -> [Vector a] -> Vector (Vector a)
    vTails _ _ xs = vecFromList (map vTail xs)

-- Safely transpose a sized matrix. Guarantees correct output dimensions
{-@ transpose :: m:Pos -> n:Pos -> MatrixN a m n -> MatrixN a n m @-}
transpose :: Int -> Int -> Matrix a -> Matrix a 
transpose m n (M _ _ cols) = 
  if m > 1 
    -- Transpose the rest and add the old first row as the first column
    then consCol n (m-1) firstRow (transpose (m-1) n (M (m-1) n restRows))
    -- m was 1 so just return a single-column matrix
    else singleCol n firstRow 
  where
    (firstRow, restRows) = unconsRow m n cols

