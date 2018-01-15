import Prelude hiding (replicate,reverse,take)

-- Size measure for ordinary lists
{-@ measure realSize @-}
{-@ realSize    :: [a] -> Nat @-}
realSize        :: [a] -> Int
realSize []     =  0
realSize (x:xs) =  1 + realSize xs

-- Sized lists
{-@ data SList a = SL { size :: Nat, elems :: {v:[a] | realSize v = size} } @-}
data SList a     = SL { size :: Int, elems :: [a] } deriving (Show)

-- Safely convert any (finite) list to a sized list
{-@ fromList    :: xs:[a] -> {v:SList a | size v = len xs} @-}
fromList        :: [a] -> SList a
fromList []     =  nil
fromList (x:xs) =  cons x (fromList xs)

-- Example valid sized list
{-@ okList :: SListN String 1 @-}
okList     =  SL 1 ["cat"]

-- Example invalid sized list
-- badList = SL 1 []

-- Sized lists of a fixed size
{-@ type SListN a N = {v:SList a | size v = N} @-}

-- The empty sized list
{-@ nil :: SListN a 0 @-}
nil     =  SL 0 []

-- Add an element to a sized list
{-@ cons :: x:a -> xs:SList a -> SListN a {size xs + 1} @-}
cons     :: a -> SList a -> SList a
cons x (SL size xs) =  SL (size + 1) (x : xs)

-- Sized tail
{-@ tl :: {xs:SList a | size xs > 0} -> SListN a {size xs - 1} @-}
tl     :: SList a -> SList a
tl (SL size (_:xs)) =  SL (size - 1) xs

-- Sized head
{-@ hd :: {xs:SList a | size xs > 0} -> a @-}
hd     :: SList a -> a
hd (SL size (x:_)) =  x

-- Example of using sized head
okHead = hd okList

-- Example showing stuff is also rejected
-- badHead = hd (tl okList)

-- Sized lists with an upper bound
{-@ type SListLE a N = {v:SList a | size v <= N} @-}

-- An Okasaki queue with size invariant that the front list is at least as long as the back list
{-@ data Queue a = Q { front :: SList a, back :: SListLE a {size front} } @-}
data Queue a     = Q { front :: SList a, back :: SList a } deriving (Show)

-- Queue examples
okQueue     = Q okList nil
-- badQueue = Q nil okList

-- The size of a Queue
{-@ measure queueSize @-}
{-@ queueSize :: Queue a -> Nat @-}
queueSize     :: Queue a -> Int
queueSize (Q front back) = size front + size back

-- Remove an element from the front of the queue
{-@ remove :: {xs:Queue a | queueSize xs > 0} -> (a, {v:Queue a | queueSize v = queueSize xs - 1}) @-}
remove :: Queue a -> (a, Queue a)
remove (Q front back) = (hd front, makeQueue (tl front) back)

-- Sized Queues
{-@ type QueueN a N = {v:Queue a | queueSize v = N} @-}

-- Sized empty queue
{-@ empty :: QueueN a 0 @-}
empty     :: Queue a
empty     =  Q nil nil

-- Sized non-empty queue
{-@ example2Q :: QueueN Int 2 @-}
example2Q     :: Queue Int
example2Q     =  Q (cons 1 (cons 2 (nil))) nil

-- Insert an element to the back of the queue
{-@ insert :: x:a -> xs:Queue a -> {v:Queue a | queueSize v = queueSize xs + 1} @-}
insert     :: a -> Queue a -> Queue a
insert x (Q front back) = makeQueue front (cons x back)

-- Produce a queue of length n from element a
{-@ replicate :: n:Nat -> a -> QueueN a n @-}
replicate     :: Int -> a -> Queue a
replicate 0 x = empty
replicate n x = insert x (replicate (n-1) x)

-- Example of correct implementation for spec
{-@ y3 :: QueueN _ 3 @-}
y3 = replicate 3 "Yeah!"

-- Show that the spec rejects some implementations
-- {-@ y2 :: QueueN _ 3 @-}
{-y2 = replicate 2 "No!"-}

-- Enforce the Queue invariant. Should be called when the back exceeds the front by at most 1 
{-@ makeQueue :: front:SList a
              -> {back:SList a | size back <= size front + 1}
              -> QueueN a {size front + size back}
@-}
makeQueue     :: SList a -> SList a -> Queue a
makeQueue front back = if size front >= size back then Q front back
                      else Q (append front (reverse back)) nil 

-- Append for sized lists. Guarantees the output is the correct size
{-@ append :: xs:SList a -> ys:SList a -> {v:SList a | size v = size xs + size ys} / [size xs] @-}
append     :: SList a -> SList a -> SList a
append xs ys = if size xs == 0 then ys 
               else cons (hd xs) (append (tl xs) ys)

-- Reverse for sized lists. Guarantees output is the same size as the input
{-@ reverse :: xs:SList a -> {v:SList a | size v = size xs} @-}
reverse     :: SList a -> SList a
reverse xs  =  go nil xs
  where
    {-@ go :: acc:SList a -> xs:SList a -> {v:SList a | size v = size acc + size xs} / [size xs] @-}
    go     :: SList a -> SList a -> SList a
    go acc xs = if size xs == 0 then acc
                else go (hd xs `cons` acc) (tl xs)

-- Safely take the first n elements from a Queue
{-@ take  :: n:Nat -> {xs:Queue a | queueSize xs >= n} -> {v:Queue a | queueSize v = n} @-}
take      :: Int -> Queue a -> Queue a
take n xs =  go n xs empty
  where
    {-@ go  :: n:Nat
            -> {xs:Queue a | queueSize xs >= n}
            -> acc:Queue a                  
            -> {v:Queue a  | queueSize v = queueSize acc + n}
    @-}
    go     :: Int -> Queue a -> Queue a -> Queue a
    go 0 _ acc  = acc
    go n xs acc = if queueSize xs == 0 
                  then acc
                  else go (n-1) t (insert h acc) 
                    where (h,t) = remove xs

