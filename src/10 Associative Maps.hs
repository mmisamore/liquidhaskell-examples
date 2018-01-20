import Prelude hiding (null,maximum)
import Data.Set hiding (elems)

-- A map from keys to values 
{-@ data Map k v = 
  Empty 
  | Node { 
      key   :: k,
      value :: v,
      left  :: Map {k':k | k' < key} v,
      right :: Map {k':k | k' > key} v
  }
@-}
data Map k v = Empty | Node { key :: k, value :: v, left :: Map k v, right :: Map k v }

-- Measure the set of keys of a map
{-@ measure keys @-}
{-@ lazy keys @-}
{-@ keys                   :: Map k v -> Set k @-}
keys                       :: Ord k => Map k v -> Set k
keys Empty                 =  empty
keys (Node k _ left right) =  singleton k `union` keys left `union` keys right

-- The empty map, with no keys 
{-@ emptyMap :: {m:Map k v | Set_emp (keys m)} @-}
emptyMap     :: Map k v
emptyMap     =  Empty 

-- Measure the size of a map to help the termination checker
{-@ measure mapSize @-}
{-@ lazy mapSize @-}
{-@ mapSize                   :: Map k v -> Nat @-}
mapSize                       :: Map k v -> Int
mapSize Empty                 =  0
mapSize (Node _ _ left right) =  1 + mapSize left + mapSize right

-- Set a value at a key 
{-@ set :: k:k -> v:v -> m:Map k v -> {v:Map k v | keys v = Set_cup (Set_sng k) (keys m)} / [mapSize m] @-}
set     :: Ord k => k -> v -> Map k v -> Map k v
set k v Empty                   = Node k v emptyMap emptyMap
set k v (Node k' v' left right)
  | k == k'                     = Node k v left right
  | k < k'                      = Node k' v' (set k v left) right
  | k > k'                      = Node k' v' left (set k v right)

-- Test for existence of a value at a given key and lift the result to logic
{-@ member :: k:k -> m:Map k v -> {v:Bool | v <=> Set_mem k (keys m)} @-}
member     :: Ord k => k -> Map k v -> Bool
member k m =  k `Data.Set.member` (keys m)

-- Bring some expression into scope for the sake of the SMT solver
{-@ assert :: a -> b -> b @-}
assert :: a -> b -> b
assert _ y = y

-- Lemma: If no keys of a map match a given key then that key is also not in the key set 
{-@ lem_notMember :: key:k -> m:Map {k':k | k' /= key} v -> {v:Bool | not (Set_mem key (keys m))} / [mapSize m] @-}
lem_notMember     :: k -> Map k v -> Bool
lem_notMember k Empty                 = True
lem_notMember k (Node _ _ left right) = (lem_notMember k left) && (lem_notMember k right)

-- Given existence of a given key, safely get the value 
{-@ get :: k:k -> {m:Map k v | Set_mem k (keys m)} -> v / [mapSize m] @-}
get     :: Ord k => k -> Map k v -> v
get k Empty = die "Unreachable in get"
get k (Node k' v' left right) 
  | k == k' = v'
  | k < k'  = assert (lem_notMember k right) $ get k left 
  | k > k'  = assert (lem_notMember k left)  $ get k right 

-- Variable names
type Var = String

-- A simple expression type
data Expr = Const Int 
          | Var Var
          | Plus Expr Expr
          | Let Var Expr Expr
          | Fun Var Expr
          | App Expr Expr
  deriving (Show)

-- A measure for the size of any expression
{-@ measure exprSize @-}
{-@ lazy exprSize @-}
{-@ exprSize             :: Expr -> Nat @-}
exprSize                 :: Expr -> Int
exprSize (Const i)       =  0
exprSize (Var v)         =  1
exprSize (Plus e1 e2)    =  1 + (exprSize e1) + (exprSize e2)
exprSize (Let var e1 e2) =  1 + (exprSize e1) + (exprSize e2)
exprSize (Fun var e)     =  1 + exprSize e
exprSize (App e1 e2)     =  1 + exprSize e1 + exprSize e2

-- Measure if an expression is a value 
{-@ measure val @-}
val           :: Expr -> Bool
val (Const _) =  True
val _         =  False

-- Refinement type for just value expressions
{-@ type Val = {v:Expr | val v} @-}

-- Mark code as unreachable
{-@ die :: {v:String | false} -> a @-}
die :: String -> a 
die = error

-- Example of a function operating over a refined type of Expr
{-@ plus                 :: Val -> Val -> Val @-}
plus                     :: Expr -> Expr -> Expr
plus (Const a) (Const b) =  Const (a + b)
plus _ _                 =  die "plus"

-- An environment mapping variable names to values
{-@ type Env = Map Var Val @-}
type Env = Map Var Expr

-- The empty environment
{-@ emptyEnv :: {v:Env | keys v = empty} @-}
emptyEnv     :: Env
emptyEnv     =  emptyMap

-- Evaluate an expression within an environment, producing a value
{-@ eval               :: g:Env -> e:ClosedExpr g -> Val / [exprSize e] @-}
eval                   :: Env -> Expr -> Expr
eval g (Const a)       =  Const a
eval g (Var var)       =  get var g
eval g (Plus e1 e2)    =  plus (eval g e1) (eval g e2)
eval g (Let var e1 e2) =  eval g' e2 where g' = set var (eval g e1) g
eval g (Fun var e)     =  -- Can only evaluate to a value if the function is constant 
                          if isClosedExpr g e then eval g e else Const 0
eval g (App e1 e2)     =  case e1 of
                            Fun var e -> eval g' e where g' = set var (eval g e2) g 
                            otherwise -> Const 0 -- Unreachable if well-formed

-- Naive definition of free variables in expressions (assuming distinct names)
{-@ measure free @-}
{-@ lazy free @-}
{-@ free             :: e:Expr -> Set Var @-}
free                 :: Expr -> Set Var
free (Const _)       =  Data.Set.empty
free (Var x)         =  singleton x
free (Plus e1 e2)    =  (free e1) `union` (free e2)
free (Let var e1 e2) =  free e1 `union` (free e2 `difference` singleton var)
free (Fun var e)     =  free e `difference` singleton var 
free (App e1 e2)     =  (free e1) `union` (free e2)

-- An expression is closed if its set of free variables is bound by the ambient environment 
{-@ predicate IsClosedExpr G E = Set_sub (free E) (keys G) @-}

-- Check if an expression is closed with respect to an environment 
{-@ isClosedExpr :: g:Env -> e:Expr -> {v:Bool | v <=> IsClosedExpr g e} @-}
isClosedExpr     :: Env -> Expr -> Bool
isClosedExpr g e =  (free e) `isSubsetOf` (keys g)

-- A type for closed expressions
{-@ type ClosedExpr G = {e:Expr | IsClosedExpr G e} @-}

-- A top-level evaluator
{-@ topEval :: {e:Expr | free e = empty} -> Val @-}
topEval     :: Expr -> Expr
topEval     =  eval emptyEnv 

-- Well-formedness check
{-@ evalAny :: Env -> Expr -> Maybe Val @-}
evalAny     :: Env -> Expr -> Maybe Expr
evalAny g e =  if isClosedExpr g e then Just (eval g e) else Nothing

-- Example usage
tests   = [v1]
  where
    v1  = topEval e1
    e1  = App f1 c3
    f1  = Fun x e3 
    e3  = Plus c2 (Var x)
    c2  = Const 2
    c3  = Const 3
    x   = "x"

-- Get the set of elements of a list
{-@ measure elems @-}
elems        :: Ord a => [a] -> Set a
elems []     =  empty
elems (x:xs) =  singleton x `union` elems xs

-- Test if a value is in the element set of a list 
{-@ predicate Elem X XS = Set_mem X (elems XS) @-}

-- Type synonym for symmetry
{-@ type List a = [a] @-}
type List a = [a]

-- Type of lists with bounded elements
{-@ type ListLE a N = List {x:a | x <= N} @-}

-- Type of lists whose element set equals that of another list
{-@ type ListEq a YS = {xs:List a | elems xs = elems YS} @-}

-- Maximum returns a dependent pair of the max and a list bounded by the max whose elements equal the input
{-@ maximum      :: {xs:[Int] | len xs > 0} -> (n :: Int, ListEq {x:Int | x <= n} xs) @-}
maximum          :: [Int] -> (Int, [Int])
maximum [x]      =  (x, [x])
maximum t@(x:xs) =  if x > n then (x, x:ys) else (n, x:ys)
  where (n, ys)  =  maximum xs

-- Lemma: If a list is bounded by n then n+1 cannot be an element
{-@ lem_notElt      :: n:Int -> xs:List {x:Int | x <= n} -> {v:Bool | not (Elem (n+1) xs)} / [len xs] @-}
lem_notElt          :: Int -> [Int] -> Bool
lem_notElt n []     =  True
lem_notElt n (_:xs) =  lem_notElt n xs

-- Return an int which is distinct from all in the input list
{-@ fresh :: xs:[Int] -> {v:Int | not (Elem v xs)} @-}
fresh           :: [Int] -> Int
fresh []        =  0
fresh xs        =  assert (lem_notElt n ys) $ n + 1
  where (n, ys) =  maximum xs

