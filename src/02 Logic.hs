-- True and False as Refinement Types of Bool
{-@ type TRUE  = { v:Bool | v} @-}
{-@ type FALSE = { v:Bool | not v} @-}

-- Logical implication
{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> _     = True
True  ==> False = False
True  ==> True  = True

-- Logical iff
{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> False = False
True  <=> True  = True 

{-@ ex0 :: TRUE @-}
ex0 = True 

{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b

{-@ ex2 :: Bool -> FALSE @-}
ex2 b = b && not b

{-@ ex3 :: Bool -> Bool -> TRUE @-}
ex3 a b = (a && b) ==> a 

{-@ ex4 :: Bool -> Bool -> TRUE @-}
ex4 a b = (a && b) ==> b 

-- Modus ponens via SMT solver
{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 a b = (a && (a ==> b)) ==> b

{-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
exDeMorgan1 a b = not (a && b) <=> (not a || not b)

{-@ ax1 :: Int -> TRUE @-}
ax1 :: Int -> Bool
ax1 x = x < (x + 1)

{-@ ax2 :: Int -> TRUE @-}
ax2 :: Int -> Bool
ax2 x = (x < 0) ==> (0 < 0 - x)

