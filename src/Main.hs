-- Created on 07 Nov 2020 by richard.stewing@udo.edu

module Main where

main :: IO ()
main = putStrLn "Hello, World"


{-@ measure len @-}
{-@ len :: [a] -> {n : Int | n >= 0} @-}
len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + len xs

{-@ append :: xs : [a] -> ys : [a] -> {l : [a] | len l = len xs + len ys} @-}
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

{-@ rep :: a -> n : Nat -> {xs : [a] | len xs = n} @-}
rep :: a -> Int -> [a]
rep _ 0 = []
rep x n = x : rep x (n-1)


data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

  
{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}


okList  = 1 :< 2 :< 3 :< Emp

-- data [a] <p :: a -> a -> Prop> 
--   = []  
--   | (:) (hd :: a) (tl :: [a<p hd>]<p>) -> [a]<p>

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}

{-@ insertSort    :: (Ord a) => xs:[a] -> (IncrList a) @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ insert :: (Ord a) => a -> IncrList a -> IncrList a @-}
insert y []     = [y]
insert y (x:xs)
  | y <= x      = y : x : xs
  | otherwise   = x : insert y xs


{-@ whatGosUp :: IncrList Integer @-}
whatGosUp = [1,2,3]


data BiggerN = B Int [Int] deriving(Show, Read, Eq) 


{-@ data PropL a <p :: a -> Bool>  = PropL [a<p>]@-}
data PropL a = PropL [a]

{-@ type Bigger5 = PropL Int <{\n -> 5 < n}> @-}

{-@ bigger5 :: Bigger5 @-}
bigger5 :: PropL Int
bigger5 = PropL [6,7,8,9]


{-@ data SplitList a <p1 :: a -> Bool, p2 :: a -> Bool> = L [a<p1>] [a<p2>] @-}
data SplitList a = L [a] [a]

-- Unclear why this specification is illeagal
-- Error:
-- /Users/haetze/Documents/Code/LH-Playground/src/Main.hs:77:55: error:
    -- • Cannot parse specification:
    -- unexpected "\\"
    -- expecting monoPredicateP
-- {-@ split :: Ord a => (n : a) -> [a] -> SplitList a <{\x -> x <= n}, {\x -> x > n}> @-}
-- split_ :: Ord a => a -> [a] -> SplitList a
-- split_ x [] = L [x] []
-- split_ x (y:ys)
--   | y <= x = L (y:xs') (ys')
--   | y >  x = L (xs') (y:ys')
--   where
--     L xs' ys' = split_ x ys
