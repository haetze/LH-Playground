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


{-@ data SplitList Int <p1 :: Int -> Bool, p2 :: Int -> Bool> = L [Int<p1>] [Int<p2>] @-}
data SplitList = L [Int] [Int]

{-@ split_ :: n : Int -> [Int] -> ([Int<{\x -> x <= n}>], [Int<{\x -> x > n}>]) @-}
split_ :: Int -> [Int] -> ([Int],[Int])
split_ x [] = ([x],[])
split_ x (y:ys)
  | y <= x = (y:xs', ys')
  | y >  x = (xs', y:ys')
  where
    (xs', ys') = split_ x ys

{-@ conc :: n:Int -> IncrList Int<{\x -> x <= n}> -> IncrList Int<{\x -> x <= n}> -> IncrList Int @-}
conc :: Int -> [Int] -> [Int] -> [Int]
conc _ [] ys = ys
conc n (x:xs) ys = x : conc n xs ys 

-- {-@ sort_q :: forall <p :: Int -> Bool> . [Int<p>] -> IncrList Int<p> @-}
-- sort_q :: [Int] -> [Int]
-- sort_q [] = []
-- sort_q [x] = [x]
-- sort_q (x:xs) = ys' ++ zs'
--   where
--     (ys,zs) = split_ x xs
--     ys' = sort_q ys
--     zs' = sort_q zs
