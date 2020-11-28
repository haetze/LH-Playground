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
--   | (:) (hd :: a) (tl :: [a<p h>]<p>) -> [a]<p>

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


