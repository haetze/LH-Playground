{-@ LIQUID "--notermination"           @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Blank where

--import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((++),reverse,length,init,last)

{-@ measure length @-}
{-@ length :: [a] -> Nat @-}
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs




{-@ type BoundedStack a N = {x:[a] | length x <= N} @-}
{-@ type EmptyStack a N = {x:BoundedStack a N | length x == 0} @-}

{-@ push :: size:Nat -> x:a -> xs:{y:BoundedStack a size | length y < size} -> {v:BoundedStack a size | length v == length xs + 1 && init v == xs && last v == x} @-}
push :: Int -> a -> [a] -> [a]
push _ x [] = [x]
push size x l@(y:xs) = y:ys ? p1 ? p2
    where 
        ys = push (size-1) x xs
        p1 = (init (y:ys) ==. y:init ys ==. y:xs *** QED)
        p2 = (last (y:ys) ==. last ys ==. x *** QED)

{-@ reflect init @-}
{-@ init :: xs:{v:[a] | length v > 0} -> {v:[a] | length v + 1 = length xs} @-}
init :: [a] -> [a]
init (x:[]) = []
init (x:xs) = x : init xs

{-@ reflect f @-}
{-@ f :: x:a -> xs:[a] -> [a] @-}
f :: a -> [a] -> [a]
f x xs = x:xs

{-@ initP :: x:a -> xs:{v:[a] | length v > 0} -> {(f x (init xs)) = init (f x xs)} @-}
initP :: a -> [a] -> ()
initP x [y] = x:init [y] ==. [x] ==. init [x,y] *** QED
initP x (y:xs) = x:init (y:xs) ==. x:y:init xs ==. init (x:y:xs) *** QED

{-@ reflect last @-}
{-@ last :: xs:{v:[a] | length v > 0} -> a @-}
last :: [a] -> a
last (x:[]) = x
last (x:xs) = last xs


{-@ pop :: size:Nat -> xs:{y:BoundedStack a size | length y > 0} -> {yp:(a,BoundedStack a size) | length (snd yp) + 1 == length xs && init xs == (snd yp) && last xs == (fst yp)} @-}
pop :: Int -> [a] -> (a,[a])
pop size [x] = (x,[])
pop size (x:xs) = (y, x:ys)
    where (y,ys) = pop size xs































