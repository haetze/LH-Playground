{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

-- Created on 25 Nov 2021 by richard.stewing@udo.edu
-- Copyright Richard Stewing,25 Nov 2021
-- Licensed under MIT, See toplevel LICENSE file.
-- This code was only tested in the web interface.
-- GHC 9.2.1 is not yet supported in liquid haskell.
-- The last supported GHC version, is not supported on M1.

module Lists where 

import Prelude hiding (reverse, (++), length)
{-@ infix   : @-}
import Language.Haskell.Liquid.Equational


length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs


{-@ length :: [a] -> Nat @-}

{-@ measure length @-}

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {os:[a] | length os == length xs + length ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

{-@ reflect reverse @-}

singletonP :: a -> Proof
{-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
singletonP x
  =   reverse [x]
  ==. reverse [] ++ [x]
  ==. [] ++ [x]
  ==. [x]
  *** QED


singleton1P :: Proof
{-@ singleton1P :: { reverse [1] == [1] } @-}
singleton1P
  =   reverse [1] 
      ? singletonP 1 
  ==. [1]
  *** QED


{-@ involutionP :: xs:[a] -> {reverse (reverse xs) == xs } @-}
involutionP :: [a] -> Proof 
involutionP [] 
  =   reverse (reverse []) 
      -- applying inner reverse
  ==. reverse []
      -- applying reverse
  ==. [] 
  *** QED 
involutionP (x:xs) 
  =   reverse (reverse (x:xs))
      -- applying inner reverse
  ==. reverse (reverse xs ++ [x])
      ? distributivityP (reverse xs) [x]
  ==. reverse [x] ++ reverse (reverse xs) 
      ? involutionP xs 
  ==. reverse [x] ++ xs 
      ? singletonP x 
  ==. [x] ++ xs
      -- applying append on []
  ==. x:([]++ xs)
      -- applying ++
  ==. (x:xs)
  *** QED


distributivityP :: [a] -> [a] -> Proof
{-@ distributivityP :: xs:[a] -> ys:[a] -> {reverse (xs ++ ys) == reverse ys ++ reverse xs} @-}

distributivityP [] ys
  =   reverse ([] ++ ys)
  ==. reverse ys 
       ? leftIdP (reverse ys) 
  ==. reverse ys ++ []
  ==. reverse ys ++ reverse []
  *** QED 
distributivityP (x:xs) ys 
  =   reverse ((x:xs) ++ ys)
  ==. reverse (x:(xs ++ ys))
  ==. reverse (xs ++ ys) ++ [x]
       ? distributivityP xs ys 
  ==. (reverse ys ++ reverse xs) ++ [x]
       ? assocP (reverse ys) (reverse xs) [x]
  ==. reverse ys ++ (reverse xs ++ [x])
  ==. reverse ys ++ reverse (x:xs)
  *** QED

{-@ rightIdP :: xs:[a] -> { xs ++ [] == xs } @-}
rightIdP :: [a] -> Proof
rightIdP []     
  =   [] ++ [] 
  ==. [] 
  *** QED 
rightIdP (x:xs)
  =   (x:xs) ++ [] 
  ==. x : (xs ++ [])
      ? rightIdP xs
  ==. x : xs
  *** QED

{-@ ple leftIdP @-}
leftIdP :: [a] -> Proof
{-@ leftIdP :: xs:[a] -> { xs ++ [] == xs } @-}
leftIdP []     = ()
leftIdP (_:xs) = leftIdP xs


{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> () 
assocP [] _ _       = ()
assocP (x:xs) ys zs = assocP xs ys zs

{-@ ple distributivityP' @-}
distributivityP' :: [a] -> [a] -> ()
{-@ distributivityP' :: xs:[a] -> ys:[a] -> {reverse (xs ++ ys) == reverse ys ++ reverse xs} @-}
distributivityP' [] ys = leftIdP (reverse ys)
distributivityP' (x:xs) ys = assocP (reverse ys) (reverse xs) [x] ? distributivityP' xs ys 
{-@ ple involutionP' @-}
{-@ involutionP' :: xs:[a] -> {reverse (reverse xs) == xs } @-}
involutionP' :: [a] -> Proof 
involutionP' [] = ()
involutionP' (x:xs) = distributivityP' (reverse xs) [x] 
                        ? involutionP' xs

{-@ reflect l @-}
{-@ l :: ys:{v:[a] | length v > 0} -> a @-}
{-@ ple l @-}
l :: [a] -> a
l (x:[]) = x
l (_:xs) = l xs

{-@ reflect h @-}
{-@ h :: ys:{v:[a] | length v > 0} -> a @-}
{-@ ple h @-}
h :: [a] -> a
h (x:_) = x

{-@ ple hP @-}
{-@ hP :: xs:{v:[a] | length v > 0} -> ys:[a] -> {h (xs ++ ys) == h xs} @-}
hP :: [a] -> [a] -> ()
hP [] _ = die "Cant happen"
hP (x:xs) ys = h ((x:xs) ++ ys) ==.
                h (x : (xs ++ ys)) ==.
                x ==.
                h (x:xs)
                *** QED

{-@ reflect init2 @-}
{-@ ple init2 @-}
{-@ init2 :: xs :{v:[a] | length v > 0} -> {v:[a] | length v + 1 == length xs} @-}
init2 :: [a] -> [a]
--init2 [] = die "Cant happen"
init2 [x] = []
init2 (x:xs) = x : init2 xs

{-@ concP :: x:a -> xs:[a] -> ys:[a] -> {x:(xs ++ ys) = x:xs ++ ys}@-}
concP :: a -> [a] -> [a] -> ()
concP x xs ys = (x:xs) ++ ys ==. x : (xs ++ ys) *** QED

{-@ initP :: xs : [a] -> ys : {v:[a] | length v > 0} -> {init2 (xs ++ ys) == xs ++ init2 ys} @-}
initP _ [] = die "Cant happen"
initP [] ys = init2 ([] ++ ys) ==. init2 ys ==. [] ++ init2 ys *** QED
initP (x:xs) ys = init2 ((x:xs) ++ ys) ==.
                    init2 (x : (xs ++ ys)) ==.
                    x : (init2 (xs ++ ys)) ? initP xs ys ==.
                    x : (xs ++ init2 ys) ? concP x xs (init2 ys) ==.
                    (x:xs) ++ init2 ys
                    *** QED

{-@ reflect tail2 @-}
{-@ ple tail2 @-}
{-@ tail2 :: xs :{v:[a] | length v > 0} -> {v:[a] | length v + 1 == length xs} @-}
tail2 :: [a] -> [a]
tail2 (x:xs) = xs

{-@ tailP :: xs : {v:[a] | length v > 0} -> ys : [a] -> {tail2 (xs ++ ys) == tail2 xs ++ ys} @-}
tailP :: [a] -> [a] -> ()
tailP (x:xs) ys = tail2 (x:xs ++ ys) ==.
                    tail2 (x:(xs ++ ys)) ==.
                    (xs ++ ys) ==.
                    tail2 (x:xs) ++ ys
                    *** QED

{-@ die :: {v:String | false} -> a @-}
die :: String -> a
die s = error s

{-@ lNE :: x : a -> xs : {v : [a] | length v > 0} -> {l (x:xs) == l xs} @-}
{-@ ple lNE @-}
lNE :: a -> [a] -> ()
lNE x [] = die "Cant happen"
lNE x xs = ()

{-@ lastP :: xs:[a] -> ys:{v:[a] | length v > 0} -> {l (xs ++ ys) == l ys} @-}
lastP :: [a] -> [a] -> ()
lastP [] ys = ()
lastP (x:xs) ys = l ((x:xs) ++ ys) ==.
                    l (x:(xs ++ ys)) ? lNE x (xs ++ ys) ==.
                    l (xs ++ ys) ? lastP xs ys ==.
                    l ys 
                    *** QED



{-@ reverseLH :: xs : {v : [a] | length v > 0} -> {h xs == l (reverse xs)}@-}
{-@ ple reverseLH @-}
reverseLH :: [a] -> ()
reverseLH [x] = ()
reverseLH (x:xs) =  h (x:xs) ==.
                    x ==.
                    l [x] ? lastP (reverse xs) [x] ==.
                    l (reverse xs ++ [x]) ==.
                    l (reverse (x:xs))
                    *** QED


{-@ reverseHL :: xs : {v : [a] | length v > 0} -> {l xs == h (reverse xs)}@-}
{-@ ple reverseHL @-}
reverseHL :: [a] -> ()
reverseHL [x] = ()
reverseHL (x:xs) = l (x:xs) ? lNE x xs ==.
                    l xs ? reverseHL xs ==.
                    h (reverse xs) ? hP (reverse xs) [x] ==.
                    h (reverse xs ++ [x]) ==.
                    h (reverse (x:xs))
                    *** QED

{-@ reflect reved @-}
{-@ reved :: Eq a => xs : [a] -> {v : [a] | length v == length xs} -> Bool @-}
reved :: Eq a => [a] -> [a] -> Bool
reved [] [] = True
reved xs ys = h xs == l ys && reved (tail2 xs) (init2 ys)

{-@ emptyConc :: xs:[a] -> {xs ++ [] == xs} @-}
emptyConc :: [a] -> ()
emptyConc [] = [] ++ [] ==. [] *** QED
emptyConc (x:xs) = (x:xs) ++ [] ==. 
                    x : (xs ++ []) ? emptyConc xs ==. 
                    x:xs *** QED

{-@ revedP1 :: Eq a => xs:[a] -> {reved xs (reverse xs)} @-}
revedP1 :: Eq a => [a] -> ()
revedP1 [] = ()
revedP1 (x:xs) = ((&&) ((==) (h (x:xs)) (l (reverse (x:xs)))) 
                        (reved (tail2 (x:xs)) 
                                (init2 (reverse (x:xs))))) ? reverseLH (x:xs) ==.
                    (&&) True (reved (tail2 (x:xs)) (init2 (reverse (x:xs)))) ==.
                    reved (tail2 (x:xs)) (init2 (reverse (x:xs))) ==.
                    reved xs (init2 (reverse (x:xs))) ==.
                    reved xs (init2 (reverse xs ++ [x])) ? initP (reverse xs) [x] ==.
                    reved xs (reverse xs ++ init2 [x]) ==.
                    reved xs (reverse xs ++ []) ? emptyConc (reverse xs) ==.
                    reved xs (reverse xs) ? revedP1 xs ==.
                    True
                    *** QED
                    
{-@ and1 :: a:Bool -> b:Bool -> p:{a && b} -> {a} @-}
and1 :: Bool -> Bool -> () -> ()
and1 a b p = ()

{-@ and2 :: a:Bool -> b:Bool -> p:{a && b} -> {b} @-}
and2 :: Bool -> Bool -> () -> ()
and2 a b p = ()

{-@ lastP2 :: xs:{v:[a] | length v > 0} -> {init2 xs ++ [l xs] == xs} @-}
lastP2 :: [a] -> ()
lastP2 [x] = init2 [x] ++ [l [x]] ==. [] ++ [x] ==. [x] *** QED
lastP2 (x:xs) = init2 (x:xs) ++ [l (x:xs)] ==.
                x : (init2 xs ++ [l xs]) ? lastP2 xs ==.
                x : xs
                *** QED

{-@ revedP2 :: Eq a => xs:[a] -> ys:{v:[a] | length v == length xs} -> p:{reved xs ys} -> {ys == reverse xs} @-}
revedP2 :: Eq a => [a] -> [a] -> () -> ()
revedP2 [] [] _ = ()
revedP2 (x:xs) ys p = reverse (x:xs) ==.
                    reverse xs ++ [x] ? revedP2 xs (init2 ys) p2 ==.
                    (init2 ys) ++ [x] ? p1 ==.
                    (init2 ys) ++ [l ys] ? lastP2 ys ==.
                    ys
                    *** QED
    where
     p1 = and1 (x == l ys) (reved xs (init2 ys)) p -- x ==. l ys
     p2 = and2 (x == l ys) (reved xs (init2 ys)) p -- reved xs (init ys)

     
{-@ reflect map' @-}
{-@ map' :: f:(a->b) -> xs:[a] -> {v:[b] | length xs == length v} @-}
map' :: (a->b) -> [a] -> [b]
map' f [] = []
map' f (x:xs) = f x : map' f xs

{-@ mapP1 :: Eq b =>  xs:[a] -> ys:[a] -> f:(a->b) -> {map' f (xs++ys) == map' f xs ++ map' f ys}@-}
mapP1 :: Eq b => [a] -> [a] -> (a->b) -> ()
mapP1 [] ys f = map' f ([] ++ ys) ==. map' f ys ==. [] ++ map' f ys ==. map' f [] ++ map' f ys *** QED
mapP1 (x:xs) ys f = map' f (x:xs ++ ys) ==.
                    map' f (x:(xs ++ ys)) ==.
                    f x : map' f (xs ++ ys) ? mapP1 xs ys f ==.
                    f x : (map' f xs ++ map' f ys) ==.
                    (f x : (map' f xs)) ++ map' f ys ==.
                    map' f (x:xs) ++ map' f ys
                    *** QED

{-@ reflect foldl @-}
foldl :: (a -> b -> b) -> b -> [a] -> b
foldl f b [] = b
foldl f b (a:as) = foldl f (f a b) as

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] -> {xs ++ (ys ++ zs) == (xs ++ ys) ++ zs} @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] ys zs = [] ++ (ys ++ zs) ==. ys ++ zs ==. ([] ++ ys) ++ zs *** QED
assoc (x:xs) ys zs = (x:xs) ++ (ys ++ zs) ==. 
                        x:(xs ++ (ys ++ zs)) ? assoc xs ys zs ==.
                        x:((xs ++ ys) ++ zs) ==.
                        (x:(xs ++ ys)) ++ zs ==.
                        ((x:xs) ++ ys) ++ zs
                        *** QED

{-@ reflect ff @-}
ff :: a -> [a] -> [a]
ff x xs = x:xs

{-@ foldlP :: xs:[a] -> ys:[a] -> {foldl ff [] xs ++ ys == foldl ff ys xs} @-}
foldlP :: [a] -> [a] -> ()
foldlP [] ys = foldl ff [] [] ++ ys ==.
                [] ++ ys ==.
                ys ==.
                foldl ff ys []
                *** QED
foldlP (x:xs) ys = foldl ff [] (x:xs) ++ ys ==.
                    foldl ff (ff x []) xs ++ ys ==.
                    foldl ff (x:[]) xs ++ ys ==.
                    foldl ff [x] xs ++ ys ? foldlP xs [x] ==.
                    (foldl ff [] xs ++ [x]) ++ ys ? assoc (foldl ff [] xs) [x] ys ==.
                    (foldl ff [] xs) ++ ([x] ++ ys) ==.
                    (foldl ff [] xs) ++ (x:([] ++ ys)) ==.
                    (foldl ff [] xs) ++ (x:ys) ? foldlP xs (x:ys) ==.
                    foldl ff (x:ys) xs ==.
                    foldl ff (ff x ys) xs ==.
                    foldl ff ys (x:xs)
                    *** QED







{-@ foldlR :: xs:[a] -> {reverse xs == foldl ff [] xs} @-}
foldlR :: [a] -> ()
foldlR [] = ()
foldlR (x:xs) = reverse (x:xs) ==. 
                reverse xs ++ [x] ? foldlR xs ==.
                foldl ff [] xs ++ [x] ? foldlP xs [x] ==.
                foldl ff [x] xs ==.
                foldl ff (ff x []) xs ==.
                foldl ff [] (x:xs)
                *** QED
