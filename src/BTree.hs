{-@ LIQUID "--notermination"           @-}
{-@ LIQUID "--reflection" @-}
module BTree where

--import Language.Haskell.Liquid.Equational
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((++))

data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }
                  
{-@ data BST a    = Leaf
                  | Node { root  :: a
                         , left  :: BSTL a root
                         , right :: BSTR a root } @-}

{-@ type BSTL a X = BST {v:a | v <= X}             @-}
{-@ type BSTR a X = BST {v:a | X <= v}             @-}
{-@ type BSTRng a X Y = BST (Btwn a X Y) @-}

-- {-@ reflect empty @-}
{-@ measure empty @-}
empty :: BST a -> Bool
empty Leaf = True
empty (Node _ _ _) = False

{-@ minB :: x:{y:BST a | not (empty y)} -> a @-}
{-@ reflect minB @-}
minB :: BST a -> a
minB (Node x Leaf _) = x
minB (Node _ l _) = minB l

{-@ minBP1 :: mini:a -> maxi:a -> x:{v:BSTRng a mini maxi | not (empty v)} -> {minB x >= mini} @-}
minBP1 :: a -> a -> BST a -> ()
minBP1 mini maxi b@(Node x Leaf _) = minB b ==. x =>= mini *** QED
minBP1 mini maxi b@(Node _ l _) = minBP1 mini maxi l ? (minB b ==. minB l *** QED) *** QED 


{-@ maxB :: x:{y:BST a | not (empty y)} -> a @-}
{-@ reflect maxB @-}
maxB :: BST a -> a
maxB (Node x _ Leaf) = x
maxB (Node _ _ r) = maxB r

{-@ maxBP1 :: mini:a -> maxi:a -> x:{v:BSTRng a mini maxi | not (empty v)} -> {maxB x <= maxi} @-}
maxBP1 :: a -> a -> BST a -> ()
maxBP1 mini maxi b@(Node x _ Leaf) = maxB b ==. x =<= maxi *** QED
maxBP1 mini maxi b@(Node _ _ r) = maxBP1 mini maxi r ? (maxB b ==. maxB r *** QED) *** QED

{-@ expand :: m1:a -> m2:a -> m3:{x:a|x <= m1} -> m4:{x:a|x >= m2} -> x:BSTRng a m1 m2 -> {y:BSTRng a m3 m4 | y == x} @-}
expand :: a -> a -> a -> a-> BST a -> BST a
expand m1 m2 m3 m4 Leaf = Leaf
expand m1 m2 m3 m4 (Node a l r) = Node a (expand m1 a m3 a l) (expand a m2 a m4 r)


{-@ toRange :: x:{y:BST a | not (empty y)} -> {y:BSTRng a (minB x) (maxB x)| not (empty y) && x == y }@-}
toRange :: BST a -> BST a
toRange x@(Node b Leaf Leaf) = Node b Leaf Leaf ? (maxB x ==. b *** QED) ? (minB x ==. b *** QED)
toRange x@(Node b l Leaf) = Node b (expand (minB l) (maxB l) (minB l) b (toRange l)) Leaf ? (minB x ==. minB l *** QED) ? (maxB x ==. b *** QED)
toRange x@(Node b Leaf r) = Node b Leaf (expand (minB r) (maxB r) b (maxB r) (toRange r)) ? (minB x ==. b *** QED) ? (maxB x ==. maxB r *** QED)
toRange x@(Node b l r) = Node b l' r' ? (minB x ==. minB l *** QED) ? (maxB x ==. maxB r *** QED)
    where
        l' = (expand (minB l) (maxB l) (minB l) b (toRange l))
        r' = (expand (minB r) (maxB r) b (maxB r) (toRange r))


mem                 :: (Ord a) => a -> BST a -> Bool
mem _ Leaf          = False
mem k (Node k' l r)
  | k == k'         = True
  | k <  k'         = mem k l
  | otherwise       = mem k r

one   :: a -> BST a
one x = Node x Leaf Leaf

add                  :: (Ord a) => a -> BST a -> BST a
add k' Leaf          = one k'
add k' t@(Node k l r)
  | k' < k           = Node k (add k' l) r
  | k  < k'          = Node k l (add k' r)
  | otherwise        = t

data MinPair a = MP { mElt :: a, rest :: BST a }

{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}


{-@ type Btwn a X Y = {x:a | X <= x && x <= Y} @-}
{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type IncrListR a X Y = IncrList (Btwn a X Y) @-}

{-@ merge :: Ord a => mini:a -> maxi:a -> IncrListR a mini maxi -> IncrListR a mini maxi -> IncrListR a mini maxi @-}
merge :: Ord a => a -> a -> [a] -> [a] -> [a]
merge mini maxi [] ys = ys
merge mini maxi xs [] = xs
merge mini maxi (x:xs) (y:ys) 
    | x < y = x : merge x maxi xs (y:ys)
    | y < x = y : merge y maxi (x:xs) ys
    | x == y = x:y:merge x maxi xs ys

{-@ die :: s:{x:String | false} -> a @-}
die = error

{-@ app :: Ord a => mini:a 
                 -> midli:{x:a | x >= mini} 
                 -> maxi:{x:a | x >= midli} 
                 -> IncrListR a mini midli 
                 -> IncrListR a midli maxi 
                 -> IncrListR a mini maxi @-}
app :: Ord a => a -> a -> a -> [a] -> [a] -> [a]
app mini midli maxi [] ys = ys
app mini midli maxi xs [] = xs
app mini midli maxi (x:xs) (y:ys)
    | x < y = x : app x midli maxi xs (y:ys)
    | y < x = die "Should not happen"
    | x == y = x:y:app x x maxi xs ys

bstSort   :: (Ord a) => [a] -> [a]
bstSort [] = []
bstSort l = case b of 
                Leaf -> []
                _    -> toIncList (minB b) (maxB b) (toRange b)
    where
    b = toBST l

toBST     :: (Ord a) => [a] -> BST a
toBST     = foldr add Leaf

{-@ toIncList :: Ord a => mini:a -> maxi:a -> x:BSTRng a mini maxi -> IncrListR a mini maxi@-}
toIncList :: Ord a => a -> a -> BST a -> [a]
toIncList _ _ Leaf = []
toIncList mini maxi (Node x l r) = app mini x  maxi (app mini x x (toIncList mini x l) [x]) (toIncList x maxi r) 


