{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
module Multiset where

import Test.QuickCheck

import Prelude hiding (elem)
import qualified Data.List as L

newtype Multiset a = MS ([a], a -> Integer)
    
empty :: Multiset a
empty = MS ([], \_ -> 0)

elem :: Eq a => a
             -> Multiset a
             -> Bool
x `elem` (MS (m,c)) = c x > 0 

infixr 1  *->
(*->) :: Eq a => a
              -> Multiset a
              -> Multiset a
x *-> (MS (m,c)) | c x > 0   = MS (m, c')
                 | otherwise = MS (x:m, c'')
 where
   c'  = \e -> if x == e then c e + 1 else c e   
   c'' = \e -> if x == e then 1 else c e

infix 2 *<=
(*<=) :: Eq a => Multiset a
              -> Multiset a
              -> Bool
(MS (m1, c1)) *<= (MS (m2, c2)) = foldr s True m1
 where
   s = \x r -> (x `L.elem` m2) && ((c1 x) <= (c2 x)) && r

infix 1 *=
(*=) :: Eq a => Multiset a
             -> Multiset a
             -> Bool
m1 *= m2 = (m1 *<= m2) && (m2 *<= m1)

infix 2 *<
(*<) :: Eq a => Multiset a
             -> Multiset a
             -> Bool
m1 *< m2 = (m1 *<= m2) && not (m2 *<= m1)

non_dup_app :: Eq a => [a]
                    -> [a]
                    -> [a]
non_dup_app l1 [] = l1
non_dup_app l1 l2 = foldl aux l2 l1
 where
   aux acc x | x `L.elem` acc = acc
             | otherwise = x:acc

infix 3 |+|
(|+|) :: Eq a => Multiset a
              -> Multiset a
              -> Multiset a
(MS (m1, c1)) |+| (MS (m2, c2)) = MS (m1 `non_dup_app` m2, c1 `append` c2)
 where
   append c1 c2 x | x `L.elem` m1 && not (x `L.elem` m2) = c1 x
                  | x `L.elem` m2 && not (x `L.elem` m1) = c2 x
                  | otherwise = max (c1 x) (c2 x)

union_prop :: [(Char,Integer)] -> [(Char,Integer)] -> Property
union_prop a1 a2 = (con1 && con2) ==> ((i *<= m1) || (i *<= m2))
 where
    con1 = is_consistent_alist a1
    con2 = is_consistent_alist a2
    m1 = from_alist a1
    m2 = from_alist a2
    i = m1 |+| m2

infix 3 |#|
(|#|) :: (Eq a, Eq b) => Multiset a
                      -> Multiset b
                      -> Multiset (Either a b)
(MS (m1,c1)) |#| (MS (m2,c2)) = MS (m'++m'',c)
 where
   m' = map Left m1
   m'' = map Right m2
   c (Left x) = c1 x
   c (Right x) = c2 x

infix 3 |^|
(|^|) :: Eq a => Multiset a
              -> Multiset a
              -> Multiset a
(MS (x:m1,c1)) |^| (MS (m2,c2)) | x `L.elem` m2 = MS (x:m,c')
                                | otherwise = (MS (m1,c1)) |^| (MS (m2,c2))
 where
   MS (m,c) = (MS (m1,c1)) |^| (MS (m2,c2))
   c' e | e == x = min (c1 e) (c2 e)
        | otherwise = c e                 
_ |^| _ = empty

intersection_prop :: [(Char,Integer)]
                  -> [(Char,Integer)]
                  -> Property
intersection_prop a1 a2 = (con1 && con2) ==> ((i *<= m1) && (i *<= m2))
 where
    con1 = is_consistent_alist a1
    con2 = is_consistent_alist a2
    m1 = from_alist a1
    m2 = from_alist a2
    i = m1 |^| m2

infix 3 |-|
(|-|) :: Eq a => Multiset a
              -> Multiset a
              -> Multiset a
(MS ([],c1)) |-| (MS (m2,c2)) = empty
(MS (x:m1,c1)) |-| t@(MS (m2,c2)) | c'' x == 0 = (MS (m1,c1)) |-| t
                                  | otherwise  = MS (x:m',c'')
 where
   MS (m',c') = (MS (m1,c1)) |-| t
   c'' e | e == x = max 0 ((c1 e) - (c2 e))
         | otherwise = c' e

infix 3 |*|
(|*|) :: Eq a => Multiset a
              -> Multiset b
              -> Multiset (a,b)
(MS (m1,c1)) |*| (MS (m2,c2)) = MS (m,c)
 where
   m = [(x,y) | x <- m1,y <- m2]
   c (x,y) = (c1 x) * (c2 y)

mmap :: (Eq a,Eq b) => (a -> b) -> Multiset a -> Multiset b
mmap f (MS ([],c)) = empty
mmap f (MS (x:m,c)) = MS (f x:m',c'')
 where
   MS (m', c') = mmap f (MS (m,c))
   c'' e | e == f x = c x
         | otherwise = c' e

-----------------------------------------------
-- Show Instance                             --
-----------------------------------------------
to_list :: Multiset a -> [a]
to_list (MS (m , _)) = m

from_list :: Eq a => [a] -> Multiset a
from_list [] = empty
from_list (x:xs) = x *-> from_list xs

to_alist :: Multiset a -> [(a, Integer)]
to_alist (MS (m,c)) = foldr (\x r -> (x,c x):r) [] m

from_alist :: Eq a => [(a,Integer)] -> Multiset a
from_alist = foldr el empty
 where
   el (e,n) r = MS (e:m',c')
    where
      MS (m',c) = r
      c' e' | e' == e = n
            | otherwise = c e'

is_consistent_alist :: Eq a => [(a,Integer)] -> Bool
is_consistent_alist = is_consistent_alist' []
 where
   is_consistent_alist' :: Eq a => [a]
                                -> [(a,Integer)]
                                -> Bool
   is_consistent_alist' acc [] = True
   is_consistent_alist' acc ((x,n):a) | x `L.elem` acc || n < 1 = False
                                      | otherwise = is_consistent_alist' (x:acc) a

is_consistent_mset :: Eq a => Multiset a
                           -> Bool
is_consistent_mset = is_consistent_alist.to_alist

to_from_alist_prop :: [(Char,Integer)] -> Property
to_from_alist_prop m =
    (is_consistent_alist m) ==> ((to_alist.from_alist $ m) == m)

instance {-# OVERLAPPING #-}
    (Show a) => Show (Multiset a) where
    showsPrec d m = showList.to_alist $ m

-----------------------------------------------
-- Eq Instance                               --
-----------------------------------------------

instance Eq a => Eq (Multiset a) where
  (==) :: Multiset a -> Multiset a -> Bool
  m1 == m2 = m1 *= m2

  (/=) :: Multiset a -> Multiset a -> Bool
  m1 /= m2 = not (m1 *= m2)

-----------------------------------------------
-- The multiset monad MSetM                  --
-----------------------------------------------
(*>>=) :: Eq b => Multiset a
               -> (a -> Multiset b)
               -> Multiset b
(MS (m,c)) *>>= f = foldr (|+|) empty m'
 where
   m' = map f m

data MSetM :: * -> * where
  Return :: a -> MSetM a
  Bind :: Multiset a -> (a -> MSetM b) -> MSetM b

instance Functor MSetM where
    fmap :: (a -> b) -> MSetM a -> MSetM b
    fmap f (Return x) = Return (f x)
    fmap f (m `Bind` g) = m `Bind` (\x -> fmap f (g x))

instance Applicative MSetM where
    pure :: a -> MSetM a
    pure = Return

    (<*>) :: MSetM (a -> b) -> MSetM a -> MSetM b
    (Return f) <*> (Return y) = Return $ f y
    t@(Return f) <*> (m `Bind` g) = m `Bind` (\x -> t <*> g x)
    (t `Bind` f) <*> m = t `Bind` (\y -> (f y) <*> m)

instance Monad MSetM where
    return :: a -> MSetM a
    return = Return

    (>>=) :: MSetM a -> (a -> MSetM b) -> MSetM b
    (Return x) >>= f = f x
    (m `Bind` g) >>= f = m `Bind` (\x -> g x >>= f)

lift_mset :: Multiset a -> MSetM a
lift_mset m = m `Bind` Return

lower_mset :: Eq a => MSetM a -> Multiset a
lower_mset (Return x) = x *-> empty
lower_mset (m `Bind` f) = m *>>= (lower_mset.f)

-----------------------------------------------
-- Sets from multisets                       --
-----------------------------------------------
type Set a = Multiset a

empty_set :: MSetM a
empty_set = lift_mset empty

set_union :: Eq a => Multiset a
                  -> Multiset a
                  -> Multiset a
set_union m1 m2 = lower_mset $ set_union' m1 m2
 where
   set_union' :: Eq a => Multiset a
                      -> Multiset a
                      -> MSetM a
   set_union' m1 m2 = do
     x <- lift_mset m1
     lift_mset $ x *-> m2

set_intersection :: Eq a => Multiset a
                         -> Multiset a
                         -> Multiset a
set_intersection m1 m2 = lower_mset $ set_intersection' m1 m2
 where
   set_intersection' :: Eq a => Multiset a
                             -> Multiset a
                             -> MSetM a
   set_intersection' m1 m2 = do
     x <- lift_mset m1
     if x `elem` m2
     then return x
     else empty_set

set_product :: (Eq a, Eq b) => Multiset a
                            -> Multiset b
                            -> Multiset (a,b)
set_product m1 m2 = lower_mset $ set_product' m1 m2
 where
   set_product' :: (Eq a, Eq b) => Multiset a
                                -> Multiset b
                                -> MSetM (a,b)
   set_product' m1 m2 = do
     x <- lift_mset m1
     y <- lift_mset m2
     return (x, y)

set_difference :: Eq a => Multiset a
                       -> Multiset a
                       -> Multiset a
set_difference m1 m2 = lower_mset $ set_difference' m1 m2
 where
   set_difference' :: Eq a => Multiset a
                           -> Multiset a
                           -> MSetM a
   set_difference' m1 m2 = do
     x <- lift_mset m1
     if x `elem` m2
     then empty_set
     else return x
