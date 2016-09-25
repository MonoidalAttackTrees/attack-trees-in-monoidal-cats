{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module Multiset where

import Test.QuickCheck

newtype Multiset a = MS ([a], a -> Integer)

empty :: Multiset a
empty = MS ([], \_ -> 0)

to_list :: Multiset a -> [a]
to_list (MS (m , _)) = m

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
   is_consistent_alist' acc ((x,n):a) | x `elem` acc || n < 1 = False
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
   s = \x r -> (x `elem` m2) && ((c1 x) <= (c2 x)) && r

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
   aux acc x | x `elem` acc = acc
             | otherwise = x:acc

infix 3 |+|
(|+|) :: Eq a => Multiset a
              -> Multiset a
              -> Multiset a
(MS (m1, c1)) |+| (MS (m2, c2)) = MS (m1 `non_dup_app` m2, c1 `append` c2)
 where
   append c1 c2 x | x `elem` m1 && not (x `elem` m2) = c1 x
                  | x `elem` m2 && not (x `elem` m1) = c2 x
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
(MS (x:m1,c1)) |^| (MS (m2,c2)) | x `elem` m2 = MS (x:m,c')
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

mmap :: (Eq a, Eq b) => (a -> b) -> Multiset a -> Multiset b
mmap f (MS ([],c)) = empty
mmap f (MS (x:m,c)) = MS (f x:m',c'')
 where
   MS (m', c') = mmap f (MS (m,c))
   c'' e | e == f x = c x
         | otherwise = c' e

(*>>=) :: (Eq a, Eq b) => Multiset a
                       -> (a -> Multiset b)
                       -> Multiset b
(MS (m,c)) *>>= f = foldr (|+|) empty m'
 where
   m' = map f m

-- Constrained-monad problem, we need Eq a and Eq b for bind.
-- 
-- instance Monad Multiset where
--     m >>= f = m *>>= f
--     return x = x *-> empty
