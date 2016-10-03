{-# LANGUAGE ViewPatterns #-}
module AttackSuites where

import Prelude hiding (elem,(<*>))
import qualified Data.List as L

import Multiset

type Attack a = Multiset a

type AttackSuite l  = Set (l, Attack l)

as_tensor :: Eq a => a
         -> AttackSuite a
         -> AttackSuite a
         -> AttackSuite a
as_tensor l n m = build_set $ do
     (l1,atk1) <- get n
     (l2,atk2) <- get m 
     insert (l, atk1 |+| atk2)

-- Attack Trees in Disjunctive Normal Form (DNF):
data DNFATree l = Or l [AndAttack l]
 deriving (Eq, Show)

data AndAttack l = And l [AndAttack l]
 deriving (Eq, Show)

base_attack :: l -> AndAttack l
base_attack l = And l []

atree_ex1 :: DNFATree Int
atree_ex1 = Or 1 [And 2 [base_attack 3, base_attack 4],
                  And 5 [base_attack 6, base_attack 7]]

atree_ex2 :: DNFATree Int
atree_ex2 = Or 1 [base_attack 1, base_attack 2, base_attack 3]

atree_ex3 :: DNFATree Int
atree_ex3 = Or 1 [And 2 [And 3 [base_attack 4, base_attack 5],
                         And 6 [base_attack 5],
                         base_attack 8],
                  base_attack 9]

interp_and :: Eq n => AndAttack n -> AttackSuite n
interp_and (And l []) = build_set $ insert (l, l *-> empty)
interp_and (And l as) = foldr1 (as_tensor l) suites
 where
   suites = map interp_and as

interp :: Eq n => DNFATree n -> AttackSuite n
interp (Or l as) = foldr set_union empty suites
 where
   suites = map interp_and as

exterp_and :: Eq l => Attack l -> DNFATree l
exterp_and (to_list -> as) = undefined

exterp :: Eq l => l -> AttackSuite l -> DNFATree l
exterp l (to_list -> as) = undefined
