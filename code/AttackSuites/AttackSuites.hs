module AttackSuites where

import Prelude hiding (elem,(<*>))
import qualified Data.List as L

import Multiset

type Attack a = Multiset a

type AttackSuite a = Set (Attack a)
type AttackSuiteM a = MSetM (Attack a)

(<*>) :: Eq a => AttackSuite a
              -> AttackSuite a
              -> AttackSuite a
n <*> m = lower_mset $ tensor n m
 where
   tensor :: Eq a => AttackSuite a
                  -> AttackSuite a
                  -> AttackSuiteM a
   tensor n m = do
     atk1 <- lift_mset n
     atk2 <- lift_mset m 
     return $ atk1 |+| atk2

data AttackTree l q = Base l q
                    | And  l (q -> q -> q) (AttackTree l q) (AttackTree l q)
                    | Or   l (q -> q -> q) (AttackTree l q) (AttackTree l q)

-- interp :: Eq n => AttackTree n -> AttackSuite n
-- interp = lower_mset.interp'
--  where
--    interp' :: Eq n => AttackTree n -> AttackSuiteM n
--    interp' (Base n) = return $ n *-> empty
--    interp' (And l r) = lift_mset $ l' <*> r'
--     where
--       l' = lower_mset $ interp' l
--       r' = lower_mset $ interp' r  
--    interp' (Or l r) = lift_mset $ l' `set_union` r'
--     where
--       l' = lower_mset $ interp' l
--       r' = lower_mset $ interp' r

-- exterp :: Eq n => AttackSuite n -> AttackTree n
-- exterp as = 
--   let t = [L.foldr1 And $ map Base $ to_list atk | atk <- asl]
--    in foldr1 Or t
--  where
--    asl = to_list as 

-- atree_ex1 :: AttackSuite String
-- atree_ex1 = atk1 *-> atk2 *-> atk3 *-> empty
--  where
--    atk1 :: Attack String
--    atk1 = from_list $ ["steal key", "open door"]
--    atk2 :: Attack String
--    atk2 = from_list $ ["force lock", "open door"]
--    atk3 :: Attack String
--    atk3 = from_list $ ["pick lock", "open door"]

