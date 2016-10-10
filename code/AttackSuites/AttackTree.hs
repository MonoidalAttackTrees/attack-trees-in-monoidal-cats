{-# LANGUAGE ViewPatterns #-}
module AttackTree where

import qualified AttackSuites as A

-- Basic Attack Trees:
data ATree l = Base l
             | Or  l (ATree l) (ATree l)
             | And l (ATree l) (ATree l)
 deriving Show

---------------------------------------------
-- Interpretation into Attack Suites       --
---------------------------------------------
toDNF :: ATree l -> ATree l
toDNF (Base l) = Base l
toDNF (Or l t1 t2) = Or l (toDNF t1) (toDNF t2)
toDNF (And l t1 t2) =
    case ((toDNF t1, toDNF t2)) of
      ((Or l1 d1 d2), (Or l2 d3 d4)) ->
          toDNF $ Or l1 (Or l2 (And l d1 d3)
                        (And l d1 d4))
                 (Or l2 (And l d2 d3)
                        (And l d2 d4))
      ((Or l1 d1 d2), d3) ->
          toDNF $ Or l1 (And l d1 d3) (And l d2 d3)
      (d1, (Or l2 d2 d3)) ->
          toDNF $ Or l2 (And l d1 d2) (And l d1 d3)
      (d1, d2) -> And l d1 d2

-- This function assumes the input is only conjunctive.
toCATree :: ATree l -> A.CATree l
toCATree (Base l) = A.BC l
toCATree (And _ t1 t2) = A.And (toCATree t1) (toCATree t2)
toCATree _ = error "Nonconjunctive input."

-- This function assumes the input is in DNF and consists of at least
-- one disjunction.
toDATree :: ATree l -> A.DATree l
toDATree (Or _ t1@(Or _ _ _) t2@(Or _ _ _)) = A.Or (Left r1) (Left r2)
 where
   r1 = toDATree t1
   r2 = toDATree t2
toDATree (Or _ t1 t2@(Or _ _ _)) = A.Or (Right r1) (Left r2)
 where
   r1 = toCATree t1
   r2 = toDATree t2
toDATree (Or _ t1@(Or _ _ _) t2) = A.Or (Left r1) (Right r2)
 where
   r1 = toDATree t1
   r2 = toCATree t2                                  
toDATree (Or _ t1 t2) = A.Or (Right r1) (Right r2)
 where
   r1 = toCATree t1
   r2 = toCATree t2
toDATree _ = error "Nondisjunctive input."

toAttackTree :: ATree l -> A.AttackTree l
toAttackTree (toDNF -> t@(Or _ _ _))= Right $ toDATree t
toAttackTree (toDNF -> t@(And _ _ _))= Left $ toCATree t

toAttackSuite :: Eq l => ATree l -> A.AttackSuite l
toAttackSuite = A.interp.toAttackTree