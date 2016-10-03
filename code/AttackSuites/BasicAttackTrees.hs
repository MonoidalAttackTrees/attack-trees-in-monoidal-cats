module BasicAttackTree where

import qualified AttackSuites as AS

data ATree l = Base l
             | Or  l (ATree l) (ATree l)
             | And l (ATree l) (ATree l)
 deriving Show

to_dnf :: ATree l -> AS.DNFATree l
to_dnf (Base l)      = AS.Or l [AS.base_attack l]
to_dnf (Or l t1 t2)  = AS.Or l $ a1 ++ a2
 where
   AS.Or _ a1 = to_dnf t1
   AS.Or _ a2 = to_dnf t2
to_dnf (And l t1 t2) = AS.Or l b
 where
   AS.Or _ a1 = to_dnf t1
   AS.Or _ a2 = to_dnf t2
   b = a1 >>= a a2

a :: [AS.AndAttack l] -> AS.AndAttack l -> [AS.AndAttack l]
a [] t = [t]
a ((AS.And y bs):cs) t@(AS.And x as) = (AS.And y (t:bs)):(a cs t)

-- (A or B) and (C or D)
-- A or (B and (C or D))
-- A or (B and C) or (B and D)