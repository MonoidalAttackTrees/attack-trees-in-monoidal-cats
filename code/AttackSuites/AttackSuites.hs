module AttackSuites where

import Prelude hiding (elem,(<*>))
import qualified Data.List as L

import Multiset

type Attack a = Multiset a

type AttackSuite l = Set (Attack l)

as_tensor :: Eq a => AttackSuite a
                  -> AttackSuite a
                  -> AttackSuite a
as_tensor n m = build_set $ do
     atk1 <- get n
     atk2 <- get m 
     insert $ atk1 |+| atk2

-- Attack Trees in Disjunctive Normal Form (DNF):

data CATree l = BC l | And (CATree l) (CATree l)
 deriving (Eq, Show)

data DATree l = BD l | Or (Either (DATree l) (CATree l))
                            (Either (DATree l) (CATree l))
 deriving (Eq, Show)

type AttackTree l = Either (CATree l) (DATree l)

interp_and :: Eq n => CATree n -> Attack n
interp_and (BC l) = l *-> empty
interp_and (And t1 t2) = (interp_and t1) |+| (interp_and t2)                 

interp_disj :: Eq l => DATree l -> AttackSuite l
interp_disj (BD l) = build_set $ insert empty
interp_disj (Or (Left t1)  (Left t2))  = a1 `as_tensor` a2
 where
   a1 = interp_disj t1
   a2 = interp_disj t2
interp_disj (Or (Left t1) (Right t2))  = a2 *-> a1
 where
   a1 = interp_disj t1
   a2 = interp_and t2
interp_disj (Or (Right t1) (Left t2))  = a1 *-> a2
 where
   a2 = interp_disj t2
   a1 = interp_and t1
interp_disj (Or (Right t1) (Right t2)) = build_set.insert $ a1 |+| a2
 where
   a1 = interp_and t1
   a2 = interp_and t2

interp :: Eq l => AttackTree l -> AttackSuite l
interp (Left t) = i *-> empty
 where
   i = interp_and t
interp (Right t) = interp_disj t
        
-- Note that the model forces the tree to be right associated.
exterp_and :: Eq l => Attack l -> CATree l
exterp_and (MS ([l],c)) = BC l
exterp_and (MS ((l:ls),c)) = And (BC l) t
 where
   t = exterp_and (MS (ls,c))

exterp :: Eq l => AttackSuite l -> AttackTree l
exterp (MS ([t],c)) = Left $ exterp_and t
exterp (MS ((t:ts),c)) = Right (Or (Right s) r)
 where
   s = exterp_and t
   r = case exterp (MS (ts,c)) of
         Left x -> Right x
         Right x -> Left x
