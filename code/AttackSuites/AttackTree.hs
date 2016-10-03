module AttackTree where

-- Basic Attack Trees:
data ATree l = Base l
             | Or  l (ATree l) (ATree l)
             | And l (ATree l) (ATree l)