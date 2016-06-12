module LK-from-Freer-is-LK where

open import level
open import functor
open import functions

data OlegLan (f : Set → Set) (a : Set₁) : Set₁ where
  FMap : {x : Set} → (x → a) → f x → OlegLan f a

data Lan (f : Set → Set) (j : Set → Set) (a : Set₁) : Set₁ where
  mkLan : {x : Set} → (j x → a) → f x → Lan f j a

OlegToLan : ∀{f a} → OlegLan f a → Lan f (λ x → x) a
OlegToLan (FMap g p) = mkLan g p

LanIsFunc : ∀{f j} → Functor (Lan f j)
LanIsFunc {f}{j} = mkFunc fm
 where
  fm : {A B : Set₁} → (A → B) → Lan f j A → Lan f j B
  fm g (mkLan h p) = mkLan (g ∘ h) p

  
