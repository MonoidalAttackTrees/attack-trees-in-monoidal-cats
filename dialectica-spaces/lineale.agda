module lineale where

open import prelude

¡ : {A : Set} → (A → A → 𝔹) → A → A → Set
¡ r x y = r x y ≡ tt

record Poset (A : Set) : Set where
 constructor MkPoset
 field
   rel : A → A → 𝔹
   prefl : ∀{a : A} → ¡ rel a a
   ptrans : ∀{a b c : A} → ¡ rel a b → ¡ rel b c → ¡ rel a c
   pasym : ∀{a b : A} → ¡ rel a b → ¡ rel b a → a ≡ b

open Poset public

record MonPoset (P : Set) : Set where
 constructor MkMonPoset
 field
   mul : P → P → P
   unit : P
   
   poset : Poset P
   assoc : ∀{a b c : P} → mul a (mul b c) ≡ mul (mul a b) c
   left-ident : ∀{a : P} → mul unit a ≡ a
   right-ident : ∀{a : P} → mul a unit ≡ a
   symm : ∀{a b : P} → mul a b ≡ mul b a
   compat : ∀{a b : P} → ¡ (rel poset) a b → (∀{c : P} → ¡ (rel poset) (mul a c) (mul b c))

open MonPoset public

record Lineale (L : Set) : Set where
 constructor MkLineale
 field
   mposet : MonPoset L
   l-imp : L → L → L
   
   rlcomp : (a b : L) → ¡ (rel (poset mposet)) ((mul mposet) a (l-imp a b)) b
   adj : {a b y : L} → ¡ (rel (poset mposet)) (mul mposet y a) b → ¡ (rel (poset mposet)) y (l-imp a b)

open Lineale public
