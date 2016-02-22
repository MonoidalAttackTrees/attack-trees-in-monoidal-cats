module lineale where

open import empty
open import nat
open import bool
open import bool-thms
open import eq
open import product

¡ : {A : Set} → (A → A → 𝔹) → A → A → Set
¡ r x y = r x y ≡ tt

record Poset (A : Set) : Set where
 constructor MkPoset
 field
   rel : A → A → 𝔹
   prefl : ∀{a : A} → ¡ rel a a
   ptrans : ∀{a b c : A} → ¡ rel a b → ¡ rel b c → ¡ rel a c
   pasym : ∀{a b : A} → ¡ rel a b → ¡ rel b a → a ≡ b

open Poset

data Three : Set where
  zero : Three
  half : Three
  one : Three

_≤2_ : 𝔹 → 𝔹 → 𝔹
tt ≤2 ff = ff
_ ≤2 _ = tt

isPoset2 : Poset 𝔹
isPoset2 = MkPoset _≤2_ aux₁ aux₂ aux₃
 where
  aux₁ : {a : 𝔹} → a ≤2 a ≡ tt
  aux₁ {tt} = refl
  aux₁ {ff} = refl

  aux₂ : {a b c : 𝔹} → a ≤2 b ≡ tt → b ≤2 c ≡ tt → a ≤2 c ≡ tt
  aux₂ {tt} {tt} {ff} x x₁ = x₁
  aux₂ {tt} {ff} {ff} x x₁ = x
  aux₂ {tt} {tt} {tt} x x₁ = refl
  aux₂ {ff} {tt} {tt} x x₁ = refl
  aux₂ {ff} {tt} {ff} x x₁ = refl
  aux₂ {ff} {ff} {tt} x x₁ = refl
  aux₂ {ff} {ff} {ff} x x₁ = refl
  aux₂ {tt} {ff} {tt} x x₁ = refl  

  aux₃ : {a b : 𝔹} → a ≤2 b ≡ tt → b ≤2 a ≡ tt → a ≡ b
  aux₃ {tt} {tt} x x₁ = refl
  aux₃ {tt} {ff} x x₁ = sym x
  aux₃ {ff} {tt} x x₁ = x₁
  aux₃ {ff} {ff} x x₁ = refl

_≤3_ : Three → Three → 𝔹
half ≤3 zero = ff
one ≤3 zero = ff
one ≤3 half = ff
_ ≤3 _ = tt

isPoset3 : Poset Three
isPoset3 = MkPoset _≤3_ (λ {a} → aux₁ {a}) (λ{a b c} → aux₂ {a}{b}{c}) aux₃
 where
   aux₁ : {a : Three} → a ≤3 a ≡ tt
   aux₁ {zero} = refl
   aux₁ {half} = refl
   aux₁ {one} = refl   

   aux₂ : {a b c : Three} → a ≤3 b ≡ tt → b ≤3 c ≡ tt → a ≤3 c ≡ tt
   aux₂ {zero} {zero} {zero} p₁ p₂ = refl
   aux₂ {zero} {zero} {half} p₁ p₂ = refl
   aux₂ {zero} {zero} {one} p₁ p₂ = refl
   aux₂ {zero} {half} {zero} p₁ p₂ = refl
   aux₂ {zero} {half} {half} p₁ p₂ = refl
   aux₂ {zero} {half} {one} p₁ p₂ = refl
   aux₂ {zero} {one} {zero} p₁ p₂ = refl
   aux₂ {zero} {one} {half} p₁ p₂ = refl
   aux₂ {zero} {one} {one} p₁ p₂ = refl
   aux₂ {half} {zero} {zero} p₁ p₂ = p₁
   aux₂ {half} {zero} {half} p₁ p₂ = refl
   aux₂ {half} {zero} {one} p₁ p₂ = refl
   aux₂ {half} {half} {zero} p₁ p₂ = p₂
   aux₂ {half} {half} {half} p₁ p₂ = refl
   aux₂ {half} {half} {one} p₁ p₂ = refl
   aux₂ {half} {one} {zero} p₁ p₂ = p₂
   aux₂ {half} {one} {half} p₁ p₂ = refl
   aux₂ {half} {one} {one} p₁ p₂ = refl
   aux₂ {one} {zero} {zero} p₁ p₂ = p₁
   aux₂ {one} {zero} {half} p₁ p₂ = p₁
   aux₂ {one} {zero} {one} p₁ p₂ = refl
   aux₂ {one} {half} {zero} p₁ p₂ = p₂
   aux₂ {one} {half} {half} p₁ p₂ = p₁
   aux₂ {one} {half} {one} p₁ p₂ = p₂
   aux₂ {one} {one} {zero} p₁ p₂ = p₂
   aux₂ {one} {one} {half} p₁ p₂ = p₂
   aux₂ {one} {one} {one} p₁ p₂ = refl

   aux₃ : {a b : Three} → a ≤3 b ≡ tt → b ≤3 a ≡ tt → a ≡ b
   aux₃ {zero} {zero} p₁ p₂ = refl
   aux₃ {zero} {half} p₁ p₂ = ⊥-elim (ff≡tt p₂)
   aux₃ {zero} {one} p₁ p₂ = ⊥-elim (ff≡tt p₂)
   aux₃ {half} {zero} p₁ p₂ = ⊥-elim (ff≡tt p₁)
   aux₃ {half} {half} p₁ p₂ = refl
   aux₃ {half} {one} p₁ p₂ = ⊥-elim (ff≡tt p₂)
   aux₃ {one} {zero} p₁ p₂ = ⊥-elim (ff≡tt p₁)
   aux₃ {one} {half} p₁ p₂ = ⊥-elim (ff≡tt p₁)
   aux₃ {one} {one} p₁ p₂ = refl

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

open MonPoset

compat-sym : ∀{P : Set}{p : MonPoset P}{a b : P} → ¡ (rel (poset p)) a b → (∀{c : P} → ¡ (rel (poset p)) ((mul p) c a) ((mul p) c b))
compat-sym {P}{MkMonPoset _⊗_ ut (MkPoset _≤_ r t s) asc li ri sm cp} {a}{b} p₁ {c} rewrite sm {c}{a} | sm {c}{b} = cp {a}{b} p₁ {c}

_⊗2_ : 𝔹 → 𝔹 → 𝔹
_⊗2_ = _&&_

isMonPoset2 : MonPoset 𝔹
isMonPoset2 = MkMonPoset _⊗2_ tt isPoset2 (λ {a b c} → aux₁ {a}{b}{c}) refl aux₂ (λ {a b} → aux₃ {a}{b}) aux₄
  where
    aux₁ : {a b c : 𝔹} → a && b && c ≡ (a && b) && c
    aux₁ {tt} {tt} {tt} = refl
    aux₁ {tt} {tt} {ff} = refl
    aux₁ {tt} {ff} {tt} = refl
    aux₁ {tt} {ff} {ff} = refl
    aux₁ {ff} {tt} {tt} = refl
    aux₁ {ff} {tt} {ff} = refl
    aux₁ {ff} {ff} {tt} = refl
    aux₁ {ff} {ff} {ff} = refl

    aux₂ : {a : 𝔹} → a && tt ≡ a
    aux₂ {tt} = refl
    aux₂ {ff} = refl

    aux₃ : {a b : 𝔹} → a && b ≡ b && a
    aux₃ {tt} {tt} = refl
    aux₃ {tt} {ff} = refl
    aux₃ {ff} {tt} = refl
    aux₃ {ff} {ff} = refl

    aux₄ : {a b : 𝔹} → a ≤2 b ≡ tt → {c : 𝔹} → (a && c) ≤2 (b && c) ≡ tt
    aux₄ {tt} {tt} x {tt} = refl
    aux₄ {tt} {tt} x {ff} = refl
    aux₄ {tt} {ff} x {tt} = x
    aux₄ {tt} {ff} x {ff} = refl
    aux₄ {ff} {tt} x {tt} = refl
    aux₄ {ff} {tt} x {ff} = refl
    aux₄ {ff} {ff} x {tt} = refl
    aux₄ {ff} {ff} x {ff} = refl

_⊗3_ : Three → Three → Three
zero ⊗3 zero = zero
zero ⊗3 half = zero
zero ⊗3 one = zero
half ⊗3 zero = zero
half ⊗3 half = half
half ⊗3 one = half
one ⊗3 zero = zero
one ⊗3 half = half
one ⊗3 one = one

assoc3 : {a b c : Three} → a ⊗3 (b ⊗3 c) ≡ (a ⊗3 b) ⊗3 c
assoc3 {zero} {zero} {zero} = refl
assoc3 {zero} {zero} {half} = refl
assoc3 {zero} {zero} {one} = refl
assoc3 {zero} {half} {zero} = refl
assoc3 {zero} {half} {half} = refl
assoc3 {zero} {half} {one} = refl
assoc3 {zero} {one} {zero} = refl
assoc3 {zero} {one} {half} = refl
assoc3 {zero} {one} {one} = refl
assoc3 {half} {zero} {zero} = refl
assoc3 {half} {zero} {half} = refl
assoc3 {half} {zero} {one} = refl
assoc3 {half} {half} {zero} = refl
assoc3 {half} {half} {half} = refl
assoc3 {half} {half} {one} = refl
assoc3 {half} {one} {zero} = refl
assoc3 {half} {one} {half} = refl
assoc3 {half} {one} {one} = refl
assoc3 {one} {zero} {zero} = refl
assoc3 {one} {zero} {half} = refl
assoc3 {one} {zero} {one} = refl
assoc3 {one} {half} {zero} = refl
assoc3 {one} {half} {half} = refl
assoc3 {one} {half} {one} = refl
assoc3 {one} {one} {zero} = refl
assoc3 {one} {one} {half} = refl
assoc3 {one} {one} {one} = refl

left-ident3 : {a : Three} → one ⊗3 a ≡ a
left-ident3 {zero} = refl
left-ident3 {half} = refl
left-ident3 {one} = refl

right-ident3 : {a : Three} → a ⊗3 one ≡ a
right-ident3 {zero} = refl
right-ident3 {half} = refl
right-ident3 {one} = refl

symm3 : {a b : Three} → a ⊗3 b ≡ b ⊗3 a
symm3 {zero} {zero} = refl
symm3 {zero} {half} = refl
symm3 {zero} {one} = refl
symm3 {half} {zero} = refl
symm3 {half} {half} = refl
symm3 {half} {one} = refl
symm3 {one} {zero} = refl
symm3 {one} {half} = refl
symm3 {one} {one} = refl

comp3 : {a b : Three} → a ≤3 b ≡ tt → {c : Three} → (a ⊗3 c) ≤3 (b ⊗3 c) ≡ tt
comp3 {zero} {zero} x {zero} = refl
comp3 {zero} {zero} x {half} = refl
comp3 {zero} {zero} x {one} = refl
comp3 {zero} {half} x {zero} = refl
comp3 {zero} {half} x {half} = refl
comp3 {zero} {half} x {one} = refl
comp3 {zero} {one} x {zero} = refl
comp3 {zero} {one} x {half} = refl
comp3 {zero} {one} x {one} = refl
comp3 {half} {zero} x {zero} = refl
comp3 {half} {zero} x {half} = x
comp3 {half} {zero} x {one} = x
comp3 {half} {half} x {zero} = refl
comp3 {half} {half} x {half} = refl
comp3 {half} {half} x {one} = refl
comp3 {half} {one} x {zero} = refl
comp3 {half} {one} x {half} = refl
comp3 {half} {one} x {one} = refl
comp3 {one} {zero} x {zero} = refl
comp3 {one} {zero} x {half} = x
comp3 {one} {zero} x {one} = x
comp3 {one} {half} x {zero} = refl
comp3 {one} {half} x {half} = refl
comp3 {one} {half} x {one} = x
comp3 {one} {one} x {zero} = refl
comp3 {one} {one} x {half} = refl
comp3 {one} {one} x {one} = refl

isMonPoset3 : MonPoset Three
isMonPoset3 = MkMonPoset _⊗3_ one isPoset3 (λ{a b c} → assoc3 {a}{b}{c}) left-ident3 right-ident3 (λ{a b} → symm3 {a}{b}) (λ {a b} → comp3 {a}{b})

record Lineale (L : Set) : Set where
 constructor MkLineale
 field
   mposet : MonPoset L
   l-imp : L → L → L
   
   rlcomp : (a b : L) → ¡ (rel (poset mposet)) ((mul mposet) a (l-imp a b)) b
   adj : {a b y : L} → ¡ (rel (poset mposet)) (mul mposet y a) b → ¡ (rel (poset mposet)) y (l-imp a b)

_→2_ : 𝔹 → 𝔹 → 𝔹
tt →2 ff = ff
_ →2 _ = tt

isLineale2 : Lineale 𝔹
isLineale2 = MkLineale isMonPoset2 _→2_ aux₁ aux₂
 where
   aux₁ : (a b : 𝔹) → (a && a →2 b) ≤2 b ≡ tt
   aux₁ tt tt = refl
   aux₁ tt ff = refl
   aux₁ ff tt = refl
   aux₁ ff ff = refl

   aux₂ : {a b y : 𝔹} → (y && a) ≤2 b ≡ tt → y ≤2 (a →2 b) ≡ tt
   aux₂ {tt} {tt} {tt} x = refl
   aux₂ {tt} {tt} {ff} x = refl
   aux₂ {tt} {ff} {tt} x = x
   aux₂ {tt} {ff} {ff} x = refl
   aux₂ {ff} {tt} {tt} x = refl
   aux₂ {ff} {tt} {ff} x = refl
   aux₂ {ff} {ff} {tt} x = refl
   aux₂ {ff} {ff} {ff} x = refl

_→3_ : Three → Three → Three
half →3 zero = zero
one →3 zero = zero
one →3 half = half
_ →3 _ = one

adj3 : {a b y : Three} → (y ⊗3 a) ≤3 b ≡ tt → y ≤3 (a →3 b) ≡ tt
adj3 {zero} {zero} {zero} p = refl
adj3 {zero} {zero} {half} p = refl
adj3 {zero} {zero} {one} p = refl
adj3 {zero} {half} {zero} p = refl
adj3 {zero} {half} {half} p = refl
adj3 {zero} {half} {one} p = refl
adj3 {zero} {one} {zero} p = refl
adj3 {zero} {one} {half} p = refl
adj3 {zero} {one} {one} p = refl
adj3 {half} {zero} {zero} p = refl
adj3 {half} {half} {zero} p = refl
adj3 {half} {half} {half} p = refl
adj3 {half} {half} {one} p = refl
adj3 {half} {one} {zero} p = refl
adj3 {half} {one} {half} p = refl
adj3 {half} {one} {one} p = refl
adj3 {one} {zero} {zero} p = refl
adj3 {one} {half} {zero} p = refl
adj3 {one} {half} {half} p = refl
adj3 {one} {one} {zero} p = refl
adj3 {one} {one} {half} p = refl
adj3 {one} {one} {one} p = refl
adj3 {half} {zero} {half} p = p
adj3 {half} {zero} {one} p = p
adj3 {one} {zero} {half} p = p
adj3 {one} {zero} {one} p = p
adj3 {one} {half} {one} p = p

rlcomp3 : (a b : Three) → (a ⊗3 (a →3 b)) ≤3 b ≡ tt
rlcomp3 zero zero = refl
rlcomp3 zero half = refl
rlcomp3 zero one = refl
rlcomp3 half zero = refl
rlcomp3 half half = refl
rlcomp3 half one = refl
rlcomp3 one zero = refl
rlcomp3 one half = refl
rlcomp3 one one = refl

isLineale : Lineale Three
isLineale = MkLineale isMonPoset3 _→3_ rlcomp3 (λ {a b y} → adj3 {a}{b}{y})
