-----------------------------------------------------------------------
-- Definitions of concrete lineales.                                 --
-----------------------------------------------------------------------

module concrete-lineales where

open import prelude
open import lineale

-----------------------------------------------------------------------
-- The lineale 2                                                     --
-----------------------------------------------------------------------
Two : Set
Two = 𝔹

_≤2_ : Two → Two → 𝔹
tt ≤2 ff = ff
_ ≤2 _ = tt

_⊗2_ : Two → Two → Two
_⊗2_ = _&&_

_→2_ : Two → Two → Two
tt →2 ff = ff
_ →2 _ = tt

isPoset2 : Poset Two
isPoset2 = MkPoset _≤2_ aux₁ aux₂ aux₃
 where
  aux₁ : {a : Two} → a ≤2 a ≡ tt
  aux₁ {tt} = refl
  aux₁ {ff} = refl

  aux₂ : {a b c : Two} → a ≤2 b ≡ tt → b ≤2 c ≡ tt → a ≤2 c ≡ tt
  aux₂ {tt} {tt} {ff} x x₁ = x₁
  aux₂ {tt} {ff} {ff} x x₁ = x
  aux₂ {tt} {tt} {tt} x x₁ = refl
  aux₂ {ff} {tt} {tt} x x₁ = refl
  aux₂ {ff} {tt} {ff} x x₁ = refl
  aux₂ {ff} {ff} {tt} x x₁ = refl
  aux₂ {ff} {ff} {ff} x x₁ = refl
  aux₂ {tt} {ff} {tt} x x₁ = refl  

  aux₃ : {a b : Two} → a ≤2 b ≡ tt → b ≤2 a ≡ tt → a ≡ b
  aux₃ {tt} {tt} x x₁ = refl
  aux₃ {tt} {ff} x x₁ = sym x
  aux₃ {ff} {tt} x x₁ = x₁
  aux₃ {ff} {ff} x x₁ = refl
   
isMonPoset2 : MonPoset Two
isMonPoset2 = MkMonPoset _⊗2_ tt isPoset2 (λ {a b c} → aux₁ {a}{b}{c}) refl aux₂ (λ {a b} → aux₃ {a}{b}) aux₄
  where
    aux₁ : {a b c : Two} → a && b && c ≡ (a && b) && c
    aux₁ {tt} {tt} {tt} = refl
    aux₁ {tt} {tt} {ff} = refl
    aux₁ {tt} {ff} {tt} = refl
    aux₁ {tt} {ff} {ff} = refl
    aux₁ {ff} {tt} {tt} = refl
    aux₁ {ff} {tt} {ff} = refl
    aux₁ {ff} {ff} {tt} = refl
    aux₁ {ff} {ff} {ff} = refl

    aux₂ : {a : Two} → a && tt ≡ a
    aux₂ {tt} = refl
    aux₂ {ff} = refl

    aux₃ : {a b : Two} → a && b ≡ b && a
    aux₃ {tt} {tt} = refl
    aux₃ {tt} {ff} = refl
    aux₃ {ff} {tt} = refl
    aux₃ {ff} {ff} = refl

    aux₄ : {a b : Two} → a ≤2 b ≡ tt → {c : Two} → (a && c) ≤2 (b && c) ≡ tt
    aux₄ {tt} {tt} x {tt} = refl
    aux₄ {tt} {tt} x {ff} = refl
    aux₄ {tt} {ff} x {tt} = x
    aux₄ {tt} {ff} x {ff} = refl
    aux₄ {ff} {tt} x {tt} = refl
    aux₄ {ff} {tt} x {ff} = refl
    aux₄ {ff} {ff} x {tt} = refl
    aux₄ {ff} {ff} x {ff} = refl

isLineale2 : Lineale Two
isLineale2 = MkLineale isMonPoset2 _→2_ aux₁ aux₂
 where
   aux₁ : (a b : Two) → (a && a →2 b) ≤2 b ≡ tt
   aux₁ tt tt = refl
   aux₁ tt ff = refl
   aux₁ ff tt = refl
   aux₁ ff ff = refl

   aux₂ : {a b y : Two} → (a && y) ≤2 b ≡ tt → y ≤2 (a →2 b) ≡ tt
   aux₂ {tt} {tt} {tt} x = refl
   aux₂ {tt} {tt} {ff} x = refl
   aux₂ {tt} {ff} {tt} x = x
   aux₂ {tt} {ff} {ff} x = refl
   aux₂ {ff} {tt} {tt} x = refl
   aux₂ {ff} {tt} {ff} x = refl
   aux₂ {ff} {ff} {tt} x = refl
   aux₂ {ff} {ff} {ff} x = refl

-----------------------------------------------------------------------
-- The lineale 3                                                     --
-----------------------------------------------------------------------

data Three : Set where
  zero : Three
  half : Three
  one : Three

_≤3_ : Three → Three → 𝔹
half ≤3 zero = ff
one ≤3 zero = ff
one ≤3 half = ff
_ ≤3 _ = tt

_⊗3_ : Three → Three → Three
zero ⊗3 zero = zero
zero ⊗3 one = zero
one ⊗3 zero = zero
one ⊗3 one = one
zero ⊗3 half = zero
half ⊗3 zero = zero
half ⊗3 half = half
half ⊗3 one = half
one ⊗3 half = half


_→3_ : Three → Three → Three
half →3 zero = zero
one →3 zero = zero
one →3 half = half
_ →3 _ = one

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

adj3 : {a b y : Three} → (a ⊗3 y) ≤3 b ≡ tt → y ≤3 (a →3 b) ≡ tt
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

isLineale3 : Lineale Three
isLineale3 = MkLineale isMonPoset3 _→3_ rlcomp3 (λ {a b y} → adj3 {a}{b}{y})

-----------------------------------------------------------------------
-- The lineale 4                                                     --
-----------------------------------------------------------------------

data Four : Set where
  zero : Four
  quater : Four
  half : Four
  one : Four

_≤4_ : Four → Four → 𝔹
quater ≤4 zero = ff
half ≤4 zero = ff
one ≤4 zero = ff
half ≤4 quater = ff
one ≤4 quater = ff
one ≤4 half = ff
_ ≤4 _ = tt

isPoset4 : Poset Four
isPoset4 = MkPoset _≤4_ (λ {a} → refl4 {a}) (λ {a b c} → trans4 {a}{b}{c}) asym4
 where
  refl4 : {a : Four} → a ≤4 a ≡ tt
  refl4 {zero} = refl
  refl4 {quater} = refl
  refl4 {half} = refl
  refl4 {one} = refl

  trans4 : {a b c : Four} → a ≤4 b ≡ tt → b ≤4 c ≡ tt → a ≤4 c ≡ tt
  trans4 {zero} {zero} {zero} x x₁ = refl
  trans4 {zero} {zero} {quater} x x₁ = refl
  trans4 {zero} {zero} {half} x x₁ = refl
  trans4 {zero} {zero} {one} x x₁ = refl
  trans4 {zero} {quater} x x₁ = refl
  trans4 {zero} {half} {zero} x x₁ = refl
  trans4 {zero} {half} {quater} x x₁ = refl
  trans4 {zero} {half} {half} x x₁ = refl
  trans4 {zero} {half} {one} x x₁ = refl
  trans4 {zero} {one} {zero} x x₁ = refl
  trans4 {zero} {one} {quater} x x₁ = refl
  trans4 {zero} {one} {half} x x₁ = refl
  trans4 {zero} {one} {one} x x₁ = refl
  trans4 {quater} {zero} {zero} x x₁ = x
  trans4 {quater} {zero} {quater} x x₁ = refl
  trans4 {quater} {zero} {half} x x₁ = refl
  trans4 {quater} {zero} {one} x x₁ = refl
  trans4 {quater} {quater} {zero} x x₁ = x₁
  trans4 {quater} {quater} {quater} x x₁ = refl
  trans4 {quater} {quater} {half} x x₁ = refl
  trans4 {quater} {quater} {one} x x₁ = refl
  trans4 {quater} {half} {zero} x x₁ = x₁
  trans4 {quater} {half} {quater} x x₁ = refl
  trans4 {quater} {half} {half} x x₁ = refl
  trans4 {quater} {half} {one} x x₁ = refl
  trans4 {quater} {one} {zero} x x₁ = x₁
  trans4 {quater} {one} {quater} x x₁ = refl
  trans4 {quater} {one} {half} x x₁ = refl
  trans4 {quater} {one} {one} x x₁ = refl
  trans4 {half} {zero} {zero} x x₁ = x
  trans4 {half} {zero} {quater} x x₁ = x
  trans4 {half} {zero} {half} x x₁ = refl
  trans4 {half} {zero} {one} x x₁ = refl
  trans4 {half} {quater} {zero} x x₁ = x₁
  trans4 {half} {quater} {quater} x x₁ = x
  trans4 {half} {quater} {half} x x₁ = refl
  trans4 {half} {quater} {one} x x₁ = refl
  trans4 {half} {half} {zero} x x₁ = x₁
  trans4 {half} {half} {quater} x x₁ = x₁
  trans4 {half} {half} {half} x x₁ = refl
  trans4 {half} {half} {one} x x₁ = refl
  trans4 {half} {one} {zero} x x₁ = x₁
  trans4 {half} {one} {quater} x x₁ = x₁
  trans4 {half} {one} {half} x x₁ = refl
  trans4 {half} {one} {one} x x₁ = refl
  trans4 {one} {zero} {zero} x x₁ = x
  trans4 {one} {zero} {quater} x x₁ = x
  trans4 {one} {zero} {half} x x₁ = x
  trans4 {one} {zero} {one} x x₁ = refl
  trans4 {one} {quater} {zero} x x₁ = x
  trans4 {one} {quater} {quater} x x₁ = x
  trans4 {one} {quater} {half} x x₁ = x
  trans4 {one} {quater} {one} x x₁ = refl
  trans4 {one} {half} {zero} x x₁ = x₁
  trans4 {one} {half} {quater} x x₁ = x₁
  trans4 {one} {half} {half} x x₁ = x
  trans4 {one} {half} {one} x x₁ = refl
  trans4 {one} {one} {zero} x x₁ = x₁
  trans4 {one} {one} {quater} x x₁ = x₁
  trans4 {one} {one} {half} x x₁ = x₁
  trans4 {one} {one} {one} x x₁ = refl

  asym4 : {a b : Four} → a ≤4 b ≡ tt → b ≤4 a ≡ tt → a ≡ b
  asym4 {zero} {zero} x x₁ = refl
  asym4 {zero} {quater} x x₁ = ⊥-elim (ff≡tt x₁)
  asym4 {zero} {half} x x₁ = ⊥-elim (ff≡tt x₁)
  asym4 {zero} {one} x x₁ = ⊥-elim (ff≡tt x₁)
  asym4 {quater} {zero} x x₁ = ⊥-elim (ff≡tt x)
  asym4 {quater} {quater} x x₁ = refl
  asym4 {quater} {half} x x₁ = ⊥-elim (ff≡tt x₁)
  asym4 {quater} {one} x x₁ = ⊥-elim (ff≡tt x₁)
  asym4 {half} {zero} x x₁ = ⊥-elim (ff≡tt x)
  asym4 {half} {quater} x x₁ = ⊥-elim (ff≡tt x)
  asym4 {half} {half} x x₁ = refl
  asym4 {half} {one} x x₁ = ⊥-elim (ff≡tt x₁)
  asym4 {one} {zero} x x₁ = ⊥-elim (ff≡tt x)
  asym4 {one} {quater} x x₁ = ⊥-elim (ff≡tt x)
  asym4 {one} {half} x x₁ = ⊥-elim (ff≡tt x)
  asym4 {one} {one} x x₁ = refl

_⊗4_ : Four → Four → Four
zero ⊗4 zero = zero
zero ⊗4 one = zero
one ⊗4 zero = zero
one ⊗4 one = one
zero ⊗4 half = zero
half ⊗4 zero = zero
half ⊗4 half = half
half ⊗4 one = half
one ⊗4 half = half
zero ⊗4 quater = zero
quater ⊗4 zero = zero
quater ⊗4 quater = quater
quater ⊗4 half = quater
quater ⊗4 one = quater
half ⊗4 quater = quater
one ⊗4 quater = quater

isMonPoset4 : MonPoset Four
isMonPoset4 = MkMonPoset _⊗4_ one isPoset4 (λ {a b c} → assoc4 {a}{b}{c}) left-ident4 right-ident4 (λ {a b} → symm4 {a}{b}) (λ {a b} → compat4 {a}{b})
 where
  assoc4 : {a b c : Four} → a ⊗4 (b ⊗4 c) ≡ (a ⊗4 b) ⊗4 c
  assoc4 {zero} {zero} {zero} = refl
  assoc4 {zero} {zero} {quater} = refl
  assoc4 {zero} {zero} {half} = refl
  assoc4 {zero} {zero} {one} = refl
  assoc4 {zero} {quater} {zero} = refl
  assoc4 {zero} {quater} {quater} = refl
  assoc4 {zero} {quater} {half} = refl
  assoc4 {zero} {quater} {one} = refl
  assoc4 {zero} {half} {zero} = refl
  assoc4 {zero} {half} {quater} = refl
  assoc4 {zero} {half} {half} = refl
  assoc4 {zero} {half} {one} = refl
  assoc4 {zero} {one} {zero} = refl
  assoc4 {zero} {one} {quater} = refl
  assoc4 {zero} {one} {half} = refl
  assoc4 {zero} {one} {one} = refl
  assoc4 {quater} {zero} {zero} = refl
  assoc4 {quater} {zero} {quater} = refl
  assoc4 {quater} {zero} {half} = refl
  assoc4 {quater} {zero} {one} = refl
  assoc4 {quater} {quater} {zero} = refl
  assoc4 {quater} {quater} {quater} = refl
  assoc4 {quater} {quater} {half} = refl
  assoc4 {quater} {quater} {one} = refl
  assoc4 {quater} {half} {zero} = refl
  assoc4 {quater} {half} {quater} = refl
  assoc4 {quater} {half} {half} = refl
  assoc4 {quater} {half} {one} = refl
  assoc4 {quater} {one} {zero} = refl
  assoc4 {quater} {one} {quater} = refl
  assoc4 {quater} {one} {half} = refl
  assoc4 {quater} {one} {one} = refl
  assoc4 {half} {zero} {zero} = refl
  assoc4 {half} {zero} {quater} = refl
  assoc4 {half} {zero} {half} = refl
  assoc4 {half} {zero} {one} = refl
  assoc4 {half} {quater} {zero} = refl
  assoc4 {half} {quater} {quater} = refl
  assoc4 {half} {quater} {half} = refl
  assoc4 {half} {quater} {one} = refl
  assoc4 {half} {half} {zero} = refl
  assoc4 {half} {half} {quater} = refl
  assoc4 {half} {half} {half} = refl
  assoc4 {half} {half} {one} = refl
  assoc4 {half} {one} {zero} = refl
  assoc4 {half} {one} {quater} = refl
  assoc4 {half} {one} {half} = refl
  assoc4 {half} {one} {one} = refl
  assoc4 {one} {zero} {zero} = refl
  assoc4 {one} {zero} {quater} = refl
  assoc4 {one} {zero} {half} = refl
  assoc4 {one} {zero} {one} = refl
  assoc4 {one} {quater} {zero} = refl
  assoc4 {one} {quater} {quater} = refl
  assoc4 {one} {quater} {half} = refl
  assoc4 {one} {quater} {one} = refl
  assoc4 {one} {half} {zero} = refl
  assoc4 {one} {half} {quater} = refl
  assoc4 {one} {half} {half} = refl
  assoc4 {one} {half} {one} = refl
  assoc4 {one} {one} {zero} = refl
  assoc4 {one} {one} {quater} = refl
  assoc4 {one} {one} {half} = refl
  assoc4 {one} {one} {one} = refl

  left-ident4 : {a : Four} → one ⊗4 a ≡ a
  left-ident4 {zero} = refl
  left-ident4 {quater} = refl
  left-ident4 {half} = refl
  left-ident4 {one} = refl

  right-ident4 : {a : Four} → a ⊗4 one ≡ a
  right-ident4 {zero} = refl
  right-ident4 {quater} = refl
  right-ident4 {half} = refl
  right-ident4 {one} = refl

  symm4 : {a b : Four} → a ⊗4 b ≡ b ⊗4 a
  symm4 {zero} {zero} = refl
  symm4 {zero} {quater} = refl
  symm4 {zero} {half} = refl
  symm4 {zero} {one} = refl
  symm4 {quater} {zero} = refl
  symm4 {quater} {quater} = refl
  symm4 {quater} {half} = refl
  symm4 {quater} {one} = refl
  symm4 {half} {zero} = refl
  symm4 {half} {quater} = refl
  symm4 {half} {half} = refl
  symm4 {half} {one} = refl
  symm4 {one} {zero} = refl
  symm4 {one} {quater} = refl
  symm4 {one} {half} = refl
  symm4 {one} {one} = refl

  compat4 : {a b : Four} → a ≤4 b ≡ tt → {c : Four} → (a ⊗4 c) ≤4 (b ⊗4 c) ≡ tt
  compat4 {zero} {zero} x {zero} = refl
  compat4 {zero} {zero} x {quater} = refl
  compat4 {zero} {zero} x {half} = refl
  compat4 {zero} {zero} x {one} = refl
  compat4 {zero} {quater} x {zero} = refl
  compat4 {zero} {quater} x {quater} = refl
  compat4 {zero} {quater} x {half} = refl
  compat4 {zero} {quater} x {one} = refl
  compat4 {zero} {half} x {zero} = refl
  compat4 {zero} {half} x {quater} = refl
  compat4 {zero} {half} x {half} = refl
  compat4 {zero} {half} x {one} = refl
  compat4 {zero} {one} x {zero} = refl
  compat4 {zero} {one} x {quater} = refl
  compat4 {zero} {one} x {half} = refl
  compat4 {zero} {one} x {one} = refl
  compat4 {quater} {zero} x {zero} = refl
  compat4 {quater} {zero} x {quater} = x
  compat4 {quater} {zero} x {half} = x
  compat4 {quater} {zero} x {one} = x
  compat4 {quater} {quater} x {zero} = refl
  compat4 {quater} {quater} x {quater} = refl
  compat4 {quater} {quater} x {half} = refl
  compat4 {quater} {quater} x {one} = refl
  compat4 {quater} {half} x {zero} = refl
  compat4 {quater} {half} x {quater} = refl
  compat4 {quater} {half} x {half} = refl
  compat4 {quater} {half} x {one} = refl
  compat4 {quater} {one} x {zero} = refl
  compat4 {quater} {one} x {quater} = refl
  compat4 {quater} {one} x {half} = refl
  compat4 {quater} {one} x {one} = refl
  compat4 {half} {zero} x {zero} = refl
  compat4 {half} {zero} x {quater} = x
  compat4 {half} {zero} x {half} = x 
  compat4 {half} {zero} x {one} = x
  compat4 {half} {quater} x {zero} = refl
  compat4 {half} {quater} x {quater} = refl
  compat4 {half} {quater} x {half} = x
  compat4 {half} {quater} x {one} = x
  compat4 {half} {half} x {zero} = refl
  compat4 {half} {half} x {quater} = refl
  compat4 {half} {half} x {half} = refl
  compat4 {half} {half} x {one} = refl
  compat4 {half} {one} x {zero} = refl
  compat4 {half} {one} x {quater} = refl
  compat4 {half} {one} x {half} = refl
  compat4 {half} {one} x {one} = refl
  compat4 {one} {zero} x {zero} = refl
  compat4 {one} {zero} x {quater} = x
  compat4 {one} {zero} x {half} = x
  compat4 {one} {zero} x {one} = x
  compat4 {one} {quater} x {zero} = refl
  compat4 {one} {quater} x {quater} = refl
  compat4 {one} {quater} x {half} = x
  compat4 {one} {quater} x {one} = x
  compat4 {one} {half} x {zero} = refl
  compat4 {one} {half} x {quater} = refl
  compat4 {one} {half} x {half} = refl
  compat4 {one} {half} x {one} = x
  compat4 {one} {one} x {zero} = refl
  compat4 {one} {one} x {quater} = refl
  compat4 {one} {one} x {half} = refl
  compat4 {one} {one} x {one} = refl

_→4_ : Four → Four → Four
one →4 zero = zero
half →4 zero = zero
one →4 half = half
quater →4 zero = zero
half →4 quater = quater
one →4 quater = quater
_ →4 _ = one

isLineale4 : Lineale Four
isLineale4 = MkLineale isMonPoset4 _→4_ rlcomp4 (λ {a b y} → adj4 {a}{b}{y})
 where
  rlcomp4 : (a b : Four) → (a ⊗4 (a →4 b)) ≤4 b ≡ tt
  rlcomp4 zero zero = refl
  rlcomp4 zero quater = refl
  rlcomp4 zero half = refl
  rlcomp4 zero one = refl
  rlcomp4 quater zero = refl
  rlcomp4 quater quater = refl
  rlcomp4 quater half = refl
  rlcomp4 quater one = refl
  rlcomp4 half zero = refl
  rlcomp4 half quater = refl
  rlcomp4 half half = refl
  rlcomp4 half one = refl
  rlcomp4 one zero = refl
  rlcomp4 one quater = refl
  rlcomp4 one half = refl
  rlcomp4 one one = refl

  adj4 : {a b y : Four} → (a ⊗4 y) ≤4 b ≡ tt → y ≤4 (a →4 b) ≡ tt
  adj4 {zero} {zero} {zero} x = refl
  adj4 {zero} {zero} {quater} x = refl
  adj4 {zero} {zero} {half} x = refl
  adj4 {zero} {zero} {one} x = refl
  adj4 {zero} {quater} {zero} x = refl
  adj4 {zero} {quater} {quater} x = refl
  adj4 {zero} {quater} {half} x = refl
  adj4 {zero} {quater} {one} x = refl
  adj4 {zero} {half} {zero} x = refl
  adj4 {zero} {half} {quater} x = refl
  adj4 {zero} {half} {half} x = refl
  adj4 {zero} {half} {one} x = refl
  adj4 {zero} {one} {zero} x = refl
  adj4 {zero} {one} {quater} x = refl
  adj4 {zero} {one} {half} x = refl
  adj4 {zero} {one} {one} x = refl
  adj4 {quater} {zero} {zero} x = refl
  adj4 {quater} {zero} {quater} x = x
  adj4 {quater} {zero} {half} x = x
  adj4 {quater} {zero} {one} x = x
  adj4 {quater} {quater} {zero} x = refl
  adj4 {quater} {quater} {quater} x = refl
  adj4 {quater} {quater} {half} x = refl
  adj4 {quater} {quater} {one} x = refl
  adj4 {quater} {half} {zero} x = refl
  adj4 {quater} {half} {quater} x = refl
  adj4 {quater} {half} {half} x = refl
  adj4 {quater} {half} {one} x = refl
  adj4 {quater} {one} {zero} x = refl
  adj4 {quater} {one} {quater} x = refl
  adj4 {quater} {one} {half} x = refl
  adj4 {quater} {one} {one} x = refl
  adj4 {half} {zero} {zero} x = refl
  adj4 {half} {zero} {quater} x = x
  adj4 {half} {zero} {half} x = x
  adj4 {half} {zero} {one} x = x
  adj4 {half} {quater} {zero} x = refl
  adj4 {half} {quater} {quater} x = refl
  adj4 {half} {quater} {half} x = x
  adj4 {half} {quater} {one} x = x
  adj4 {half} {half} {zero} x = refl
  adj4 {half} {half} {quater} x = refl
  adj4 {half} {half} {half} x = refl
  adj4 {half} {half} {one} x = refl
  adj4 {half} {one} {zero} x = refl
  adj4 {half} {one} {quater} x = refl
  adj4 {half} {one} {half} x = refl
  adj4 {half} {one} {one} x = refl
  adj4 {one} {zero} {zero} x = refl
  adj4 {one} {zero} {quater} x = x
  adj4 {one} {zero} {half} x = x
  adj4 {one} {zero} {one} x = x
  adj4 {one} {quater} {zero} x = refl
  adj4 {one} {quater} {quater} x = refl
  adj4 {one} {quater} {half} x = x
  adj4 {one} {quater} {one} x = x
  adj4 {one} {half} {zero} x = refl
  adj4 {one} {half} {quater} x = refl
  adj4 {one} {half} {half} x = refl
  adj4 {one} {half} {one} x = x
  adj4 {one} {one} {zero} x = refl
  adj4 {one} {one} {quater} x = refl
  adj4 {one} {one} {half} x = refl
  adj4 {one} {one} {one} x = refl
