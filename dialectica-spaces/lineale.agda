module lineale where

open import nat
open import bool
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

_≤𝔹_ : 𝔹 → 𝔹 → 𝔹
tt ≤𝔹 ff = ff
_ ≤𝔹 _ = tt

isPost𝔹 : Poset 𝔹
isPost𝔹 = MkPoset _≤𝔹_ aux₁ aux₂ aux₃
 where
  aux₁ : {a : 𝔹} → a ≤𝔹 a ≡ tt
  aux₁ {tt} = refl
  aux₁ {ff} = refl

  aux₂ : {a b c : 𝔹} → a ≤𝔹 b ≡ tt → b ≤𝔹 c ≡ tt → a ≤𝔹 c ≡ tt
  aux₂ {tt}{tt}{tt} p₁ p₂ = refl
  aux₂ {tt}{tt}{ff} p₁ p₂ = p₂
  aux₂ {tt}{ff}{tt} p₁ p₂ = refl
  aux₂ {ff}{tt}{tt} p₁ p₂ = refl
  aux₂ {ff}{ff}{tt} p₁ p₂ = refl
  aux₂ {ff}{tt}{ff} p₁ p₂ = refl
  aux₂ {tt}{ff}{ff} p₁ p₂ = p₁
  aux₂ {ff}{ff}{ff} p₁ p₂ = refl

  aux₃ : {a b : 𝔹} → a ≤𝔹 b ≡ tt → b ≤𝔹 a ≡ tt → a ≡ b
  aux₃ {tt}{tt} p₁ p₂ = refl
  aux₃ {tt}{ff} p₁ p₂ = sym p₁
  aux₃ {ff}{tt} p₁ p₂ = p₂
  aux₃ {ff}{ff} p₁ p₂ = refl  

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

_⊗𝔹_ : 𝔹 → 𝔹 → 𝔹
tt ⊗𝔹 tt = tt
_ ⊗𝔹 _ = ff

isMonPoset𝔹 : MonPoset 𝔹
isMonPoset𝔹 = MkMonPoset _⊗𝔹_ tt isPost𝔹 aux₁ aux₂ aux₃ aux₄ aux₅
 where
  aux₁ : {a b c : 𝔹} → a ⊗𝔹 (b ⊗𝔹 c) ≡ (a ⊗𝔹 b) ⊗𝔹 c
  aux₁ {tt}{tt}{tt} = refl
  aux₁ {tt}{tt}{ff} = refl
  aux₁ {tt}{ff}{tt} = refl
  aux₁ {ff}{tt}{tt} = refl
  aux₁ {ff}{ff}{tt} = refl
  aux₁ {ff}{tt}{ff} = refl
  aux₁ {tt}{ff}{ff} = refl
  aux₁ {ff}{ff}{ff} = refl

  aux₂ : {a : 𝔹} → tt ⊗𝔹 a ≡ a
  aux₂ {tt} = refl
  aux₂ {ff} = refl

  aux₃ : {a : 𝔹} → a ⊗𝔹 tt ≡ a
  aux₃ {tt} = refl
  aux₃ {ff} = refl

  aux₄ : {a b : 𝔹} → a ⊗𝔹 b ≡ b ⊗𝔹 a
  aux₄ {tt}{tt} = refl
  aux₄ {tt}{ff} = refl
  aux₄ {ff}{tt} = refl
  aux₄ {ff}{ff} = refl

  aux₅ : {a b : 𝔹} → a ≤𝔹 b ≡ tt → {c : 𝔹} → (a ⊗𝔹 c) ≤𝔹 (b ⊗𝔹 c) ≡ tt
  aux₅ {tt}{tt} p₁ {tt} = refl
  aux₅ {tt}{tt} p₁ {ff} = refl
  aux₅ {tt}{ff} p₁ {tt} = p₁
  aux₅ {ff}{tt} p₁ {tt} = refl
  aux₅ {ff}{ff} p₁ {tt} = refl
  aux₅ {ff}{tt} p₁ {ff} = refl
  aux₅ {tt}{ff} p₁ {ff} = refl
  aux₅ {ff}{ff} p₁ {ff} = refl

isLargest : ∀{A : Set} → (A → A → 𝔹) → A → Set
isLargest {A} rel x = ∀{y : A} → ¡ rel y x

record Lineale (L : Set) : Set where
 constructor MkLineale
 field
   mposet : MonPoset L

   rlcomp : (a b : L) → Σ[ x ∈ L ]( isLargest (rel (poset mposet)) x × (¡ (rel (poset mposet)) ((mul mposet) a x) b ))

_→𝔹_ : 𝔹 → 𝔹 → 𝔹
tt →𝔹 tt = tt
tt →𝔹 ff = ff
ff →𝔹 tt = tt
ff →𝔹 ff = tt

isLineale𝔹 : Lineale 𝔹
isLineale𝔹 = MkLineale isMonPoset𝔹 (λ a b → a →𝔹 b , aux₁ , aux₂)
 where
  aux₁ : {a b y : 𝔹} → y ≤𝔹 (a →𝔹 b) ≡ tt
  aux₁ {tt}{tt}{tt} = refl
  aux₁ {tt}{tt}{ff} = refl
  aux₁ {tt}{ff}{tt} = {!!}
  aux₁ {ff}{tt}{tt} = refl
  aux₁ {ff}{ff}{tt} = refl
  aux₁ {ff}{tt}{ff} = refl
  aux₁ {tt}{ff}{ff} = refl
  aux₁ {ff}{ff}{ff} = refl
 
  aux₂ : {a b : 𝔹} → (a ⊗𝔹 (a →𝔹 b)) ≤𝔹 b ≡ tt
  aux₂ {tt}{tt} = refl
  aux₂ {tt}{ff} = refl
  aux₂ {ff}{tt} = refl  
  aux₂ {ff}{ff} = refl
