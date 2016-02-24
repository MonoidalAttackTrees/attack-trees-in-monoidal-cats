open import prelude
open import lineale
open import lineale-thms

module DCSets (L : Set) (l-pf : Lineale L) where

_≤DC_ : L → L → Set
x ≤DC y = ¡ (rel (poset (mposet l-pf))) x y

reflDC : {a : L} → a ≤DC a
reflDC = prefl (poset (mposet l-pf))

transDC : {a b c : L} → a ≤DC b → b ≤DC c → a ≤DC c
transDC = ptrans (poset (mposet l-pf))

compatDC : {a : L} {b : L} → rel (poset (mposet l-pf)) a b ≡ tt →
      {c : L} → rel (poset (mposet l-pf)) (mul (mposet l-pf) a c) (mul (mposet l-pf) b c)
      ≡ tt
compatDC = compat (mposet l-pf)

_⊗L_ : L → L → L
x ⊗L y = mul (mposet l-pf) x y

unitDC = unit (mposet l-pf)

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (U → X → L))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (U → Y → X) ] (∀{u : U}{y : Y} → α u (F u y) ≤DC β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , (λ u z → F u (G (f u) z)), aux₁)
 where
   aux₁ : {u : U} {y : Z} → rel (poset (mposet l-pf)) (α u (F u (G (f u) y))) (γ (g (f u)) y) ≡ tt
   aux₁ {u}{z} = transDC (p₁ {u} {G (f u) z}) p₂
   
infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , curry snd , reflDC)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safely ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , α}{V , Y , β}{f , F , _} = refl , refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , α}{V , Y , β}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , α}{V , Y , β}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , α}
         {V , Y , β}
         {W , Z , γ}
         {f₁ , F₁ , _}
         {f₂ , F₂ , _}
         {g₁ , G₁ , _}
         {g₂ , G₂ , _}
         {j , J , _}
         (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , α}{V , Y , β}{W , Z , γ}{S , T , ι}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _}{V , Y , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _}{V , Y , _}{f , F , _} = refl , refl


-----------------------------------------------------------------------
-- SMC Structure                                                     --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → L) → (V → Y → L) → ((U × V) → (X × Y) → L)
_⊗ᵣ_ α β (u , v) (x , y) = (α u x) ⊗L (β v y)

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , α) ⊗ₒ (V , Y , β) = ((U × V) , (X × Y) , α ⊗ᵣ β)

F⊗ : ∀{Z T V X U Y : Set}{F : U → Z → X}{G : V → T → Y} → (U × V) → (Z × T) → (X × Y)
F⊗ {F = F}{G} (u , v) (z , t) = F u z , G v t
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {F = F}{G} , (λ {u} {y} → p⊗ {u}{y})
 where
  p⊗ : {u : Σ U (λ x → V)} {y : Σ Z (λ x → T)} →
      rel (poset (mposet l-pf)) ((α ⊗ᵣ β) u (F⊗ {F = F}{G = G} u y))
      ((γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y)
      ≡ tt
  p⊗ {u , v}{z , t} with compat-sym {L}{mposet l-pf}{(β v (G v t))}{(δ (g v) t)} p₂ {(γ (f u) z)}
  ... | cp₂ with compatDC (p₁ {u}{z}) {β v (G v t)}
  ... | cp₁ = transDC cp₁ cp₂

-- The unit for tensor:
ι : ⊤ → ⊤ → L
ι triv triv = unitDC

I : Obj
I = (⊤ , ⊤ , ι)

J : Obj
J = (⊤ , ⊤ , (λ x y → unitDC))

-- The left-unitor:
λ⊗-p : ∀{U X α}{u : Σ ⊤ (λ x → U)} {y : X} →
      rel (poset (mposet l-pf)) ((ι ⊗ᵣ α) u (triv , y)) (α (snd u) y) ≡
      tt
λ⊗-p {U}{X}{α}{(triv , u)}{x} rewrite left-ident (mposet l-pf) {(α u x)} = reflDC
   
λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
λ⊗ {(U , X , α)} = snd , (λ _ x → triv , x) , (λ {u y} → λ⊗-p {U}{X}{α}{u}{y})

λ⊗-inv : ∀{A : Obj} → Hom A (I ⊗ₒ A)
λ⊗-inv {(U , X , α)} = (λ u → triv , u) , (λ _ r → snd r) , (λ {u}{y} → λ⊗-inv-p {U}{X}{α}{u}{y})
 where
  λ⊗-inv-p : ∀{U X α}{u : U} {y : Σ ⊤ (λ x → X)} →
      rel (poset (mposet l-pf)) (α u (snd y)) ((ι ⊗ᵣ α) (triv , u) y) ≡
      tt
  λ⊗-inv-p {U}{X}{α}{u}{triv , x} rewrite left-ident (mposet l-pf) {(α u x)} = reflDC

-- The right-unitor:
ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
ρ⊗ {(U , X , α)} = fst , (λ r x → x , triv) , (λ {u}{y} → ρ⊗-p {U}{X}{α}{u}{y})
 where
  ρ⊗-p : ∀{U X α}{u : Σ U (λ x → ⊤)} {y : X} →
      rel (poset (mposet l-pf)) ((α ⊗ᵣ ι) u (y , triv)) (α (fst u) y) ≡
      tt
  ρ⊗-p {U}{X}{α}{(u , triv)}{x} rewrite right-ident (mposet l-pf) {(α u x)} = reflDC


ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
ρ⊗-inv {(U , X , α)} = (λ u → u , triv) , (λ u r → fst r) , (λ {u} {y} → ρ⊗-p-inv {U} {X} {α} {u} {y})
 where
   ρ⊗-p-inv : ∀{U X α}{u : U} {y : Σ X (λ x → ⊤)} →
      rel (poset (mposet l-pf)) (α u (fst y)) ((α ⊗ᵣ ι) (u , triv) y) ≡
      tt
   ρ⊗-p-inv {U}{X}{α}{u}{x , triv} rewrite right-ident (mposet l-pf) {(α u x)} = reflDC

-- Symmetry:
β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
β⊗ {(U , X , α)}{(V , Y , β)} = twist-× , (λ r₁ r₂ → twist-× r₂) , (λ {u y} → β⊗-p {U}{V}{Y}{X}{α}{β}{u}{y})
 where
   β⊗-p : ∀{U V Y X α β}{u : Σ U (λ x → V)} {y : Σ Y (λ x → X)} →
      rel (poset (mposet l-pf)) ((α ⊗ᵣ β) u (twist-× y))
      ((β ⊗ᵣ α) (twist-× u) y)
      ≡ tt
   β⊗-p {U}{V}{Y}{X}{α}{β}{u , v}{y , x} rewrite symm (mposet l-pf) {α u x}{β v y} = reflDC

-- The associator:
Fα-inv : ∀{ℓ}{U V W X Y Z : Set ℓ} → (U × (V × W)) → ((X × Y) × Z) → (X × (Y × Z))
Fα-inv (u , (v , w)) ((x , y) , z) = x , y , z
   
α⊗-inv : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
α⊗-inv {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , (λ {u} {y} → α-inv-cond {u} {y})
 where
   α-inv-cond : {u : Σ U (λ x → Σ V (λ x₁ → W))}
      {y : Σ (Σ X (λ x → Y)) (λ x → Z)} →
      rel (poset (mposet l-pf)) ((α ⊗ᵣ (β ⊗ᵣ γ)) u (Fα-inv u y))
      (((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y)
      ≡ tt
   α-inv-cond {u , (v , w)}{(x , y) , z} rewrite assoc (mposet l-pf) {α u x}{β v y}{γ w z} = reflDC


Fα : ∀{V W X Y U Z : Set} → ((U × V) × W) → (X × (Y × Z)) → ((X × Y) × Z)
Fα {V}{W}{X}{Y}{U}{Z} ((u , v) , w) (x , (y , z)) = (x , y) , z

α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα , (λ {u y} → α-cond {u}{y}))
 where
  α-cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}
       {y : Σ X (λ x → Σ Y (λ x₁ → Z))} →
      rel (poset (mposet l-pf)) (((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα u y))
      ((α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y)
      ≡ tt
  α-cond {(u , v) , w}{x , (y , z)} rewrite assoc (mposet l-pf) {α u x}{β v y}{γ w z} = reflDC

α⊗-id₁ : ∀{A B C} → (α⊗ {A}{B}{C}) ○ α⊗-inv ≡h id
α⊗-id₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ (Σ U (λ x → V)) (λ x → W)} → rl-assoc-× (lr-assoc-× a) ≡ a
   aux {(u , v) , w} = refl

   aux' : {a : Σ (Σ U (λ x → V)) (λ x → W)} → (λ z → Fα {V}{W}{X}{Y}{U}{Z} a (Fα-inv (lr-assoc-× a) z)) ≡ (λ y → y)
   aux' {(u , v), w} = ext-set aux''
    where
      aux'' : {a : Σ (Σ X (λ x → Y)) (λ x → Z)} → Fα ((u , v) , w) (Fα-inv (u , v , w) a) ≡ a
      aux'' {(x , y) , z} = refl

α⊗-id₂ : ∀{A B C} → (α⊗-inv {A}{B}{C}) ○ α⊗ ≡h id
α⊗-id₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ U (λ x → Σ V (λ x₁ → W))} → lr-assoc-× (rl-assoc-× a) ≡ a
   aux {u , (v , w)} = refl
   aux' : {a : Σ U (λ x → Σ V (λ x₁ → W))} → (λ z → Fα-inv {_}{U}{V}{W}{X}{Y}{Z} a (Fα (rl-assoc-× a) z)) ≡ (λ y → y)
   aux' {u , (v , w)} = ext-set aux''
    where
      aux'' : {a : Σ X (λ x → Σ Y (λ x₁ → Z))} → Fα-inv (u , v , w) (Fα ((u , v) , w) a) ≡ a
      aux'' {x , (y , z)} = refl
       
-- Internal hom:
⊸-cond : ∀{U V X Y : Set}{α : U → X → L}{β : V → Y → L}
  → Σ (U → V) (λ x → U → Y → X)
  → Σ U (λ x → Y)
  → L
⊸-cond {α = α}{β} (f , F) (u , y) = l-imp l-pf (α u (F u y)) (β (f u) y)

_⊸ₒ_ : Obj → Obj → Obj
(U , X , α) ⊸ₒ (V , Y , β) = ((U → V) × (U → Y → X)) , ((U × Y) , ⊸-cond {α = α}{β})

_⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ₒ B) (C ⊸ₒ D)
_⊸ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , (λ {u y} → cond {u}{y})
 where
  h : Σ (U → V) (λ x → U → Y → X) → Σ (W → S) (λ x → W → T → Z)
  h (i , I) = (λ w → g (i (f w))) , (λ w t → F w (I (f w) (G (i (f w)) t)))
  H : Σ (U → V) (λ x → U → Y → X) → Σ W (λ x → T) → Σ U (λ x → Y)
  H (i , I) (w , t) = f w , G (i (f w)) t
  cond : {u : Σ (U → V) (λ x → U → Y → X)} {y : Σ W (λ x → T)} →
      rel (poset (mposet l-pf)) (⊸-cond {α = α}{β} u (H u y)) (⊸-cond {α = γ}{δ} (h u) y) ≡ tt
  cond {i , I}{w , y} = l-imp-funct {L} {l-pf} p₁ p₂

cur : {A B C : Obj}
  → Hom (A ⊗ₒ B) C
  → Hom A (B ⊸ₒ C)
cur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ u → (λ v → f (u , v)) , (λ v z → snd (F (u , v) z))) , (λ u r → fst (F (u , (fst r)) (snd r))) , (λ {u y} → cond {u}{y})
 where
   cond : {u : U} {y : Σ V (λ x → Z)}
     → rel (poset (mposet l-pf)) (α u (fst (F (u , fst y) (snd y))))
      (⊸-cond {α = β}{γ} ((λ v → f (u , v)) , (λ v z → snd (F (u , v) z))) y)
      ≡ tt
   cond {u}{v , z} with p₁ {u , v}{z} 
   ... | p₂ with F (u , v) z
   ... | t₁ , t₂ rewrite sym (symm (mposet l-pf) {(β v t₂)}{(α u t₁)}) = adj l-pf p₂    

cur-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ₒ B) C}
  → f₁ ≡h f₂
  → cur f₁ ≡h cur f₂
cur-≡h {U , X , α}{V , Y , β}{W , Z , γ}
       {f₁ , F₁ , p₁}{f₂ , F₂ , p₂} (p₃ , p₄)
       rewrite p₃ | p₄ = refl , refl

uncur : {A B C : Obj}
  → Hom A (B ⊸ₒ C)
  → Hom (A ⊗ₒ B) C
uncur {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = let h = λ r → fst (f (fst r)) (snd r)
        H = λ r z → F (fst r) (snd r , z) , snd (f (fst r)) (snd r) z
     in h , (H , (λ {u y} → cond {u}{y}))
 where
  cond : {u : Σ U (λ x → V)} {y : Z} →
      rel (poset (mposet l-pf))
      ((α ⊗ᵣ β) u (F (fst u) (snd u , y) , snd (f (fst u)) (snd u) y))
      (γ (fst (f (fst u)) (snd u)) y)
      ≡ tt
  cond {u , v}{z} with p₁ {u}{v , z}
  ... | p₂ with f u
  ... | t₁ , t₂ rewrite symm (mposet l-pf) {α u (F u (v , z))}{β v (t₂ v z)} = adj-inv {L} {l-pf} p₂ 
  
cur-uncur-bij₁ : ∀{A B C}{f : Hom (A ⊗ₒ B) C}
  → uncur (cur f) ≡h f
cur-uncur-bij₁ {U , X , α}{V , Y , β}{W , Z , γ}{f , F , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
   aux₁ {u , v} = refl
   aux₂ : {a : Σ U (λ x → V)} → (λ z → fst (F (fst a , snd a) z) , snd (F (fst a , snd a) z)) ≡ F a
   aux₂ {u , v} = ext-set aux₃
    where
      aux₃ : {a : Z} → (fst (F (u , v) a) , snd (F (u , v) a)) ≡ F (u , v) a
      aux₃ {z} with F (u , v) z
      ... | x , y = refl

cur-uncur-bij₂ : ∀{A B C}{g : Hom A (B ⊸ₒ C)}
  → cur (uncur g) ≡h g
cur-uncur-bij₂ {U , X , α}{V , Y , β}{W , Z , γ}{g , G , p₁} = (ext-set aux) , ext-set (ext-set aux')
 where
  aux : {a : U} → ((λ v → fst (g a) v) , (λ v z → snd (g a) v z)) ≡ g a
  aux {u} with g u
  ... | i , I = refl
  aux' : {u : U}{r : Σ V (λ x → Z)} → G u (fst r , snd r) ≡ G u r
  aux' {u}{v , z} = refl

-- The of-course exponential:
!ₒ-cond : ∀{U X : Set} → (α : U → X → L) → U → 𝕃 X → L
!ₒ-cond {U}{X} α u [] = unit (mposet l-pf) 
!ₒ-cond {U}{X} α u (x :: xs) = (α u x) ⊗L (!ₒ-cond α u xs) 

!ₒ-cond-++ : ∀{U X : Set}{α : U → X → L}{u : U}{l₁ l₂ : 𝕃 X}
  → !ₒ-cond α u (l₁ ++ l₂) ≡ ((!ₒ-cond α u l₁) ⊗L (!ₒ-cond α u l₂))
!ₒ-cond-++ {U}{X}{α}{u}{[]}{l₂} =  sym (left-ident (mposet l-pf) { !ₒ-cond α u l₂}) 
!ₒ-cond-++ {U}{X}{α}{u}{x :: xs}{l₂} rewrite !ₒ-cond-++ {U}{X}{α}{u}{xs}{l₂} = assoc (mposet l-pf) {(α u x)}{(!ₒ-cond α u xs)}{(!ₒ-cond α u l₂)}

!ₒ : Obj → Obj
!ₒ (U , X , α) = U ,  X * , !ₒ-cond {U}{X} α

!ₐ-s : ∀{U Y X : Set}
  → (U → Y → X)
  → (U → Y * → X *)
!ₐ-s f u l = map (f u) l

!ₐ : {A B : Obj} → Hom A B → Hom (!ₒ A) (!ₒ B)
!ₐ {U , X , α}{V , Y , β} (f , F , p) = f , (!ₐ-s F , (λ {u y} → aux {u}{y}))
 where
   aux : {u : U} {y : 𝕃 Y} → rel (poset (mposet l-pf)) (!ₒ-cond α u (map (F u) y)) (!ₒ-cond β (f u) y) ≡ tt
   aux {u}{[]} =  prefl (poset (mposet l-pf)) 
   aux {u}{y :: ys} with aux {u}{ys}
   ... | IH = l-mul-funct {p = mposet l-pf} p IH

-- Of-course is a comonad:
ε : ∀{A} → Hom (!ₒ A) A
ε {U , X , α} = id-set , (λ u x → [ x ]) , (λ {u}{x} → cond {u}{x})
 where
  cond : {u : U} {y : X} → rel (poset (mposet l-pf))
      (mul (mposet l-pf) (α u y) (unit (mposet l-pf))) (α u y)
      ≡ tt
  cond {u}{x} rewrite right-ident (mposet l-pf) {α u x} = prefl (poset (mposet l-pf))

δ-s : {U X : Set} → U → 𝕃 (𝕃 X) → 𝕃 X
δ-s u xs = foldr _++_ [] xs
  
δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
δ {U , X , α} = id-set , δ-s , (λ {u ls} → cond {u}{ls})
 where
   cond : {u : U} {y : 𝕃 (𝕃 X)} →
      rel (poset (mposet l-pf)) (!ₒ-cond α u (foldr _++_ [] y))
      (!ₒ-cond (!ₒ-cond α) u y)
      ≡ tt
   cond {u}{[]} = prefl (poset (mposet l-pf))
   cond {u}{l :: ls} with !ₒ-cond-++ {U}{X}{α}{u}{l}{foldr _++_ [] ls}
   ... | p' rewrite p' = compat-sym {p = mposet l-pf} (cond {u} {ls})
   
comonand-diag₁ : ∀{A}
  → (δ {A}) ○ (!ₐ (δ {A})) ≡h (δ {A}) ○ (δ { !ₒ A})
comonand-diag₁ {U , X , α} = refl , ext-set (λ {x} → ext-set (λ {l} → aux {x} {l}))
 where
  aux : ∀{x : U}{l : 𝕃 (𝕃 (𝕃 X))}
    → foldr _++_ [] (!ₐ-s (λ u xs
    → foldr _++_ [] xs) x l) ≡ foldr _++_ [] (foldr _++_ [] l)
  aux {u}{[]} = refl
  aux {u}{x :: xs} rewrite aux {u}{xs} = foldr-append {_}{_}{X}{X}{x}{foldr _++_ [] xs}

comonand-diag₂ : ∀{A}
  → (δ {A}) ○ (ε { !ₒ A}) ≡h (δ {A}) ○ (!ₐ (ε {A}))
comonand-diag₂ {U , X , α} =
  refl , ext-set (λ {u} → ext-set (λ {l} → aux {l}))
  where
    aux : ∀{a : 𝕃 X} → a ++ [] ≡ foldr _++_ [] (map (λ x → x :: []) a)
    aux {[]} = refl
    aux {x :: xs} rewrite (++[] xs) | sym (foldr-map {_}{X}{xs}) = refl    
