module lineale-thms where

open import prelude
open import lineale

compat-sym : ∀{P : Set}{p : MonPoset P}{a b : P} → ¡ (rel (poset p)) a b → (∀{c : P} → ¡ (rel (poset p)) ((mul p) c a) ((mul p) c b))
compat-sym {P}{MkMonPoset _⊗_ ut (MkPoset _≤_ r t s) asc li ri sm cp} {a}{b} p₁ {c} rewrite sm {c}{a} | sm {c}{b} = cp {a}{b} p₁ {c}
