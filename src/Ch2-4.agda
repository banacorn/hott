{-# OPTIONS --without-K #-}

module Ch2-4 where

open import Level hiding (lift)

open import Ch2-1

-- Definition 2.4.1 (homotopy)
_~_ : {a b : Level} {A : Set a} {P : A → Set b}
  → (f g : (z : A) → P z)
  → Set (a ⊔ b)
_~_ {a} {b} {A} {P} f g = ∀ (x : A) → f x ≡ g x
