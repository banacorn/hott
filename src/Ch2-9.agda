{-# OPTIONS --without-K --no-pattern-matching #-}

module Ch2-9 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2
open import Ch2-3
open import Ch2-4
open import Ch2-5
open import Ch2-6
open import Ch2-7
open import Ch2-8

open import Data.Product
open import Function using (id; _∘_)

-- happly (Definition 2.9.2)
happly : ∀ {a} {b} {A : Set a} {B : A → Set b}
  → {f g : (x : A) → B x}
  → (f ≡ g) → (f ~ g)
happly {_} {_} {A} {B} {f} {g} p = J ((x : A) → B x) D d f g p
  where
    D : (f g : (x : A) → B x) (p : f ≡ g) → Set _
    D f g p = f ~ g

    d : (x : (x : A) → B x) → D x x refl
    d f x = refl

postulate
  funext : ∀ {a} {b} {A : Set a} {B : A → Set b}
    → {f g : (x : A) → B x}
    → (f ~ g) → (f ≡ g)

Theorem-2-9-1 : ∀ {a} {b} {A : Set a} {B : A → Set b}
  → (f g : (x : A) → B x)
  → (f ≡ g) ≅ (f ~ g)
Theorem-2-9-1 {_} {_} {A} {B} f g = happly , (funext , α) , (funext , {!   !})

  where
    α : happly ∘ funext ~ id
    α p = J {!   !} D {!   !} f g (funext p)
      -- J ((x : A) → B x) D d f g (funext p)
      --
      where
        D : (f g : (x : A) → B x) (p : {!   !}) → Set _
        D f g p = {!   !}
          -- ((λ {x} → happly) ∘ funext) p ≡ id p
          -- ((λ {x} → happly) ∘ funext) p ≡ id p
          -- happly ∘ funext ~ id

        -- d : (x : (x : A) → B x) → D x x refl
        -- d x = refl

    -- happly-isequiv : isequiv (happly f g)
    -- happly-isequiv =


  -- where
  --   f : x ≡ y → ⊤
  --   f p = tt
  --
  --   f' : ⊤ → x ≡ y
  --   f' x = refl
  --
  --   α : (λ _ → f refl) ~ id
  --   α w = refl
  --
  --   β : (λ _ → refl) ~ id
  --   β w = J ⊤ D d x y w
  --     where
  --       D : (x y : ⊤) (p : x ≡ y) → Set _
  --       D x y p = refl ≡ id p
  --
  --       d : (x : ⊤) → D x x refl
  --       d x = refl
  --
  --   f-isequiv : isequiv f
  --   f-isequiv = (f' , α) , f' , β
