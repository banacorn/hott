{-# OPTIONS --without-K #-}

module Ch2-5 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2
open import Ch2-3
open import Ch2-4

open import Data.Product
open import Function using (_∘_; id)

-- Example 2.5.1 (equivalence)
Example-2-5-1 : ∀ {a b} {A : Set a} {B : Set b}
  → (a a' : A) (b b' : B)
  → ((a , b) ≡ (a' , b')) ≅ ((a ≡ a') × (b ≡ b'))
Example-2-5-1 {_} {_} {A} {B} a a' b b' = f , f-isequiv

  where
    f : (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b'
    f eq = J (A × B) D d (a , b) (a' , b') eq
      where
        D : (x y : A × B) → (p : x ≡ y) → Set _
        D (a , b) (a' , b') p = a ≡ a' × b ≡ b'

        d : (x : A × B) → D x x refl
        d x = refl , refl

    f-isequiv : isequiv f
    f-isequiv = (g , α) , (g , β)
      where
        g : a ≡ a' × b ≡ b' → (a , b) ≡ (a' , b')
        g (fst , snd) = J A D d a a' fst b b' snd
          where
            D : (a a' : A) → (p : a ≡ a') → Set _
            D a a' p = (b b' : B) (q : b ≡ b') → (a , b) ≡ (a' , b')

            d : (x : A) → D x x refl
            d x b b' q = J B E e b b' q
              where
                E : (b b' : B) → (q : b ≡ b') → Set _
                E b b' q = (x , b) ≡ (x , b')

                e : (x : B) → E x x refl
                e x = refl

        α : f ∘ g ~ id
        α (refl , refl) = refl

        β : g ∘ f ~ id
        β refl = refl

        -- TODO: prove α & β with J


          -- J A D d a a' p b b' q f g
          -- where
          --   D : (a a' : A) → (p : a ≡ a') → Set _
          --   D a a' p = (b b' : B) (q : b ≡ b')
          --     → (f : (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b')
          --     → (g : a ≡ a' × b ≡ b' → (a , b) ≡ (a' , b'))
          --     → (f ∘ g) (p , q) ≡ id (p , q)
          --
          --   d : (x : A) → D x x refl
          --   d x b b' q f g = J B E e b b' q x f g
          --     where
          --       E : (b b' : B) → (q : b ≡ b') → Set _
          --       E b b' q = (a : A)
          --           (f : (a , b) ≡ (a , b') → a ≡ a × b ≡ b')
          --         → (g : a ≡ a × b ≡ b' → (a , b) ≡ (a , b'))
          --         → (f ∘ g) (refl , q) ≡ (refl , q)
          --
          --       e : (x : B) → E x x refl
          --       e x a f g = {!   !}
