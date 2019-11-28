{-# OPTIONS --without-K --no-pattern-matching #-}

module Ch2-8 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2
open import Ch2-3
open import Ch2-4
open import Ch2-5
open import Ch2-6
open import Ch2-7

open import Data.Product
open import Data.Unit
open import Function using (id; _∘_)

Theorem-2-8-1 : (x y : ⊤) → (x ≡ y) ≅ ⊤
Theorem-2-8-1 x y = f , f-isequiv

  where
    f : x ≡ y → ⊤
    f p = tt

    f' : ⊤ → x ≡ y
    f' x = refl

    α : (λ _ → f refl) ~ id
    α w = refl

    β : (λ _ → refl) ~ id
    β w = J ⊤ D d x y w
      where
        D : (x y : ⊤) (p : x ≡ y) → Set _
        D x y p = refl ≡ id p

        d : (x : ⊤) → D x x refl
        d x = refl

    f-isequiv : isequiv f
    f-isequiv = (f' , α) , f' , β
