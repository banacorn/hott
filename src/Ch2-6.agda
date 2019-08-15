{-# OPTIONS --without-K #-}

module Ch2-6 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2
open import Ch2-3
open import Ch2-4
open import Ch2-5

open import Data.Product
open import Function using (id; _∘_)

-- Definition 2.6.1
Definition-2-6-1 : ∀ {a b} {A : Set a} {B : Set b} {x y : A × B}
  → (p : x ≡ y)
  → proj₁ x ≡ proj₁ y × proj₂ x ≡ proj₂ y
Definition-2-6-1 {_} {_} {A} {B} {x} {y} p = J (A × B) D d x y p
  where
    D : (x y : A × B) (p : x ≡ y) → Set _
    D x y p = proj₁ x ≡ proj₁ y × proj₂ x ≡ proj₂ y

    d : (x : A × B) → D x x refl
    d x = refl , refl

-- Definition 2.6.3
Definition-2-6-3 : ∀ {i j} {A : Set i} {B : Set j} {a b : A} {a' b' : B}
  → a ≡ b × a' ≡ b' → (a , a') ≡ (b , b')
Definition-2-6-3 {_} {_} {A} {B} {a} {b} {a'} {b'} (fst , snd) = J A D d a b fst a' b' snd
  where
    D : (a b : A) (fst : a ≡ b) → Set _
    D a b fst = (a' b' : B) (snd : a' ≡ b') → (a , a') ≡ (b , b')

    d : (x : A) → D x x refl
    d x a' b' snd = J B E e a' b' snd x

      where
        E : (a' b' : B) (snd : a' ≡ b') → Set _
        E a' b' snd = (x : A) → (x , a') ≡ (x , b')

        e : (x : B) → E x x refl
        e x y = refl

-- Theorem 2.6.2
Theorem-2-6-2 : ∀ {a b} {A : Set a} {B : Set b} (x y : A × B)
  → (x ≡ y) ≅ (proj₁ x ≡ proj₁ y × proj₂ x ≡ proj₂ y)
Theorem-2-6-2 {_} {_} {A} {B} (a , a') (b , b') = Definition-2-6-1 , it-isequiv
  --
  where
    it-isequiv : isequiv Definition-2-6-1
    it-isequiv = (Definition-2-6-3 , α) , (Definition-2-6-3 , β)

      where
        α : Definition-2-6-1 ∘ Definition-2-6-3 ~ id
        α (fst , snd) = J A D d a b fst a' b' snd
          where
            D : (x y : A) (p : x ≡ y) → Set _
            D x y p = (x' y' : B) (snd : x' ≡ y')
              → (Definition-2-6-1 ∘ Definition-2-6-3) (p , snd) ≡ ((p , snd))

            d : (x : A) → D x x refl
            d x x' y' q = J B E e x' y' q
              where
                E : (x' y' : B) (q : x' ≡ y') → Set _
                E x' y' q = (Definition-2-6-1 ∘ Definition-2-6-3) (refl , q) ≡ ((refl , q))

                e : (x' : B) → E x' x' refl
                e x' = refl

        β : Definition-2-6-3 ∘ Definition-2-6-1 ~ id
        β p = J (A × B) D d (a , a') (b , b') p
          where
            D : (x y : A × B) (p : x ≡ y) → Set _
            D x y p = (Definition-2-6-3 ∘ Definition-2-6-1) p ≡ id p

            d : (x : A × B) → D x x refl
            d x = refl
