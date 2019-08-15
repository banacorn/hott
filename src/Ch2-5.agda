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
    f : ∀ {a b a' b'} → (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b'
    f {a} {b} {a'} {b'} eq = J (A × B) D d (a , b) (a' , b') eq
      where
        D : (x y : A × B) → (p : x ≡ y) → Set _
        D (a , b) (a' , b') p = a ≡ a' × b ≡ b'

        d : (x : A × B) → D x x refl
        d x = refl , refl

    f-isequiv : isequiv f
    f-isequiv = (g , α) , (g , β)
      where
        g : ∀ {a b a' b'} → a ≡ a' × b ≡ b' → (a , b) ≡ (a' , b')
        g {a} {b} {a'} {b'} (fst , snd) = J A D d a a' fst b b' snd
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
        α (fst , snd) = J A D d a a' fst b b' snd
          where
            D : (x y : A) (p : x ≡ y) → Set _
            D x y p = (x' y' : B) (snd : x' ≡ y')
              → (f ∘ g) (p , snd) ≡ ((p , snd))

            d : (x : A) → D x x refl
            d x x' y' q = J B E e x' y' q
              where
                E : (x' y' : B) (q : x' ≡ y') → Set _
                E x' y' q = (f ∘ g) (refl , q) ≡ ((refl , q))

                e : (x' : B) → E x' x' refl
                e x' = refl

        β : g ∘ f ~ id
        β p = J (A × B) D d (a , b) (a' , b') p
          where
            D : (x y : A × B) (p : x ≡ y) → Set _
            D x y p = (g ∘ f) p ≡ p

            d : (x : A × B) → D x x refl
            d x = refl
