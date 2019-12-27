{-# OPTIONS --without-K --no-pattern-matching #-}
-- {-# OPTIONS --without-K #-}

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

  Π-comp : ∀ {a} {b} {A : Set a} {B : A → Set b}
    → (f g : (x : A) → B x)
    → (h : f ~ g)
    → happly (funext h) ~ h

  Π-elim : ∀ {a} {b} {A : Set a} {B : A → Set b}
    → (f g : (x : A) → B x)
    → (p : f ≡ g)
    → p ≡ funext (happly p)

Theorem-2-9-1 : ∀ {a} {b} {A : Set a} {B : A → Set b}
  → (f g : (x : A) → B x)
  → (f ≡ g) ≅ (f ~ g)
Theorem-2-9-1 {a} {b} {A} {B} f g =
  happly ,
    (funext , (λ x → funext (Π-comp f g x))) ,
    (funext , λ x → ¬ (Π-elim f g x))


--       B x₁      B x₂
--     f  |         |
--       A x₁     x : A x₂
--             p
-- X      x₁ ----> x₂

Theorem-2-9-4 : ∀ {a} {b} {X : Set a}
  → (x₁ x₂ : X)
  → (p : x₁ ≡ x₂)
  → (A B : X → Set b)
  → (f : A x₁ → B x₁)
  → transport (λ x → A x → B x) p f ≡ λ x → transport B p (f (transport A (¬ p) x))
Theorem-2-9-4 {a} {b} {X} x₁ x₂ p A B f = J X D d x₁ x₂ p f
  --
  where
    D : (x₁ x₂ : X) → x₁ ≡ x₂ → Set _
    D x₁ x₂ p = (f : A x₁ → B x₁) → transport (λ x → A x → B x) p f ≡ (λ x → transport B p (f (transport A (¬ p) x)))

    d : (x : X) → D x x refl
    d x f = refl

    --       B x₁ a'        B x₂
    --     f    |            |
    --     a' :  A x₁     a : A x₂
    --             p
    -- X      x₁ ----> x₂


Theorem-2-9-5 : ∀ {α} {b} {c} {X : Set α}
  → (x₁ x₂ : X)
  → (p : x₁ ≡ x₂)
  → (A : X → Set b)
  → (B : (x : X) → A x → Set c)
  → (f : (a : A x₁) → B x₁ a)
  → (a : A x₂)
  → transport (λ x → (a : A x) → B x a) p f a
        ≡ transport (λ w → B (proj₁ w) (proj₂ w)) (¬ {! pair≡ {α} {b} {X} {A x₂} {x₂ , a} {x₁ , transport A ? a}  !}) (f (transport A (¬ p) a))
    -- transport (λ x → A x → B x) p f ≡ λ x → transport B p (f (transport A (¬ p) x))
Theorem-2-9-5 = {!   !}



--       B x         B y
--     f  |           |    g
--   a : A x         A y
--             p
-- X      x ------> y

Theorem-2-9-6 : {!   !}
Theorem-2-9-6 = {!   !}

Theorem-2-9-7 : ∀ {α} {b} {c} {X : Set α}
  → (x y : X)
  → (p : x ≡ y)
  → (A : X → Set b)
  → (B : (x : X) → A x → Set c)
  → (f : (a : A x) → B x a)
  → (g : (a : A y) → B y a)
  → (transport {!   !}  p f ≡ g) ≅ {!   !}
Theorem-2-9-7 = {!   !}
