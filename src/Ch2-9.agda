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

Theorem-2-9-1 : ∀ {a} {b} {A : Set a} {B : A → Set b}
  → (f g : (x : A) → B x)
  → (f ≡ g) ≅ (f ~ g)
Theorem-2-9-1 {_} {_} {A} {B} f g = happly , (funext , α) , (funext , {!   !})
  -- (λ x → happly (funext x)) ~ (λ x → x)
  where
    α : happly ∘ funext ~ id
    α p = J ((x : A) → B x) D d f g (funext p) p

      where
        D : (f g : (x : A) → B x) → f ≡ g → Set _
        D f g p' = happly {f = f} {g} ∘ funext ~ id

        d : (y : (x : A) → B x) → D y y refl
        d y p = {! happly (funext p)  !}
    -- α : ∀ h → happly ∘ funext h ~ h
    -- α p = J ((x : A) → B x) D d f g (funext p) p
    --   where
    --     D : (f g : (x : A) → B x) → f ≡ g → Set _
    --     D f g p = (q : (x : A) → f x ≡ g x) → (happly {f = f} {g} (funext q)) ≡ id q
    --
    --     d : (x : (x : A) → B x) → D x x refl
    --     d x p = {! p id  !}

    -- β :  funext ? ∘ happly ~ ?
    -- β p = {!   !}

Theorem-2-9-4 : ∀ {a} {b} {X : Set a}
  → (x₁ x₂ : X)
  → (p : x₁ ≡ x₂)
  → (A B : X → Set b)
  → (f : A x₁ → B x₁)
  → transport {a} {b} (λ x → A x → B x) p f ≡ λ x → transport B p (f (transport A (¬ p) x))
Theorem-2-9-4 x₁ x₂ p A B f = {!   !}
