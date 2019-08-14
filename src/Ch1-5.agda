{-# OPTIONS --without-K #-}

module Ch1-5 where

open import Data.Product

open import Ch2-1

uniq : ∀ {a b} {A : Set a} {B : Set b}
  → (x : A × B)
  → ((proj₁ x , proj₂ x) ≡ x)
uniq (fst , snd) = refl

ind : ∀ {a b c} {A : Set a} {B : Set b}
  → (C : A × B → Set c)
  → ((x : A) → (y : B) → C (x , y))
  → (p : A × B)
  → C p
ind C c (fst , snd) = c fst snd
