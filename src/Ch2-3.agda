{-# OPTIONS --without-K #-}

module Ch2-3 where

open import Level hiding (lift)

open import Ch2-1

-- Lemma 2.3.1 (transport)
transport : {a b : Level} {A : Set a} {x y : A}
  → (P : A → Set b)
  → (p : x ≡ y)
  → P x → P y
transport {a} {b} {A} {x} {y} P p = J {a} {a ⊔ suc b} A D d x y p P
  -- J A D d x y p P
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set (a ⊔ suc b)
    D x y p = (P : A → Set b) → P x → P y

    -- base case
    d : (x : A) → D x x refl
    d x P y = y

open import Data.Product

-- Lemma 2.3.2 (path lifting property)
lift : {a b : Level} {A : Set a} {x y : A}
  → (P : A → Set b)
  → (u : P x)
  → (p : x ≡ y)
  → (x , u) ≡ (y , transport P p u)
lift {a} {b} {A} {x} {y} P u p = J {a} {a ⊔ b} A D d x y p u
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set (a ⊔ b)
    D x y p = (u : P x) → (x , u) ≡ (y , transport P p u)

    -- base case
    d : (x : A) → D x x refl
    d x u = refl


-- Lemma 2.3.4 (dependent map)
apd : {a b : Level} {A : Set a} {x y : A}
  → {P : A → Set b}
  → (f : (z : A) → P z)
  → (p : x ≡ y)
  → transport P p (f x) ≡ f y
apd {a} {b} {A} {x} {y} {P} f p = J A D d x y p P f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (P : A → Set b) (f : (z : A) → P z) → transport P p (f x) ≡ f y

    -- base case
    d : (x : A) → D x x refl
    d x P f = refl

open import Function using (const; _∘_)

-- Lemma 2.3.5
transportconst : {a ℓ : Level} {A : Set a} {x y : A}
  → {B : Set ℓ}
  → (p : x ≡ y)
  → (b : B)
  → transport (const B) p b ≡ b
transportconst {a} {ℓ} {A} {x} {y} {B} p b = J A D d x y p B b
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (B : Set ℓ) (b : B) → transport (const B) p b ≡ b

    -- base case
    d : (x : A) → D x x refl
    d x B b = refl

open import Ch2-2

-- Lemma 2.3.8
lemma-2-3-8 : {a ℓ : Level} {A : Set a} {B : Set ℓ} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → apd f p ≡ transportconst p (f x) ∙ ap f p
lemma-2-3-8 {a} {ℓ} {A} {B} {x} {y} f p = J {a} {a ⊔ ℓ} A D d x y p f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (f : A → B) → apd f p ≡ transportconst p (f x) ∙ ap f p

    -- base case
    d : (x : A) → D x x refl
    d x f = refl

-- Lemma 2.3.9
lemma-2-3-9 : {a b : Level} {A : Set a} {x y z : A}
  → (P : A → Set b)
  → (p : x ≡ y)
  → (q : y ≡ z)
  → (u : P x)
  → transport P q (transport P p u) ≡ transport P (p ∙ q) u
lemma-2-3-9 {a} {b} {A} {x} {y} {z} P p q u = J A D d x y p P z q u
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set _
    D x y p = (P : A → Set b) (z : A) (q : y ≡ z) (u : P x)
      → transport P q (transport P p u) ≡ transport P (p ∙ q) u

    -- base case
    d : (x : A) → D x x refl
    d x P z q u = refl

-- Lemma 2.3.10
lemma-2-3-10 : {a b c : Level} {A : Set a} {B : Set b} {x y : A}
  → (P : B → Set c)
  → (f : A → B)
  → (p : x ≡ y)
  → (u : P (f x))
  → transport (P ∘ f) p u ≡ transport P (ap f p) u
lemma-2-3-10 {a} {b} {c} {A} {B} {x} {y} P f p u = J A D d x y p P f u
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set _
    D x y p = (P : B → Set c) (f : A → B) (u : P (f x))
      → transport (P ∘ f) p u ≡ transport P (ap f p) u

    -- base case
    d : (x : A) → D x x refl
    d x P f u = refl

-- Lemma 2.3.11
lemma-2-3-11 : {a b c : Level} {A : Set a} {x y : A}
  → (P : A → Set b) (Q : A → Set c)
  → (f : (z : A) → P z → Q z)
  → (p : x ≡ y)
  → (u : P x)
  → transport Q p (f x u) ≡ f y (transport P p u)
lemma-2-3-11 {a} {b} {c} {A} {x} {y} P Q f p u = J A D d x y p P Q f u
  -- J A D d x y p {!   !} {!   !} {!   !} {!   !}
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set _
    D x y p = (P : A → Set b) (Q : A → Set c) (f : (z : A) → P z → Q z) (u : P x)
      → transport Q p (f x u) ≡ f y (transport P p u)

    -- base case
    d : (x : A) → D x x refl
    d x P Q f u = refl
