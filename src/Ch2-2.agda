{-# OPTIONS --without-K #-}

module Ch2-2 where

open import Ch2-1

open import Level

-- Lemma 2.2.1 (ap)
ap : {a b : Level} {A : Set a} {B : Set b} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → f x ≡ f y
ap {a} {b} {A} {B} {x} {y} f p = J {a} {a ⊔ b} A D d x y p f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set (a ⊔ b)
    D x y p = (f : A → B) → f x ≡ f y

    -- base case
    d : (x : A) → D x x refl
    d x f = refl
--
-- ap2 : {A B C : Set} {x y : A} {a b : B}
--   → (f : A → B → C) (p : x ≡ y) (q : a ≡ b)
--   → f x a ≡ f y b
-- ap2 {A} {B} {C} {x} {y} {a} {b} f p q = J A D d x y p a b q f
--   -- J A D d x y p f
--   where
--     -- the predicate
--     D : (x y : A) (p : x ≡ y) → Set
--     D x y p = (a b : B) (q : a ≡ b) (f : A → B → C) → f x a ≡ f y b
--
--     -- base case
--     d : (x : A) → D x x refl
--     d x a b q f = ap (f x) q


-- Lemma 2.2.2.i (ap respects _∙_)
ap-∙ : {A B : Set} {x y z : A}
  → (f : A → B)
  → (p : x ≡ y) (q : y ≡ z)
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ {A} {B} {x} {y} {z} f p q = J A D d x y p f z q
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = (f : A → B) (z : A) (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q

    -- base case
    d : (x : A) → D x x refl
    d x f z q = refl

-- Lemma 2.2.2.ii (ap respects ¬_)
ap-¬ : {A B : Set} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → ap f (¬ p) ≡ ¬ ap f p
ap-¬ {A} {B} {x} {y} f p = J A D d x y p f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = (f : A → B) → ap f (¬ p) ≡ ¬ ap f p

    -- base case
    d : (x : A) → D x x refl
    d x f = refl

open import Function using (_∘_; id)

-- Lemma 2.2.2.iii (ap respects function compos)
ap-∘ : {A B C : Set} {x y : A}
  → (f : A → B) (g : B → C)
  → (p : x ≡ y)
  → ap g (ap f p) ≡ ap (g ∘ f) p
ap-∘ {A} {B} {C} {x} {y} f g p = J A D d x y p f g
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = (f : A → B) → (g : B → C) → ap g (ap f p) ≡ ap (g ∘ f) p

    -- base case
    d : (x : A) → D x x refl
    d x f g = refl

-- Lemma 2.2.2.iv (ap respects identity function)
ap-id : {A : Set} {x y : A}
  → (p : x ≡ y)
  → ap id p ≡ p
ap-id {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = ap id p ≡ p

    -- base case
    d : (x : A) → D x x refl
    d x = refl
