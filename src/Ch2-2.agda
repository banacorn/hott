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

ap2 : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} {x y : A} {z w : B}
  → (f : A → B → C) (p : x ≡ y) (q : z ≡ w)
  → f x z ≡ f y w
ap2 {a} {b} {c} {A} {B} {C} {x} {y} {z} {w} f p q = J A D d x y p z w q f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set _
    D x y p = (a b : B) (q : z ≡ w) (f : A → B → C) → f x z ≡ f y w

    -- base case
    d : (x : A) → D x x refl
    d x z w q f = ap (f x) q

[_]∙ : {a : Level} {A : Set a} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z)
  → x ≡ z
[ p ]∙ q = p ∙ q

∙[_] : {a : Level} {A : Set a} {x y z : A}
  → (q : y ≡ z) (p : x ≡ y)
  → x ≡ z
∙[ p ] q = q ∙ p

-- -- -- cong₂ ::
-- [_]∙[_] : {a : Level} {A : Set a} {x y z : A}
--   → (p q : x ≡ y) (r s : y ≡ z)
--   → p ∙ r ≡ q ∙ s
-- [_]∙[_] {a} {A} {x} {y} {z} p q r s = {! ap2  !}


ap-refl : {a b : Level} {A : Set a} {B : Set b} {x : A}
  → (f : A → B)
  → ap {a} {b} {A} {B} {x} f refl ≡ refl
ap-refl f = refl

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
ap-id : {a : Level} {A : Set a} {x y : A}
  → (p : x ≡ y)
  → ap id p ≡ p
ap-id {a} {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = ap id p ≡ p

    -- base case
    d : (x : A) → D x x refl
    d x = refl
