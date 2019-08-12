{-# OPTIONS --without-K #-}

module Ch2-3 where

open import Level hiding (lift)

open import Ch2-1

-- lemma-2-3.1 (transport)
transport : {a : Level} (b : Level) {A : Set a} {x y : A}
  → (P : A → Set (a ⊔ b))
  → (p : x ≡ y)
  → P x → P y
transport {a} b {A} {x} {y} P p = J A D d x y p P
  -- J A D d x y p P
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set (suc a ⊔ suc b)
    D x y p = (P : A → Set (a ⊔ b)) → P x → P y

    -- base case
    d : (x : A) → D x x refl
    d x P y = y

open import Data.Product

-- lemma-2-3.2 (path lifting property)
lift : {a b : Level} {A : Set a} {x y : A}
  → (P : A → Set (a ⊔ b))
  → (u : P x)
  → (p : x ≡ y)
  → (x , u) ≡ (y , transport b P p u)
lift {a} {b} {A} {x} {y} P u p = J {b = b} A D d x y p u
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (u : P x) → (x , u) ≡ (y , transport b P p u)

    -- base case
    d : (x : A) → D x x refl
    d x u = refl


-- lemma-2-3.4 (dependent map)
apd : {a : Level} (b : Level) {A : Set a} {x y : A}
  → {P : A → Set (a ⊔ b)}
  → (f : (z : A) → P z)
  → (p : x ≡ y)
  → transport b P p (f x) ≡ f y
apd {a} b {A} {x} {y} {P} f p = J A D d x y p P f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (P : A → Set (a ⊔ b)) (f : (z : A) → P z) → transport b P p (f x) ≡ f y

    -- base case
    d : (x : A) → D x x refl
    d x P f = refl

open import Function using (const)

-- lemma-2-3-5
transportconst : {a : Level} (ℓ : Level) {A : Set a} {x y : A}
  → {B : Set (a ⊔ ℓ)}
  → (p : x ≡ y)
  → (b : B)
  → transport ℓ (const B) p b ≡ b
transportconst {a} ℓ {A} {x} {y} {B} p b = J A D d x y p B b
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (B : Set (a ⊔ ℓ)) (b : B) → transport ℓ (const B) p b ≡ b

    -- base case
    d : (x : A) → D x x refl
    d x B b = refl

open import Ch2-2

-- lemma-2-3-8
lemma-2-3-8 : {a ℓ : Level} {A : Set a} {B : Set (a ⊔ ℓ)} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → apd ℓ f p ≡ transportconst ℓ p (f x) ∙ ap f p
lemma-2-3-8 {a} {ℓ} {A} {B} {x} {y} f p = J {a} {ℓ} A D d x y p f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → _
    D x y p = (f : A → B) → apd ℓ f p ≡ transportconst ℓ p (f x) ∙ ap f p

    -- base case
    d : (x : A) → D x x refl
    d x f = refl
