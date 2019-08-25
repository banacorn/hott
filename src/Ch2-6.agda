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

-- pair≡ :  ∀ {a b} {A : Set a} {B : Set b} {x y : A × B}
--   → proj₁ x ≡ proj₁ y × proj₂ x ≡ proj₂ y → x ≡ y
-- pair≡ p = Definition-2-6-3 p

-- Definition 2.6.4
_X_ : {a b : Level} {Z : Set a}
  → (A B : Z → Set b)
  → Z → Set _
_X_ {a} {b} {Z} A B z = A z × B z


-- Theorem 2.6.4
Theorem-2-6-4 : {a b : Level} {Z : Set a}
  → (A B : Z → Set b)
  → {z w : Z} (p : z ≡ w)
  → (x : (A X B) z)
  → transport (A X B) p x ≡ ((transport A p (proj₁ x)) , transport B p (proj₂ x))
Theorem-2-6-4 {_} {_} {Z} A B {z} {w} p x = J _ D d z w p x
  where
    D : (z w : Z) (p : z ≡ w) → Set _
    D z w p = (x : (A X B) z)
      → transport (A X B) p x ≡
        (transport A p (proj₁ x) , transport B p (proj₂ x))

    d : (z : Z) → D z z refl
    d z x = refl

-- Definition 2.6.5
Definition-2-6-5 : {a a' b b' : Level}
  → {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'}
  → (g : A → A') (h : B → B')
  → A × B
  → A' × B'
Definition-2-6-5 g h x = g (proj₁ x) , h (proj₂ x)


-- Theorem 2.6.5
Theorem-2-6-5 : {a a' b b' : Level}
  → {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'}
  → (g : A → A') (h : B → B')
  → {x y : A × B}
  → (p : proj₁ x ≡ proj₁ y)
  → (q : proj₂ x ≡ proj₂ y)
  → ap (Definition-2-6-5 g h) (Definition-2-6-3 (p , q)) ≡ Definition-2-6-3 (ap g p , ap h q)
Theorem-2-6-5 {A = A} {A'} {B} {B'} g h {x} {y} p q = J _ D d (proj₁ x) (proj₁ y) p g h (proj₂ x) (proj₂ y) q
  where
    D : (x₁ y₁ : A) (p : x₁ ≡ y₁) → Set _
    D x₁ y₁ p = (g : A → A') (h : B → B') (x₂ y₂ : B) (q : x₂ ≡ y₂)
      → ap (Definition-2-6-5 g h) (Definition-2-6-3 (p , q)) ≡
        Definition-2-6-3 (ap g p , ap h q)


    d : (x : A) → D x x refl
    d x g h x₂ y₂ q = J _ E e x₂ y₂ q g h

      where
        E : (x₂ y₂ : B) (q : x₂ ≡ y₂) → Set _
        E x₂ y₂ q = (g : A → A') (h : B → B')
          → ap (Definition-2-6-5 g h) (Definition-2-6-3 (refl , q)) ≡
            Definition-2-6-3 (ap g refl , ap h q)

        e : (y : B) → E y y refl
        e y g h = refl
