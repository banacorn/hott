{-# OPTIONS --without-K --no-pattern-matching #-}

module Ch2-7 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2
open import Ch2-3
open import Ch2-4
open import Ch2-5
open import Ch2-6

open import Data.Product
open import Function using (id; _∘_)


Definition-2-7-2-i : ∀ {a b} {A : Set a} {P : A → Set b}
  → (w w' : Σ[ x ∈ A ] P x)
  → (w ≡ w')
  → (Σ[ p ∈ proj₁ w ≡ proj₁ w' ] transport P p (proj₂ w) ≡ proj₂ w')
Definition-2-7-2-i {_} {_} {A} {P} w w' p = J (Σ-syntax A P) D d w w' p
  where
    D : (w w' : Σ[ x ∈ A ] P x) (p : w ≡ w') → Set _
    D w w' p = Σ[ p ∈ proj₁ w ≡ proj₁ w' ] transport P p (proj₂ w) ≡ proj₂ w'

    d : (x : Σ[ x ∈ A ] P x) → D x x refl
    d x = refl , refl

Definition-2-7-2-ii : ∀ {a b} {A : Set a} {P : A → Set b}
  → (w w' : Σ[ x ∈ A ] P x)
  → (Σ[ p ∈ proj₁ w ≡ proj₁ w' ] transport P p (proj₂ w) ≡ proj₂ w')
  → (w ≡ w')
Definition-2-7-2-ii {_} {_} {A} {P} w w' p = J A D d (proj₁ w) (proj₁ w') (proj₁ p) (proj₂ w) (proj₂ w') (proj₂ p)
  -- J A D d w1 w1' fst w2 w2' snd
  where
    D : (w1 w1' : A) (p : w1 ≡ w1') → Set _
    D w1 w1' p = (w2 : P w1) (w2' : P w1') (q : transport P p w2 ≡ w2') → (w1 , w2) ≡ (w1' , w2')

    d : (x : A) → D x x refl
    d x w2 w2' snd = J (P x) E e w2 w2' snd


      where
        E : (w2 w2' : P x) (q : w2 ≡ w2') → Set _
        E w2 w2' q = (x , w2) ≡ (x , w2')

        e : (y : P x) → E y y refl
        e y = refl


Lemma-2-7-2-iii : ∀ {a b} {A : Set a} {P : A → Set b}
  → (w w' : Σ[ x ∈ A ] P x)
  → isequiv (Definition-2-7-2-i w w')
Lemma-2-7-2-iii {_} {_} {A} {P} w w' = (Definition-2-7-2-ii w w' , α) , (Definition-2-7-2-ii w w' , β)
  where
    α : Definition-2-7-2-i w w' ∘ Definition-2-7-2-ii w w' ~ id
    α p = J A D d (proj₁ w) (proj₁ w') (proj₁ p) (proj₂ w) (proj₂ w') (proj₂ p)
      where
        D : (x y : A) (p : x ≡ y) → Set _
        D x y p = (x' : P x) (y' : P y) (q : transport P p x' ≡ y')
          → (Definition-2-7-2-i (x , x') (y , y')
              ∘ Definition-2-7-2-ii (x , x') (y , y')) (p , q) ≡ id (p , q)

        d : (s : A) → D s s refl
        d s x' y' q = J (P s) E e x' y' q
          where
            E : (x' y' : P s) (q : x' ≡ y') → Set _
            E x' y' q =
              (Definition-2-7-2-i (s , x') (s , y')
                  ∘ Definition-2-7-2-ii (s , x') (s , y')) (refl , q) ≡ id (refl , q)

            e : (t : P s) → E t t refl
            e t = refl

    β : Definition-2-7-2-ii w w' ∘ Definition-2-7-2-i w w' ~ id
    β p = J (Σ[ x ∈ A ] P x) D d w w' p
      where
        D : (w w' : Σ[ x ∈ A ] P x) (p : w ≡ w') → Set _
        D w w' p = (Definition-2-7-2-ii w w' ∘ Definition-2-7-2-i w w') p ≡ id p

        d : (x : Σ[ x ∈ A ] P x) → D x x refl
        d x = refl


-- Theorem 2.7.2
Theorem-2-7-2 : ∀ {a b} {A : Set a} {P : A → Set b}
  → (w w' : Σ[ x ∈ A ] P x)
  → (w ≡ w') ≅ (Σ[ p ∈ proj₁ w ≡ proj₁ w' ] transport P p (proj₂ w) ≡ proj₂ w')
Theorem-2-7-2 {_} {_} {A} {P} w w' = Definition-2-7-2-i w w' , Lemma-2-7-2-iii w w'

-- Corollary 2.7.3
Corollary-2-7-3 : ∀ {a b} {A : Set a} {P : A → Set b}
  → (z : Σ[ x ∈ A ] P x)
  → z ≡ (proj₁ z , proj₂ z)
Corollary-2-7-3 {a} {b} {A} {P} z
  = ←≅ (Theorem-2-7-2 z z) (refl , refl)

-- Theorem 2.7.4
Theorem-2-7-4 : ∀ {a b} {A : Set a}
  → {P : A → Set b}
  → {Q : Σ[ x ∈ A ] P x → Set b}
  → {x y : A}
  → (p : x ≡ y)
  → (f : Σ[ u ∈ P x ] Q (x , u))
  → transport (λ w → Σ[ u ∈ P w ] Q (w , u)) p f
      ≡ (transport P p (proj₁ f) , transport Q
          (←≅ (Theorem-2-7-2 (x , (proj₁ f))
          (y , (transport P p (proj₁ f)))) (p , refl)) (proj₂ f))
Theorem-2-7-4 {a} {b} {A} {P} {Q} {x} {y} p f = J A D d x y p f
  where
    D : (x y : A) (p : x ≡ y) → Set _
    D x y p = (f : Σ[ u ∈ P x ] Q (x , u))
      → transport (λ w → Σ-syntax (P w) (λ u → Q (w , u))) p f ≡
      (transport P p (proj₁ f) ,
       transport Q
       (←≅ (Theorem-2-7-2 (x , proj₁ f) (y , transport P p (proj₁ f)))
        (p , refl))
       (proj₂ f))


    d : (x : A) → D x x refl
    d x f = refl
