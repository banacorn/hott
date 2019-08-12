{-# OPTIONS --without-K #-}

module Ch2-4 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2

-- Definition 2.4.1 (homotopy)
_~_ : ∀ {a b} {A : Set a} {P : A → Set b}
  → (f g : (z : A) → P z)
  → Set (a ⊔ b)
_~_ {a} {b} {A} {P} f g = ∀ (x : A) → f x ≡ g x


-- Lemma 2.4.2

open import Relation.Binary

~-isEquivalence : ∀ {a b} {A : Set a} {P : A → Set b} → IsEquivalence (_~_ {A = A} {P})
~-isEquivalence = record
  { refl = ~-refl
  ; sym = ~-sym
  ; trans = ~-trans
  }
  where
    ~-refl : Reflexive _~_
    ~-refl f = refl
    ~-sym : Symmetric _~_
    ~-sym i~j x = ¬ (i~j x)
    ~-trans : Transitive _~_
    ~-trans i~j j~k x = i~j x ∙ j~k x

-- Lemma 2.4.3
Lemma-2-4-3 : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
  → (f g : A → B)
  → (H : f ~ g)
  → (p : x ≡ y)
  → H x ∙ ap g p ≡ ap f p ∙ H y
Lemma-2-4-3 {a} {b} {A} {B} {x} {y} f g H p = J A D d x y p f g H
  where
    D : (x y : A) (p : x ≡ y) → Set _
    D x y p = (f g : A → B) (H : f ~ g) → H x ∙ ap g p ≡ ap f p ∙ H y

    --              f(p)
    --      f(x) ========== f(y)
    --       ||              ||
    --  H(x) ||              ||  H(y)
    --       ||              ||
    --      g(x) ========== g(y)
    --              g(p)
    --
    d : (x : A) → D x x refl
    d x f g H =
      begin
        H x ∙ ap g refl
      ≈⟨ ap (λ w → H x ∙ w) (ap-refl g) ⟩
        H x ∙ refl
      ≈⟨ ¬ ∙-identityʳ (H x) ⟩
        H x
      ≈⟨ refl ⟩
        H x
      ≈⟨ ∙-identityˡ (H x) ⟩
        refl ∙ H x
      ≈⟨ ap (λ w → w ∙ H x) (¬ ap-refl f) ⟩
        ap f refl ∙ H x
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid (f x ≡ g x))


open import Function using (id)

-- Corollary 2.4.4
Corollary-2-4-4 : ∀ {a} {A : Set a}
  → (f : A → A)
  → (H : f ~ id)
  → (x : A)
  → H (f x) ≡ ap f (H x)
Corollary-2-4-4 {a} {A} f H x =
  begin
    H (f x)
  ≈⟨ ∙-identityʳ (H (f x)) ⟩
    H (f x) ∙ refl
  ≈⟨ ap [ H (f x) ]∙ (¬ ¬-identityˡ (H x)) ⟩
    H (f x) ∙ (H x ∙ ¬ H x)
  ≈⟨ ∙-assoc (H (f x)) (H x) (¬ H x) ⟩
    (H (f x) ∙ H x) ∙ ¬ H x
  ≈⟨ ap (λ w → (H (f x) ∙ w) ∙ ¬ H x) (¬ ap-id (H x)) ⟩
    (H (f x) ∙ ap id (H x)) ∙ ¬ H x
  ≈⟨ ap ∙[ ¬ H x ] (Lemma-2-4-3 f id H (H x)) ⟩
    (ap f (H x) ∙ H x) ∙ ¬ H x
  ≈⟨ ¬ ∙-assoc (ap f (H x)) (H x) (¬ H x) ⟩
    ap f (H x) ∙ (H x ∙ ¬ H x)
  ≈⟨ ap [ ap f (H x) ]∙ (¬-identityˡ (H x)) ⟩
    ap f (H x) ∙ refl
  ≈⟨ ¬ ∙-identityʳ (ap f (H x)) ⟩
    ap f (H x)
  ∎
  where
    open import Relation.Binary.Reasoning.Setoid (setoid _)
