{-# OPTIONS --without-K #-}

module Ch2-4 where

open import Level hiding (lift)

open import Ch2-1
open import Ch2-2
open import Ch2-3

-- Definition 2.4.1 (homotopy)
infixl 8 _~_
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

~-setoid : ∀ {a b} → (A : Set a) → (P : A → Set b) → Setoid _ _
~-setoid {a} {b} A P = record
  { Carrier       = _
  ; _≈_           = _~_ {a} {b} {A} {P}
  ; isEquivalence = ~-isEquivalence {a} {b} {A} {P}
  }

open import Function using (id; _∘_)

∘-cong-right : ∀ {a} {b} {c} {A : Set a} {B : Set b} {C : Set c} {g h : A → B}
  → (f : B → C)
  → g ~ h
  → f ∘ g ~ f ∘ h
∘-cong-right f g~h x = ap f (g~h x)

∘-cong-left : ∀ {a} {b} {c} {A : Set a} {B : Set b} {C : Set c} {g h : B → C}
  → (f : A → B)
  → g ~ h
  → g ∘ f ~ h ∘ f
∘-cong-left f g~h x = g~h (f x)

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

open import Data.Product

-- Definition 2.4.6
qinv : ∀ {a b} {A : Set a} {B : Set b}
  → (f : A → B)
  → Set (a ⊔ b)
qinv {a} {b} {A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ~ id × g ∘ f ~ id)

-- Example 2.4.7
example-2-4-7 : ∀ {a} {A : Set a} → qinv (id {a} {A})
example-2-4-7 = id , ((λ x → refl) , λ x → refl)

-- Example 2.4.8
example-2-4-8-i : ∀ {a} {A : Set a} {x y z : A}
  → (p : x ≡ y)
  → qinv (λ (q : y ≡ z) → p ∙ q)
example-2-4-8-i {a} {A} {x} {y} {z} p = (λ q → ¬ p ∙ q) , (α , β)
  where
    α : (q : x ≡ z) → p ∙ (¬ p ∙ q) ≡ q
    α q =
      begin
        p ∙ (¬ p ∙ q)
      ≈⟨ ∙-assoc p (¬ p) q ⟩
        p ∙ ¬ p ∙ q
      ≈⟨ ap (λ w → w ∙ q) (¬-identityˡ p) ⟩
        refl ∙ q
      ≈⟨ ¬ ∙-identityˡ q ⟩
        q
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid _)
    β : (q : y ≡ z) → ¬ p ∙ (p ∙ q) ≡ q
    β q =
      begin
        ¬ p ∙ (p ∙ q)
      ≈⟨ ∙-assoc (¬ p) p q ⟩
        ¬ p ∙ p ∙ q
      ≈⟨ ap (λ w → w ∙ q) (¬-identityʳ p) ⟩
        refl ∙ q
      ≈⟨ ¬ ∙-identityˡ q ⟩
        q
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid _)

example-2-4-8-ii : ∀ {a} {A : Set a} {x y z : A}
  → (p : x ≡ y)
  → qinv (λ (q : z ≡ x) → q ∙ p)
example-2-4-8-ii {a} {A} {x} {y} {z} p = (λ q → q ∙ ¬ p) , α , β
  where
    α : (q : z ≡ y) → q ∙ ¬ p ∙ p ≡ q
    α q =
      begin
        q ∙ ¬ p ∙ p
      ≈⟨ ¬ ∙-assoc q (¬ p) p ⟩
        q ∙ (¬ p ∙ p)
      ≈⟨ ap (λ w → q ∙ w) (¬-identityʳ p) ⟩
        q ∙ refl
      ≈⟨ ¬ (∙-identityʳ q) ⟩
        q
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid _)
    β : (q : z ≡ x) → q ∙ p ∙ ¬ p ≡ q
    β q =
      begin
        q ∙ p ∙ ¬ p
      ≈⟨ ¬ ∙-assoc q p (¬ p) ⟩
        q ∙ (p ∙ ¬ p)
      ≈⟨ ap (λ w → q ∙ w) (¬-identityˡ p) ⟩
        q ∙ refl
      ≈⟨ ¬ (∙-identityʳ q) ⟩
        q
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid _)

example-2-4-9 : ∀ {a b} {A : Set a} {x y : A}
  → (P : A → Set b)
  → (p : x ≡ y)
  → qinv (transport P p)
example-2-4-9 {a} {b} {A} {x} {y} P p = (transport P (¬ p)) , α , β
  where
    α : (w : P y) → transport P p (transport P (¬ p) w) ≡ w
    α w =
      begin
        transport P p (transport P (¬ p) w)
      ≈⟨ lemma-2-3-9 P (¬ p) p w ⟩
        transport P (¬ p ∙ p) w
      ≈⟨ ap (λ q → transport P q w) (¬-identityʳ p) ⟩
        transport P refl w
      ≈⟨ refl ⟩
        w
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid _)

    β : (w : P x) → transport P (¬ p) (transport P p w) ≡ w
    β w =
      begin
        transport P (¬ p) (transport P p w)
      ≈⟨ lemma-2-3-9 P p (¬ p) w ⟩
        transport P (p ∙ ¬ p) w
      ≈⟨ ap (λ q → transport P q w) (¬-identityˡ p) ⟩
        transport P refl w
      ≈⟨ refl ⟩
        w
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid _)

-- Definition 2.4.10
isequiv : ∀ {a b} {A : Set a} {B : Set b}
  → (f : A → B)
  → Set (a ⊔ b)
isequiv {a} {b} {A} {B} f =
  (Σ[ g ∈ (B → A) ] f ∘ g ~ id) × (Σ[ h ∈ (B → A) ] h ∘ f ~ id)

-- Property 2.4.10-i
Property-2-4-10-i : ∀ {a b} {A : Set a} {B : Set b}
  → (f : A → B)
  → qinv f
  → isequiv f
Property-2-4-10-i f (g , α , β) = (g , α) , (g , β)

-- Property 2.4.10-ii
Property-2-4-10-ii : ∀ {a b} {A : Set a} {B : Set b}
  → (f : A → B)
  → isequiv f
  → qinv f
Property-2-4-10-ii {a} {b} {A} {B} f ((g , α) , (h , β)) = g , (α , β')
  where
    --
    --      β           α
    --    g ~ h ∘ f ∘ g ~ h
    --
    γ : g ~ h
    γ x = ¬ (β (g x)) ∙ ap h (α x)

    β' : g ∘ f ~ id
    β' x = γ (f x) ∙ β x

-- Property 2.4.10-iii
-- Property-2-4-10-iii : ∀ {a b} {A : Set a} {B : Set b}
--   → (f : A → B)
--   → (e₁ e₂ : isequiv f)
--   → e₁ ≡ e₂
-- Property-2-4-10-iii {a} {b} {A} {B} f e₁ e₂ = {!   !}

-- Definition 2.4.11
_≅_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A ≅ B = Σ[ f ∈ (A → B) ] isequiv f

-- Lemma 2.4.12-i
Lemma-2-4-12-i : ∀ {a} (A : Set a) → A ≅ A
Lemma-2-4-12-i A = id , Property-2-4-10-i id example-2-4-7

-- Lemma 2.4.12-ii
Lemma-2-4-12-ii : ∀ {a} {b} {A : Set a} {B : Set b}
  → A ≅ B
  → B ≅ A
Lemma-2-4-12-ii {a} {b} {A} {B} (f , f-isequiv) = f⁻¹ , f⁻¹-isequiv
  where
    f-qinv : qinv f
    f-qinv = Property-2-4-10-ii f f-isequiv

    f⁻¹ : B → A
    f⁻¹ = proj₁ f-qinv

    f⁻¹-qinv : qinv f⁻¹
    f⁻¹-qinv = f , (swap (proj₂ f-qinv))

    f⁻¹-isequiv : isequiv f⁻¹
    f⁻¹-isequiv = Property-2-4-10-i f⁻¹ f⁻¹-qinv

-- Lemma 2.4.12-iii
Lemma-2-4-12-iii : ∀ {a} {b} {c} {A : Set a} {B : Set b} {C : Set c}
  → A ≅ B → B ≅ C → A ≅ C
Lemma-2-4-12-iii {a} {b} {c} {A} {B} {C} (g , g-isequiv) (f , f-isequiv)
  = (f ∘ g) , f∘g-isequiv
  where
    f-qinv : qinv f
    f-qinv = Property-2-4-10-ii f f-isequiv

    g-qinv : qinv g
    g-qinv = Property-2-4-10-ii g g-isequiv

    f⁻¹ : C → B
    f⁻¹ = proj₁ f-qinv

    f∘f⁻¹~id : f ∘ f⁻¹ ~ id
    f∘f⁻¹~id = proj₁ (proj₂ f-qinv)

    f⁻¹∘f~id : f⁻¹ ∘ f ~ id
    f⁻¹∘f~id = proj₂ (proj₂ f-qinv)

    g⁻¹ : B → A
    g⁻¹ = proj₁ g-qinv

    g∘g⁻¹~id : g ∘ g⁻¹ ~ id
    g∘g⁻¹~id = proj₁ (proj₂ g-qinv)

    g⁻¹∘g~id : g⁻¹ ∘ g ~ id
    g⁻¹∘g~id = proj₂ (proj₂ g-qinv)

    α : (f ∘ g) ∘ (g⁻¹ ∘ f⁻¹) ~ id
    α = begin
        (f ∘ g) ∘ (g⁻¹ ∘ f⁻¹)
      ≈⟨ (λ x → refl) ⟩
        f ∘ (g ∘ g⁻¹) ∘ f⁻¹
      ≈⟨ ∘-cong-right f (∘-cong-left f⁻¹ g∘g⁻¹~id) ⟩
        f ∘ id ∘ f⁻¹
      ≈⟨ (λ x → refl) ⟩
        f ∘ f⁻¹
      ≈⟨ f∘f⁻¹~id ⟩
        id
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (~-setoid _ _)

    β : (g⁻¹ ∘ f⁻¹) ∘ (f ∘ g) ~ id
    β = begin
        (g⁻¹ ∘ f⁻¹) ∘ (f ∘ g)
      ≈⟨ (λ x → refl) ⟩
        g⁻¹ ∘ (f⁻¹ ∘ f) ∘ g
      ≈⟨ ∘-cong-right g⁻¹ (∘-cong-left g f⁻¹∘f~id) ⟩
        g⁻¹ ∘ id ∘ g
      ≈⟨ (λ x → refl) ⟩
        g⁻¹ ∘ g
      ≈⟨ g⁻¹∘g~id ⟩
        id
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (~-setoid _ _)

    f∘g-qinv : qinv (f ∘ g)
    f∘g-qinv = (g⁻¹ ∘ f⁻¹) , α , β

    f∘g-isequiv : isequiv (f ∘ g)
    f∘g-isequiv = Property-2-4-10-i (f ∘ g) f∘g-qinv
