{-# OPTIONS --without-K #-}

module Hott where

infixl 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

J : (A : Set) (C : (x y : A) → x ≡ y → Set)
    → ((x : A) → C x x refl)
    → (x y : A) (P : x ≡ y)
    → C x y P
J A C b x .x refl = b x


-- K : (A : Set) (x : A) (C : x ≡ x → Set)
--   → C refl
--   → (loop : x ≡ x)
--   → C loop
-- K A x C b p = {! p  !}

-- lemma-2-1-1: inversion of paths
infix 6 ¬_
¬_ : {A : Set} {x y : A} → x ≡ y → y ≡ x
¬_ {A} {x} {y} p = J A D d x y p

  where
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = y ≡ x

    d : (x : A) → D x x refl
    d x = refl


-- lemma-2-1-2: concatenation of paths
infixl 5 _∙_
_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {A} {x} {y} {z} p q = J A D d x y p z q

  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = (z : A) (q : y ≡ z) → x ≡ z

    -- base case
    d : (x z : A) (q : x ≡ z) → x ≡ z
    d x z q = q


-- lemma-2-1-4-i: identity of path concatenation
∙-identityʳ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
∙-identityʳ {A} {x} {y} p = J A D d x y p

  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = p ≡ p ∙ refl

    -- base case
    d : (x : A) → D x x refl
    d x = refl

∙-identityˡ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
∙-identityˡ {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = p ≡ refl ∙ p

    -- base case
    d : (x : A) → D x x refl
    d x = refl

-- lemma-2-1-4-ii: identity of path inversion
¬-identityʳ : {A : Set} {x y : A} (p : x ≡ y) → ¬ p ∙ p ≡ refl
¬-identityʳ {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = ¬ p ∙ p ≡ refl

    -- base case
    d : (x : A) → D x x refl
    d x = refl

¬-identityˡ : {A : Set} {x y : A} (p : x ≡ y) → p ∙ ¬ p ≡ refl
¬-identityˡ {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = p ∙ ¬ p ≡ refl

    -- base case
    d : (x : A) → D x x refl
    d x = refl

-- lemma-2-1-4-iii: involution of path inversion
involution : {A : Set} {x y : A} (p : x ≡ y) → ¬ ¬ p ≡ p
involution {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = ¬ ¬ p ≡ p

    -- base case
    d : (x : A) → D x x refl
    d x = refl

-- lemma-2-1-4-iv: associativity of path concatenation
∙-assoc : {A : Set} {w x y z : A}
  → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
∙-assoc {A} {w} {x} {y} {z} p q r = J A D d w x p y q z r
  where
    -- the predicate
    D : (w x : A) (p : w ≡ x) → Set
    D w x p = (y : A) (q : x ≡ y)
            → (z : A) (r : y ≡ z)
            → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r

    -- base case
    d : (x : A) → D x x refl
    d x y q z r = refl

open import Relation.Binary

-- sym : Symmetric _≡_
-- sym = ?
--
-- trans : Transitive _≡_
-- trans = ?


isEquivalence : ∀ {A} → IsEquivalence (_≡_ {A})
isEquivalence = record
  { refl = refl
  ; sym = ¬_
  ; trans = _∙_
  }

setoid : Set → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence {A}
  }

-- horizontal composition
_⋆_ : {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c}
  → (α : p ≡ q) (β : r ≡ s)
  → p ∙ r ≡ q ∙ s
_⋆_ {A} {a} {b} {c} {p} {q} {r} {s} α β =  {!   !}
  -- (α ∙r r) ∙ (q ∙l β)

  where
    ru : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
    ru {A} {x} {y} p =
      begin
        p
      ≈⟨ ∙-identityʳ p ⟩
        p ∙ refl
      ∎
      where
        open import Relation.Binary.Reasoning.Setoid (setoid (x ≡ y))

    -- whisker right
    infixl 6 _∙r_
    _∙r_ : {A : Set} {a b c : A} {p q : a ≡ b}
      → (α : p ≡ q) (r : b ≡ c)
      → p ∙ r ≡ q ∙ r
    _∙r_ {A} {a} {b} {c} {p} {q} α r = J A D d b c r a p q α
      where
        -- the predicate
        D : (b c : A) (r : b ≡ c) → Set
        D b c r = (a : A) (p q : a ≡ b) (α : p ≡ q)
          → p ∙ r ≡ q ∙ r

        -- base case
        d : (x : A) → D x x refl
        d x a p q α =
          begin
            p ∙ refl
          ≈⟨ ¬ ∙-identityʳ p ⟩
            p
          ≈⟨ α ⟩
            q
          ≈⟨ ∙-identityʳ q ⟩
            q ∙ refl
          ∎
          where
            open import Relation.Binary.Reasoning.Setoid (setoid (a ≡ x))

    -- whisker-right-lemma : ∀ {A : Set} {a b c : A}
    --   → {p q : a ≡ b} {r : b ≡ c}
    --   → {α : p ≡ q}
    --   → α ∙r refl ≡ {!   !}
    --   -- → α ∙r refl ≡ ¬ ru p ∙ α ∙ ru q
    -- whisker-right-lemma {A} {a} {b} {c} {p} {q} {r} {α} = refl
      -- begin
      --   α ∙r refl
      -- ≈⟨ refl ⟩
      --   {! ¬ ru p ∙ (α ∙ ru q)  !}
      -- ≈⟨ {!   !} ⟩
      --   {!   !}
      -- ≈⟨ {!   !} ⟩
      --   {!   !}
      -- ≈⟨ {!   !} ⟩
      --   ¬ ru p ∙ α ∙ ru q
      -- ∎
      -- where
      --   open import Relation.Binary.Reasoning.Setoid (setoid (p ∙ refl ≡ q ∙ refl))

    -- whisker left
    infixl 6 _∙l_
    _∙l_ : {A : Set} {a b c : A} {r s : b ≡ c}
      → (q : a ≡ b) (β : r ≡ s)
      → q ∙ r ≡ q ∙ s
    _∙l_ {A} {a} {b} {c} {r} {s} q β = J A D d a b q c r s β
      where
        -- the predicate
        D : (a b : A) (q : a ≡ b) → Set
        D a b q = (c : A) (r s : b ≡ c) (β : r ≡ s)
          → q ∙ r ≡ q ∙ s

        -- base case
        d : (x : A) → D x x refl
        d x c r s β = ¬ ∙-identityˡ r ∙ β ∙ ∙-identityˡ s

    -- whisker-left-lemma : ∀ {A : Set} {a b c : A}
    --   → {p q : a ≡ b} {r : b ≡ c}
    --   → {α : p ≡ q}
    --   → α ∙r refl ≡ ¬ ru p ∙ α ∙ ru q
    -- whisker-left-lemma {A} {a} {b} {c} {p} {q} {r} {α} = refl

subst : {A B : Set} {x y : A}
  → (p : x ≡ y) (f : A → B)
  → f x ≡ f y
subst {A} {B} {x} {y} p f = J A D d x y p f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = (f : A → B) → f x ≡ f y

    -- base case
    d : (x : A) → D x x refl
    d x f = refl

subst2 : {A B C : Set} {x y : A} {a b : B}
  → (f : A → B → C) (p : x ≡ y) (q : a ≡ b)
  → f x a ≡ f y b
subst2 {A} {B} {C} {x} {y} {a} {b} f p q = J A D d x y p a b q f
  -- J A D d x y p f
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = (a b : B) (q : a ≡ b) (f : A → B → C) → f x a ≡ f y b

    -- base case
    d : (x : A) → D x x refl
    d x a b q f = subst q (f x)


theorem : {A : Set} {a b c : A}
  → {p q : a ≡ b} {r s : b ≡ c}
  → (α : p ≡ q) (β : r ≡ s)
  → α ⋆ β ≡ subst2 _∙_ α β
theorem α β = {!   !}
