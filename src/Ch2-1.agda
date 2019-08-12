{-# OPTIONS --without-K #-}

module Ch2-1 where

open import Level

infixl 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x


J : {a b : Level} (A : Set a) (C : (x y : A) → x ≡ y → Set b)
    → ((x : A) → C x x refl)
    → (x y : A) (P : x ≡ y)
    → C x y P
J A C b x .x refl = b x

-- K : (A : Set) (x : A) (C : x ≡ x → Set)
--   → C refl
--   → (loop : x ≡ x)
--   → C loop
-- K A x C b p = {! p  !}

-- Lemma 2.1.1 (inversion of paths)
infix 6 ¬_
¬_ : {a : Level} {A : Set a} {x y : A} → x ≡ y → y ≡ x
¬_ {a} {A} {x} {y} p = J A D d x y p

  where
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = y ≡ x

    d : (x : A) → D x x refl
    d x = refl


-- Lemma 2.1.2 (concatenation of paths)
infixl 5 _∙_
_∙_ : {a : Level} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {a} {A} {x} {y} {z} p q = J {a} {a} A D d x y p z q

  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = (z : A) (q : y ≡ z) → x ≡ z

    -- base case
    d : (x z : A) (q : x ≡ z) → x ≡ z
    d x z q = q


-- Lemma 2.1.4.i (identity of path concatenation)
∙-identityʳ : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
∙-identityʳ {a} {A} {x} {y} p = J A D d x y p

  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = p ≡ p ∙ refl

    -- base case
    d : (x : A) → D x x refl
    d x = refl

∙-identityˡ : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
∙-identityˡ {a} {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = p ≡ refl ∙ p

    -- base case
    d : (x : A) → D x x refl
    d x = refl

-- Lemma 2.1.4.ii (identity of path inversion)
¬-identityʳ : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → ¬ p ∙ p ≡ refl
¬-identityʳ {a} {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = ¬ p ∙ p ≡ refl

    -- base case
    d : (x : A) → D x x refl
    d x = refl

¬-identityˡ : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → p ∙ ¬ p ≡ refl
¬-identityˡ {a} {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set a
    D x y p = p ∙ ¬ p ≡ refl

    -- base case
    d : (x : A) → D x x refl
    d x = refl

-- Lemma 2.1.4.iii (involution of path inversion)
involution : {A : Set} {x y : A} (p : x ≡ y) → ¬ ¬ p ≡ p
involution {A} {x} {y} p = J A D d x y p
  where
    -- the predicate
    D : (x y : A) (p : x ≡ y) → Set
    D x y p = ¬ ¬ p ≡ p

    -- base case
    d : (x : A) → D x x refl
    d x = refl

-- Lemma 2.1.4.iv (associativity of path concatenation)
∙-assoc : {a : Level} {A : Set a} {w x y z : A}
  → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
∙-assoc {a} {A} {w} {x} {y} {z} p q r = J A D d w x p y q z r
  where
    -- the predicate
    D : (w x : A) (p : w ≡ x) → Set a
    D w x p = (y : A) (q : x ≡ y)
            → (z : A) (r : y ≡ z)
            → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r

    -- base case
    d : (x : A) → D x x refl
    d x y q z r = refl

-- module EckmannHilton where
--
--   open import Relation.Binary
--
--   isEquivalence : ∀ {A} → IsEquivalence (_≡_ {A})
--   isEquivalence = record
--     { refl = refl
--     ; sym = ¬_
--     ; trans = _∙_
--     }
--
--   setoid : Set → Setoid _ _
--   setoid A = record
--     { Carrier       = A
--     ; _≈_           = _≡_
--     ; isEquivalence = isEquivalence {A}
--     }
--     -- begin
--     --   p ∙ refl
--     -- ≈⟨ ¬ ∙-identityʳ p ⟩
--     --   p
--     -- ≈⟨ α ⟩
--     --   q
--     -- ≈⟨ ∙-identityʳ q ⟩
--     --   q ∙ refl
--     -- ∎
--     -- where
--     --   open import Relation.Binary.Reasoning.Setoid (setoid (a ≡ x))
--
--   -- whisker right
--   infixl 6 _∙r_
--   _∙r_ : {A : Set} {a b c : A} {p q : a ≡ b}
--     → (α : p ≡ q) (r : b ≡ c)
--     → p ∙ r ≡ q ∙ r
--   _∙r_ {A} {a} {b} {c} {p} {q} α r = J A D d b c r a p q α
--     where
--       -- the predicate
--       D : (b c : A) (r : b ≡ c) → Set
--       D b c r = (a : A) (p q : a ≡ b) (α : p ≡ q)
--         → p ∙ r ≡ q ∙ r
--
--       -- base case
--       d : (x : A) → D x x refl
--       d x a p q α = ¬ ∙-identityʳ p ∙ α ∙ ∙-identityʳ q
--
--
--   -- whisker left
--   infixl 6 _∙l_
--   _∙l_ : {A : Set} {a b c : A} {r s : b ≡ c}
--     → (q : a ≡ b) (β : r ≡ s)
--     → q ∙ r ≡ q ∙ s
--   _∙l_ {A} {a} {b} {c} {r} {s} q β = J A D d a b q c r s β
--     where
--       -- the predicate
--       D : (a b : A) (q : a ≡ b) → Set
--       D a b q = (c : A) (r s : b ≡ c) (β : r ≡ s)
--         → q ∙ r ≡ q ∙ s
--
--       -- base case
--       d : (x : A) → D x x refl
--       d x c r s β = ¬ ∙-identityˡ r ∙ β ∙ ∙-identityˡ s
--
--   -- horizontal composition
--   _⋆_ : {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c}
--     → (α : p ≡ q) (β : r ≡ s)
--     → p ∙ r ≡ q ∙ s
--   _⋆_ {A} {a} {b} {c} {p} {q} {r} {s} α β = (α ∙r r) ∙ (q ∙l β)
--
--     where
--       whisker-right-lemma : ∀ {A : Set} {a b : A}
--         → {p q : a ≡ b} {α : p ≡ q}
--         → α ∙r refl ≡ ¬ ∙-identityʳ p ∙ α ∙ ∙-identityʳ q
--       whisker-right-lemma {A} {a} {b} {p} {q} {α} = refl
--
--       whisker-left-lemma : ∀ {A : Set} {b c : A}
--         → {r s : b ≡ c} {β : r ≡ s}
--         → refl ∙l β ≡ ¬ ∙-identityˡ r ∙ β ∙ ∙-identityˡ s
--       whisker-left-lemma {A} {b} {c} {r} {s} {α} = refl
--
--   cong : {A B : Set} {x y : A}
--     → (f : A → B) (p : x ≡ y)
--     → f x ≡ f y
--   cong {A} {B} {x} {y} f p = J A D d x y p f
--     where
--       -- the predicate
--       D : (x y : A) (p : x ≡ y) → Set
--       D x y p = (f : A → B) → f x ≡ f y
--
--       -- base case
--       d : (x : A) → D x x refl
--       d x f = refl
--
--   cong2 : {A B C : Set} {x y : A} {a b : B}
--     → (f : A → B → C) (p : x ≡ y) (q : a ≡ b)
--     → f x a ≡ f y b
--   cong2 {A} {B} {C} {x} {y} {a} {b} f p q = J A D d x y p a b q f
--     -- J A D d x y p f
--     where
--       -- the predicate
--       D : (x y : A) (p : x ≡ y) → Set
--       D x y p = (a b : B) (q : a ≡ b) (f : A → B → C) → f x a ≡ f y b
--
--       -- base case
--       d : (x : A) → D x x refl
--       d x a b q f = cong (f x) q
--
--
--   -- theorem : {A : Set} {a b c : A}
--   --   → {p q : a ≡ b} {r s : b ≡ c}
--   --   → (α : p ≡ q) (β : r ≡ s)
--   --   → α ⋆ β ≡ cong2 _∙_ α β
--   -- theorem {A} {a} {b} {c} {p} {q} {r} {s} α β = J A D d a b p q c r s α β
--   --
--   --   where
--   --     -- the predicate
--   --     D : (a b : A) (p : a ≡ b) → Set
--   --     D a b p = (q : a ≡ b) (c : A) (r s : b ≡ c) (α : p ≡ q) (β : r ≡ s)
--   --       → α ⋆ β ≡ cong2 _∙_ α β
--   --
--   --     -- base case ʳˡ
--   --     d : (x : A) → D x x refl
--   --     d x q c r s α β = J A E e x c r s q α β
--   --
--   --       where
--   --         -- the predicate
--   --         E : (b c : A) (r : b ≡ c) → Set
--   --         E b c r = (s : b ≡ c) (q : b ≡ b) (α : refl ≡ q) (β : r ≡ s)
--   --           → α ⋆ β ≡ cong2 _∙_ α β
--   --
--   --         -- base case
--   --         e : (x : A) → E x x refl
--   --         e x s q α β = {!   !}
