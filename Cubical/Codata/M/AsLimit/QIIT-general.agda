{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.QIIT-general where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.itree

open import Cubical.HITs.SetQuotients

-- Order on container types
container-order : ∀ {ℓ} → (S : Container ℓ) → Type (ℓ-suc ℓ)
container-order {ℓ} S = S .fst → S .fst → Type ℓ

ismon : ∀ {ℓ} → (S : Container ℓ) → (g : ℕ → S .fst) (P : container-order S) → Type ℓ
ismon S g P = (n : ℕ) → P (g n) (g (suc n))

Seq : ∀ {ℓ} → (S : Container ℓ) (P : container-order S) → Type ℓ
Seq S P = (Σ[ g ∈ (ℕ → S .fst)] (ismon S g P))

-- Sequence should be equal to M-type, if some properties of the container order is fulfilled!

correct-order : ∀ {ℓ} → (S : Container ℓ) → container-order S → Set ℓ
correct-order S P =
  (∀ x → P x x) -- order must be reflexive !

M≡Seq : ∀ {ℓ} → (S : Container ℓ) (P : container-order S) → (correct-order S P) → M S ≡ Seq S P
M≡Seq S P C = isoToPath (iso (M→Seq) (Seq→M) M-Seq Seq-M)
  where
    open import Cubical.Foundations.Isomorphism
    -- equal (but just in the limit) !

    postulate
      -- this is hard? follows structure of M S (check s0 ??)
      Seq→M : Seq S P → M S

    M→Seq : M S → Seq S P
    M→Seq = M-coinduction-const (Seq S P) λ x → (λ _ → x .fst) , (λ _ → C (x .fst))

    postulate
      M-Seq : section M→Seq Seq→M
      Seq-M : retract M→Seq Seq→M
-------------------------------
-- EXAMPLES Partiality monad --
-------------------------------

_⊑maybe_ : ∀ {A : Set} → container-order (delay-S A)
x ⊑maybe y = (x ≡ y) ⊎ ((x ≡ inr tt) × (x ≡ inr tt → ⊥))

Seq-part : Set → Set
Seq-part A = Seq (delay-S A) (_⊑maybe_)

-------------------
-- EXAMPLES TREE --
-------------------

-- equivalence of trees removing values, only looking at branching!
mutual
  data _∼tree_ {E} {R} : (_ _ : tree E R) → Type₁ where
    ∼leaf : ∀ x y → tree-ret x ∼tree tree-ret y -- ignore differences in values
    ∼node : ∀ {A} (e : E A) (k₁ k₂ : A → tree E R) → ((a : A) → k₁ a ∞∼tree k₂ a) → tree-vis e k₁ ∼tree tree-vis e k₂

  record _∞∼tree_ {E} {R} (x y : tree E R) : Type₁ where
    coinductive
    field
      force : x ∼tree y

open _∞∼tree_

tree/∼ : ∀ E R → Type₁
tree/∼ E R = tree E R / _∼tree_

_⊑tree-S_ : ∀ {E : Type₀ -> Type₁} {R : Type₀} → (x y : tree-S E R .fst) → Set₁
_⊑tree-S_ {E} {R} x y =
    (x ≡ y) -- reflexivity
  ⊎ (Σ[ r ∈ R ] (Σ[ r' ∈ R ] (x ≡ inl r') → ⊥) × (y ≡ inl r)) -- terminates

tree-Seq : ∀ E R → Set₁
tree-Seq E R = Seq (tree-S E R) _⊑tree-S_

-- data _⊑tree_ {E R} : (_ _ : tree E R) → Set₁ where
--   ⊑-refl : ∀ x → (tree-ret x) ⊑tree (tree-ret x)
--   ⊑-step : ∀ x → (tree-vis x) ⊑tree ?
-- -- x ⊑tree y = {!!}

-- tree→sTree (k1 a) ≡ tree→sTree (k2 a)

-- mutual
--   abstract
--     -- silhouete-tree
--     data sTree (E : Set → Set₁) : Set₁ where
--       leaf : sTree E
--       node : ∀ {A} → E A → (A → ∞sTree E) → sTree E
--       sTree-isSet : isSet (sTree E)
--       α : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y

--     record ∞sTree (E : Set → Set₁) : Set₁ where
--       coinductive
--       field
--         force : sTree E

--   abstract
--     -- How "defined" the M-type is.
--     data _⊑_ {E : Set → Set₁} : (_ _ : sTree E) → Set₁ where
--       ⊑-refl            : ∀ x → x ⊑ x
--       ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
--       ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

-- open ∞sTree

-- abstract
--   mutual
--     Ptree→sTree : ∀ {E R} → P₀ (tree-S E R) (tree E R) → sTree E
--     Ptree→sTree (inl _ , _) = leaf
--     Ptree→sTree (inr (A , e) , b) = node e (∞tree→sTree A b)

--     ∞tree→sTree : ∀ {ℓ} (A : Set) {E} {R} → (Lift {ℓ-zero} {ℓ} A → tree E R) → A → ∞sTree E
--     force (∞tree→sTree A b a) = tree→sTree (b (lift a))

--     tree→sTree : ∀ {E R} → tree E R → sTree E
--     tree→sTree {E} = M-coinduction-const (sTree E) Ptree→sTree

--   recc :
--     ∀ {A B : Set {!!}} {R : A → A → Set {!!}} →
--     (f : A → B) →
--     (∀ x y → R x y → f x ≡ f y) →
--     isSet B →
--     A / R → B
--   recc {A} {B} {R} f feq B-set ar =
--     Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

--   tree→sTree-mono : ∀ {E R} (x y : tree E R) → x ⊑tree y → tree→sTree x ⊑ tree→sTree y
--   tree→sTree-mono = {!!}

--   tree→sTree-≈→≡ : ∀ {E R} (x y : tree E R) → x ∼tree y → tree→sTree x ≡ tree→sTree y
--   tree→sTree-≈→≡ x y (∼leaf _ _) = refl
--   tree→sTree-≈→≡ x y (∼node {A} e k1 k2 p) =
--     let temp : (a : A) → tree→sTree (k1 a) ≡ tree→sTree (k2 a)
--         temp a = tree→sTree-≈→≡ (k1 a) (k2 a) (force (p a)) in
--     tree→sTree (tree-vis e k1)
--       ≡⟨ α {!!} {!!} ⟩
--     tree→sTree (tree-vis e k2) ∎
--   -- α (tree→sTree-mono x y {!!}) {!!}

--   -- tree→sTree (tree-vis e k1) ≡ tree→sTree (tree-vis e k2)

--   tree/∼→sTree : ∀ {E R} → tree/∼ E R → sTree E
--   tree/∼→sTree = recc (tree→sTree) tree→sTree-≈→≡ sTree-isSet
