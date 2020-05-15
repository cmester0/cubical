{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.QIIT-examples where

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

-- -- TREES
-- tree-S : (E : Type₀ -> Type₁) (R : Type₀) -> Container (ℓ-suc ℓ-zero)
-- tree-S E R = (R ⊎ (Σ[ A ∈ Type₀ ] (E A))) , (λ { (inl _) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

-- tree : (E : Type₀ -> Type₁) (R : Type₀) -> Type₁
-- tree E R = M (tree-S E R)

-- tree-ret : ∀ {E} {R}  -> R -> tree E R
-- tree-ret {E} {R} r = in-fun (inl r , λ ())

-- tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
-- tree-vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x } )

-- equivalence of trees removing values, only looking at branching!
mutual
  data _∼tree_ {E} {R} : (_ _ : tree E R) → Type₁ where
    ∼leaf : ∀ x y → tree-ret x ∼tree tree-ret y -- ignore differences in values
    ∼node : ∀ {A} (e : E A) (k₁ k₂ : A → tree E R) → ((a : A) → k₁ a ∞∼tree k₂ a) → tree-vis e k₁ ∼tree tree-vis e k₂

  record _∞∼tree_ {E} {R} (x y : tree E R) : Type₁ where
    coinductive
    field
      force : x ∼tree y

tree/∼ : ∀ E R → Type₁
tree/∼ E R = tree E R / _∼tree_

abstract
  data silhouete-tree : Set₁ where


  data silhouete-relation : Set₁ where
