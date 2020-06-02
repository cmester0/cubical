{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.partiality-monad-new where

{-
  Inspired by  Code related to the paper 
  "Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type" (https://arxiv.org/pdf/1610.09254.pdf)
  Thorsten Altenkirch, Nils Anders Danielsson and Nicolai Kraus
  Located at: http://www.cse.chalmers.se/~nad/publications/altenkirch-danielsson-kraus-partiality/README.html
-}

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming (elim to elim/)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.HLevels

mutual
  data Delay (R : Set) : Set where
    now : R → Delay R
    later : Delay R → Delay R

-- Weak bisimularity for delay monad
mutual
  data _∼delay_ {R} : (_ _ : Delay R) → Set where
    ∼now : ∀ (r : R) → now r ∼delay now r
    ∼later-l : ∀ t u → t ∼delay u → later t ∼delay u
    ∼later-r : ∀ t u → t ∼delay u → t ∼delay later u
    ∼later : ∀ t u → t ∼delay u → later t ∼delay later u

----------------------
-- Partiality monad --
----------------------

-- Partiality monad (QIIT)
mutual
  data <_>⊥ {ℓ} (A : Type ℓ) : Type ℓ where
    now : < A >⊥
    later : A → < A >⊥
    ⊔      : Increasing-sequence A → < A >⊥
    α      : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
    ⊥-isSet : isSet (< A >⊥)

  -- Increasing sequences.

  Increasing-sequence : ∀ {ℓ} → Type ℓ → Type ℓ
  Increasing-sequence A = Σ[ f ∈ (ℕ → < A >⊥) ] ((n : ℕ) → f n ⊑ f (suc n))

  -- Upper bounds.

  Is-upper-bound : ∀ {ℓ} → {A : Type ℓ} → Increasing-sequence A → < A >⊥ → Set ℓ
  Is-upper-bound s x = ∀ n → (fst s n) ⊑ x

  -- A projection function for Increasing-sequence.

  -- An ordering relation.

  data _⊑_ {ℓ} {A : Set ℓ} : < A >⊥ → < A >⊥ → Set ℓ where
    ⊑-refl            : ∀ x → x ⊑ x
    ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    never⊑            : ∀ x → never ⊑ x
    upper-bound       : ∀ s → Is-upper-bound s (⊔ s)
    least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⊔ s ⊑ ub
    ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

-------------------------------------------------------------
-- Equivalence to Sequence quotiented by weak bisimularity --
-------------------------------------------------------------
