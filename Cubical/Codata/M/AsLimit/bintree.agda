{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.bintree where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Codata.M.AsLimit.Container
-- open import Cubical.Codata.M.AsLimit.itree
open import Cubical.Codata.M.AsLimit.M

-- TREES
tree-S : Container (ℓ-zero)
tree-S = (Unit ⊎ Unit) , (λ { (inl _) -> ⊥ ; (inr _) -> (Unit ⊎ Unit)} )

tree : Type₀
tree = M (tree-S)

tree-leaf : tree
tree-leaf = in-fun (inl tt , λ ())

tree-node : ((Unit ⊎ Unit) -> tree) -> tree
tree-node k = in-fun (inr tt , k)

asdf : ∀ (b : ⊥ → tree) (k : Unit ⊎ Unit → tree) → in-fun (inl tt , b) ≡ in-fun (inr tt , k) → ⊥
asdf = {!!}

mutual
  data T : Set₁ where
    leaf : T
    node : ((Unit ⊎ Unit) → ∞T) → T
    perm : (f : Unit ⊎ Unit → ∞T) → (g : Unit ⊎ Unit → Unit ⊎ Unit) → isEquiv g → node f ≡ node (f ∘ g)

  record ∞T : Set₁ where
    coinductive
    field
      force : T

open ∞T

data _∼_ : (_ _ : tree) → Set where
  ∼leaf : tree-leaf ∼ tree-leaf
  ∼node : ∀ {f g} → ((x : Unit ⊎ Unit) → f x ∼ g x) → tree-node f ∼ tree-node g
  ∼perm : (f : Unit ⊎ Unit → tree) → (g : Unit ⊎ Unit → Unit ⊎ Unit) → isEquiv g → tree-node f ∼ tree-node (f ∘ g)

mutual
  tree→T : tree → T
  tree→T = M-coinduction-const T λ {(inl tt , _) → leaf ; (inr tt , k) → node (tree→∞T ∘ k)}

  tree→∞T : tree → ∞T
  force (tree→∞T x) = tree→T x

-- case_return_of_f : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') → (∀ y → x ≡ y → B y) → B x
-- case x return _ of f f = f x refl

M-coinduction' :
  ∀ {ℓ ℓ'} {S : Container ℓ}
  → (k : M S → Type ℓ')
  → (x : M S) 
  → ((y : P₀ S (M S)) → (x ≡ in-fun y) → k (in-fun y))
  ---------------
  → (k x)
M-coinduction' k x p =
  subst k (in-inverse-out-x x)
  (case out-fun x return (λ x → k (in-fun x)) of (λ {y v → p y (subst (λ a → a ≡ in-fun y) (in-inverse-out-x x) (cong in-fun v))}) f)

data ⊥₁ : Set₁ where

leaf≢node : ∀ {g} → leaf ≡ node g → ⊥₁
leaf≢node {g} x = subst (λ {leaf → T ; _ → ⊥₁}) x (x i0)

-- tree→T-isInjective : isInjective tree→T
-- tree→T-isInjective {x} {y} p =
--   M-coinduction' (λ x → x ≡ y) x (
--     λ {(inl tt , b) v → M-coinduction' (λ y → in-fun (inl tt , b) ≡ y) y
--                                     (λ {(inl tt , b') _ → cong in-fun (ΣPathP (refl , isContr→isProp isContr⊥→A b b'))
--                                        ;(inr tt , g) v' → rec⊥ (leaf≢node (transport (λ i → tree→T (v i) ≡ tree→T (v' i)) p))}) 
--       ;(inr tt , f) v → M-coinduction (λ y → in-fun (inr tt , f) ≡ y)
--                                     (λ {(inl tt , b') → {!!}
--                                        ;(inr tt , g) → {!!}})
--                                     y})
