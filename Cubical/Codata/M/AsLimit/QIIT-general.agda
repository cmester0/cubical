{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.QIIT-general where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
-- open import Cubical.Codata.M.AsLimit.itree

open import Cubical.HITs.SetQuotients

-- Order on container types
container-order : ∀ {ℓ} → (S : Container ℓ) → Type (ℓ-suc ℓ)
container-order {ℓ} S = S .fst → S .fst → Type ℓ

isMon : ∀ {ℓ} (S : Container ℓ) → (container-order S) → (ℕ → S .fst) → Type ℓ
isMon S P g = (n : ℕ) → P (g n) (g (suc n))

isMon' : ∀ {ℓ} → (S : Container ℓ) → (container-order S) → (ℕ → S .fst) → ℕ → Type ℓ
isMon' S P g n = P (g n) (g (suc n))

Seq : ∀ {ℓ} → (S : Container ℓ) (P : container-order S) → Type ℓ
Seq S P = (Σ[ g ∈ (ℕ → S .fst)] (isMon S P g))

record ∞Seq {ℓ} (S : Container ℓ) (P : container-order S) : Type ℓ where
  field
    force : Seq S P

open ∞Seq

shift-Seq :
  ∀ {ℓ} (S : Container ℓ) (P : container-order S)
  → (t : Seq S P)
  → Σ[ va ∈ (S .fst) ] (isMon' S P (λ {0 → va ; (suc n) → fst t n}) 0)
  --------------
  → Seq S P
shift-Seq _ _ (g , a) (va , mon) =
  (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})

unshift-Seq :
  ∀ {ℓ} (S : Container ℓ) (P : container-order S)
  → (Seq S P)
  → (Seq S P)
unshift-Seq _ _ (g , a) = g ∘ suc , a ∘ suc

unshift-shift :
  ∀ {ℓ} {S : Container ℓ} {P : container-order S}
  → (t : Seq S P) →
  ∀ {va-mon} → unshift-Seq S P (shift-Seq S P t va-mon) ≡ t
unshift-shift (g , a) = refl

shift-unshift :
  ∀ {ℓ} {S : Container ℓ} {P : container-order S}
  → (t : Seq S P)
  → shift-Seq S P (unshift-Seq S P t) (fst t 0 , snd t 0) ≡ t
shift-unshift (g , a) =
  ΣPathP
    ( (funExt λ {0 → refl ; (suc n) → refl })
    , (λ {i 0 → a 0 ; i (suc n) → a (suc n)}) )

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
      -- this is hard? follows structure of M S (check s0 , and do it inductively !)
      Seq→M : Seq S P → M S

    -- This is wrong? It should follow the structure of the M-type?
    M→Seq : M S → Seq S P
    M→Seq = M-coinduction-const (Seq S P) λ x → (λ _ → x .fst) , (λ _ → C (x .fst))

    postulate
      M-Seq : section M→Seq Seq→M
      Seq-M : retract M→Seq Seq→M
-------------------------------
-- EXAMPLES Partiality monad --
-------------------------------

-- _⊑maybe_ : ∀ {A : Set} → container-order (delay-S A)
-- x ⊑maybe y = (x ≡ y) ⊎ ((x ≡ inr tt) × (x ≡ inr tt → ⊥))

-- ⊑maybe-correct : ∀ {A : Set} → correct-order (delay-S A) _⊑maybe_
-- ⊑maybe-correct x = inl refl

-- Seq-part : Set → Set
-- Seq-part A = Seq (delay-S A) (_⊑maybe_)

-------------------
-- EXAMPLES TREE --
-------------------

-- TREES
tree-S : (R : Type₀) (E : Type₀) → Container ℓ-zero
tree-S R E =
  (R ⊎ Unit) ,
  λ { (inl _) -> ⊥
    ; (inr tt) -> E }

tree : (E : Type₀) (R : Type₀) -> Type₀
tree E R = M (tree-S E R)

tree-leaf : ∀ {R} {E}  -> R -> tree R E
tree-leaf r = in-fun (inl r , λ ())

tree-node : ∀ {R} {E} -> (E -> tree R E) -> tree R E
tree-node k = in-fun (inr tt , k)

-- equivalence of trees removing values, only looking at branching!
mutual
  data _∼tree_ {R} {E} : (_ _ : tree R E) → Type₀ where
    ∼leaf : (x y : R)
          → tree-leaf x ∼tree tree-leaf y -- ignore differences in values
    ∼node : (k₁ k₂ : E → tree R E)
          → ((a : E) → k₁ a ∞∼tree k₂ a)
          → tree-node k₁ ∼tree tree-node k₂

  record _∞∼tree_ {E} {R} (x y : tree E R) : Type₀ where
    coinductive
    field
      force : x ∼tree y

open _∞∼tree_

tree/∼ : ∀ E R → Type₀
tree/∼ E R = tree E R / _∼tree_

_⊑tree-S_ : ∀ {R : Type₀} {E : Type₀} → (x y : R ⊎ Unit) → Type₀
_⊑tree-S_ x y =
    (x ≡ y) -- reflexivity
  ⊎ ((x ≡ inr tt) × ((y ≡ inr tt) → ⊥)) -- terminates

⊑tree-S-correct : ∀ {R E} → correct-order (tree-S R E) (_⊑tree-S_ {R = R} {E = E})
⊑tree-S-correct x = inl refl

tree-Seq : ∀ R E → Type₀
tree-Seq R E = Seq (tree-S R E) (_⊑tree-S_ {R = R} {E = E})    

tree-shift :
  ∀ {R E}
  → (t : tree-Seq R E)
  → Σ[ va ∈ R ⊎ Unit ] (isMon' (tree-S R E) (_⊑tree-S_ {R = R} {E = E}) (λ {0 → va ; (suc n) → fst t n}) 0)
  --------------
  → tree-Seq R E
tree-shift {R} {E} = shift-Seq (tree-S R E) (_⊑tree-S_ {R = R} {E = E})    

-- Termination tree
tTree-container : ∀ R E → Container ℓ-zero
tTree-container R E = (Unit ⊎ R) ⊎ Unit , λ {(inl (inl x)) → E ; _ → ⊥}

tTree : ∀ R E → Set
tTree R E = M (tTree-container R E)

tTree-terminated : ∀ {R E} → tTree R E
tTree-terminated = in-fun (inr tt , λ ())

_⊑tTree_ : ∀ {R E} → (_ _ : tTree R E) → Set
x ⊑tTree y =
  (x ≡ y) ⊎
  ((x ≡ tTree-terminated) × (y ≡ tTree-terminated → ⊥))

mutual
  Ptree→Tree-tree : ∀ {R E} → P₀ (tree-S R E) (tree R E) → (ℕ → E) → tree-Seq R E
  Ptree→Tree-tree (inl t , _) = λ _ → (λ _ → inl t) , (λ _ → inl refl)
  Ptree→Tree-tree {R} {E} (inr tt , k) e =
    let temp = (tree→Tree-tree (k (e 0)) (e ∘ suc)) in
    tree-shift {R = R} {E = E}
      temp
      (inr tt , (case fst temp 0 return (λ x → isMon' (tree-S R E) (_⊑tree-S_ {R = R} {E = E})
        (λ { 0 → inr tt
           ; (suc 0) → x
           ; (suc (suc n)) → fst (tree→Tree-tree (k (e 0)) (λ x → e (suc x))) (suc n)
           })
        0) of
          λ {(inl r) → inr (refl , inl≢inr)
            ;(inr tt) → inl refl }))
  
  tree→Tree-tree : ∀ {R E} → tree R E → ((ℕ → E) → tree-Seq R E)
  tree→Tree-tree {R} {E} = M-coinduction-const ((ℕ → E) → tree-Seq R E) Ptree→Tree-tree

-- shift-Seq :
--   ∀ {ℓ} (S : Container ℓ) (P : container-order S)
--   → (t : Seq S P)
--   → Σ[ va ∈ (S .fst) ] (isMon' S P (λ {0 → va ; (suc n) → fst t n}) 0)
--   --------------
--   → Seq S P
-- shift-Seq _ _ (g , a) (va , mon) =
--   (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})



-- mutual
--   Ptree→tree-Seq : ∀ {E R} → (ℕ → E) → P₀ (tree-S E R) (tree E R) → tree-Seq E R
--   Ptree→tree-Seq _ (inl r , _) = (λ _ → inl r) , (λ _ → inl refl)
--   Ptree→tree-Seq {E} {R} e (inr _ , b) =
--     shift-Seq (tree-S E R) (_⊑tree-S_ {E = E} {R = R}) (tree→tree-Seq (e ∘ suc) {!!}) (inr tt , {!!})
--     -- tree→tree-Seq (e ∘ suc) (b (e 0))
--     -- shift-Seq (tree-S E R) (_⊑tree-S_ {E = E} {R = R}) {!!} {!!}

--   tree→tree-Seq : ∀ {E R} → (ℕ → E) → tree E R → tree-Seq E R
--   tree→tree-Seq {E} {R} e = M-coinduction-const (tree-Seq E R) (Ptree→tree-Seq e)


data _⊑tree_ {E R} : (_ _ : tree E R) → Set₁ where
  ⊑-leaf : ∀ x → tree-leaf x ⊑tree tree-leaf x
  ⊑-node : ∀ x y → (∀ e → x e ⊑tree y e) → tree-node x ⊑tree tree-node y

mutual
  abstract
    -- silhouete-tree
    data sTree (E : Set) : Set where
      leaf : sTree E
      node : (E → ∞sTree E) → sTree E
      sTree-isSet : isSet (sTree E)
      α : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y

    record ∞sTree (E : Set) : Set where
      coinductive
      field
        force : sTree E

  abstract
    -- How "defined" the M-type is.
    data _⊑_ {E : Set} : (_ _ : sTree E) → Set where
      ⊑-refl            : ∀ x → x ⊑ x
      ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
      ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

open ∞sTree

-- abstract
--   mutual
--     Ptree→sTree : ∀ {R E} → P₀ (tree-S R E) (tree R E) → sTree E
--     Ptree→sTree (inl _ , _) = leaf
--     Ptree→sTree (inr _ , b) = node (∞tree→sTree ∘ b)

--     ∞tree→sTree : ∀ {E R} → tree E R → ∞sTree E
--     force (∞tree→sTree e) = tree→sTree e

--     tree→sTree : ∀ {E R} → tree E R → sTree E
--     tree→sTree {E} = M-coinduction-const (sTree E) Ptree→sTree

--   recc :
--     ∀ {A B : Set₀} {R : A → A → Set₀} →
--     (f : A → B) →
--     (∀ x y → R x y → f x ≡ f y) →
--     isSet B →
--     A / R → B
--   recc {A} {B} {R} f feq B-set ar =
--     Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

--   tree→sTree-mono : ∀ {E R} (x y : tree E R) → x ⊑tree y → tree→sTree x ⊑ tree→sTree y
--   tree→sTree-mono x y (⊑-leaf a) = ⊑-refl (tree→sTree (tree-leaf a))
--   tree→sTree-mono x y (⊑-node a b p) =
--     let temp : ∀ e → tree→sTree (a e) ⊑ tree→sTree (b e)
--         temp = λ e → tree→sTree-mono (a e) (b e) (p e) in
--     {!!}

-- -- --   tree→sTree-≈→≡ : ∀ {E R} (x y : tree E R) → x ∼tree y → tree→sTree x ≡ tree→sTree y
-- -- --   tree→sTree-≈→≡ x y (∼leaf _ _) = refl
-- -- --   tree→sTree-≈→≡ x y (∼node {A} e k1 k2 p) =
-- -- --     let temp : (a : A) → tree→sTree (k1 a) ≡ tree→sTree (k2 a)
-- -- --         temp a = tree→sTree-≈→≡ (k1 a) (k2 a) (force (p a)) in
-- -- --     tree→sTree (tree-vis e k1)
-- -- --       ≡⟨ α {!!} {!!} ⟩
-- -- --     tree→sTree (tree-vis e k2) ∎
-- -- --   -- α (tree→sTree-mono x y {!!}) {!!}

-- -- --   -- tree→sTree (tree-vis e k1) ≡ tree→sTree (tree-vis e k2)

-- -- --   tree/∼→sTree : ∀ {E R} → tree/∼ E R → sTree E
-- -- --   tree/∼→sTree = recc (tree→sTree) tree→sTree-≈→≡ sTree-isSet

