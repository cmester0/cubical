{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.itree where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M

open import Cubical.HITs.SetQuotients

open import Cubical.Functions.Embedding

-- ITrees
-- https://arxiv.org/pdf/1906.00046.pdf
-- Interaction Trees: Representing Recursive and Impure Programs in Coq
-- Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, Steve Zdancewic

-- Itrees without Vis constructor is the delay monad

-- Delay monad defined as an M-type
delay-S : (R : Type₀) -> Container ℓ-zero
delay-S R = (Unit ⊎ R) , λ { (inr _) -> ⊥ ; (inl tt) -> Unit }

delay : (R : Type₀) -> Type₀
delay R = M (delay-S R)

delay-ret : {R : Type₀} -> R -> delay R
delay-ret r = in-fun (inr r , λ ())

delay-tau : {R : Type₀} -> delay R -> delay R
delay-tau S = in-fun (inl tt , λ x → S)

-- Bottom element raised
data ⊥₁ : Type₁ where

-- Itrees without Tau constructor is trees or even trees
-- TREES
tree-S : (E : Type₀ -> Type₁) (R : Type₀) -> Container (ℓ-suc ℓ-zero)
tree-S E R = (R ⊎ (Σ[ A ∈ Type₀ ] (E A))) , (λ { (inl _) -> ⊥₁ ; (inr (A , e)) -> Lift A } )

tree : (E : Type₀ -> Type₁) (R : Type₀) -> Type₁
tree E R = M (tree-S E R)

tree-ret : ∀ {E} {R}  -> R -> tree E R
tree-ret {E} {R} r = in-fun (inl r , λ ())

tree-vis : ∀ {E} {R}  -> ∀ {A} -> E A -> (A -> tree E R) -> tree E R
tree-vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x } )

------------
-- ITrees --
------------

itree-S : ∀ (E : Type₀ -> Type₁) (R : Type₀) -> Container (ℓ-suc ℓ-zero)
itree-S E R = ((R ⊎ Unit) ⊎ (Σ[ A ∈ Type₀ ] (E A))) , (λ { (inl (inl _)) -> ⊥₁ ; (inl (inr _)) -> Lift Unit ; (inr (A , e)) -> Lift A } )

itree :  ∀ (E : Type₀ -> Type₁) (R : Type₀) -> Type₁
itree E R = M (itree-S E R)

ret : ∀ {E} {R}  -> R -> itree E R
ret r = in-fun (inl (inl r) , λ ())

tau : {E : Type₀ -> Type₁} -> {R : Type₀} -> itree E R -> itree E R
tau t = in-fun (inl (inr tt) , λ _ → t)

vis : ∀ {E} {R}  -> ∀ {A : Type₀} -> E A -> (A -> itree E R) -> itree E R
vis {A = A} e k = in-fun (inr (A , e) , λ { (lift x) -> k x })

--------------------------------
-- ITrees Strong Bisimulation --
--------------------------------

-- mutual
--   data _∼IT_ {E R} : (_ _ : itree E R) → Set₁ where
--     ∼ret : ∀ r → ret r ∼IT ret r
--     ∼tau : ∀ t u → t ∞∼IT u → tau t ∼IT tau u
--     ∼vis : ∀ {A} (e : E A) k1 k2 → (∀ x → k1 x ∞∼IT k2 x) → vis e k1 ∼IT vis e k2

--   record _∞∼IT_ {E R} (x y : itree E R) : Set₁ where
--     coinductive
--     field
--       force : x ∼IT y

-- bisimulation _∼IT_

-------------------------------------
-- ITrees Strong Weak Bisimulation --
-------------------------------------

mutual
  data _∼IT_ {E R} : (_ _ : itree E R) → Set₁ where
    ∼ret : ∀ r → ret r ∼IT ret r
    ∼tau : ∀ t u → t ∞∼IT u → tau t ∼IT tau u
    ∼tauL : ∀ t u → t ∼IT tau u → tau t ∼IT tau u
    ∼tauR : ∀ t u → tau t ∼IT u → tau t ∼IT tau u
    ∼vis : ∀ {A} (e : E A) k1 k2 → (∀ x → k1 x ∞∼IT k2 x) → vis e k1 ∼IT vis e k2

  record _∞∼IT_ {E R} (x y : itree E R) : Set₁ where
    coinductive
    field
      force : x ∼IT y

quotiented-itree : ∀ E R → Set₁
quotiented-itree E R = itree E R / _∼IT_

------------------------
-- ITrees / ∼ ≡ QIIT --
------------------------

mutual
  infix 4  _⊑_

  abstract
    -- The partiality monad.

    data Qitree (E : Type₀ → Type₁) (R : Type₀) : Type₁ where
      never  : Qitree E R
      η      : R → Qitree E R
      ⊔      : Increasing-sequence E R → Qitree E R
      α      : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
      ⊥-isSet : isSet (Qitree E R)
      
      visq   : ∀ {A : Type₀} -> E A -> (A -> Qitree E R) -> Qitree E R
      visq-eq : ∀ {A} (e : E A) k1 k2 → (∀ x → k1 x ≡ k2 x) → visq e k1 ≡ visq e k2

  -- Increasing sequences.

  Increasing-sequence : (Type₀ → Type₁) → Type₀ → Type₁
  Increasing-sequence E R = Σ[ f ∈ (ℕ → Qitree E R) ] ((n : ℕ) → f n ⊑ f (suc n))

  -- Upper bounds.

  Is-upper-bound : {E : Type₀ → Type₁} {R : Type₀} → Increasing-sequence E R → Qitree E R → Type₁
  Is-upper-bound s x = (n : ℕ) → (fst s n) ⊑ x

  -- A projection function for Increasing-sequence.

  abstract
    -- An ordering relation.
    data _⊑_ {E : Type₀ → Type₁} {A : Type₀} : (_ _ : Qitree E A) → Type₁ where
      ⊑-refl            : ∀ x → x ⊑ x
      ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
      never⊑            : ∀ x → never ⊑ x
      upper-bound       : ∀ s → Is-upper-bound s (⊔ s)
      least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⊔ s ⊑ ub
      ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

--------------
-- Maybe --
--------------

infix 4 _↑ _↓_

-- x ↓ y means that the computation x has the value y.

_↓_ : ∀ {E : Type₀ → Type₁} {R : Type₀} → itree-S E R .fst → R → Set₁
x ↓ y = x ≡ inl (inl y)

-- x ↑ means that the computation x does not have a value.
                                                      
_↑ :  ∀ {E : Type₀ → Type₁} {R : Type₀} → itree-S E R .fst → Set₁
_↑ {E = E} x = (Σ[ A ∈ Type₀ ] Σ[ e ∈ E A ] x ≡ inr (A , e)) ⊎ (x ≡ inl (inr tt))

_LE_ : ∀ {E : Type₀ → Type₁} {R : Type₀} → (_ _ : itree-S E R .fst) → Set₁
x LE y = (x ≡ y) ⊎ ((x ↑) × (y ↑ → ⊥))

--------------
-- Sequence --
--------------

data ⊥ℓ {ℓ} : Set ℓ where

⊥ℓrec : ∀ {ℓ ℓ'} {A : Type ℓ} → ⊥ℓ {ℓ'} → A
⊥ℓrec ()

inl≢inr : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} → {x : A} {y : B} → inl x ≡ inr y → ⊥
inl≢inr {A = A} {B} x =
  ⊥ℓrec (subst (λ {(inl x) → A ⊎ B ; (inr y) → ⊥ℓ}) x (x i0))

module _ where
  ismon : ∀ {E : Type₀ → Type₁} {R : Type₀} → (g : ℕ → itree-S E R .fst) → Set₁
  ismon {A} g = (n : ℕ) → (g n) LE (g (suc n))

  ismon' : ∀ {E : Type₀ → Type₁} {R : Type₀} → (g : ℕ → itree-S E R .fst) → ℕ → Set₁
  ismon' {A} g n = (g n) LE (g (suc n))

  Seq : (Type₀ → Type₁) → (Type₀) → Type₁
  Seq E R = (Σ[ g ∈ (ℕ → itree-S E R .fst) ] (ismon g))

  shift-seq : ∀ {E : Type₀ → Type₁} {R : Type₀} → (t : Seq E R) → Σ (itree-S E R .fst) (λ va → ismon' (λ {0 → va ; (suc n) → fst t n}) 0) → Seq E R
  shift-seq (g , a) (va , mon) = (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})

  shift' : ∀ {E : Type₀ → Type₁} {R : Type₀} → Seq E R → Seq E R
  shift' {E = E} {R = R} t =
    shift-seq t
      ((inl (inr tt)) ,
       (case fst t 0 return (λ x → ismon' (λ {0 → inl (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n}) 0) of
       λ {(inl (inl r)) → inr (inr refl , λ {(inl (A , (e , p))) → inl≢inr p ; (inr x) →
               inl≢inr (transport
                          (isEmbedding→Injection {ℓ = ℓ-suc ℓ-zero} (inl {B = (Σ[ A ∈ Type₀ ] (E A))}) (isEmbedding-inl {ℓ-suc ℓ-zero} {ℓ-suc ℓ-zero})
                            {f = λ { (lift tt) → (inl r) }}
                            {g = λ { (lift tt) → inr tt }} (lift tt))
                          (cong (λ a → inl {B = (Σ[ A ∈ Type₀ ] (E A))} ((λ { tt → a }) tt)) x))})
         ;(inl (inr tt)) → {!!}}))

  unshift : ∀ {E : Type₀ → Type₁} {R : Type₀} → Seq E R → Seq E R
  unshift (g , a) = g ∘ suc , a ∘ suc

  -- works for any -- (fst t 0)
  unshift-shift : ∀ {E : Type₀ → Type₁} {R : Type₀} t {va-mon} → unshift {E = E} {R = R} (shift-seq t va-mon) ≡ t
  unshift-shift (g , a) = refl

  shift-unshift : ∀ {E : Type₀ → Type₁} {R : Type₀} t → shift-seq {E = E} {R = R} (unshift t) (fst t 0 , snd t 0) ≡ t
  shift-unshift (g , a) =
    ΣPathP ((funExt λ {0 → refl ; (suc n) → refl }) , λ {i 0 → a 0 ; i (suc n) → a (suc n)})
