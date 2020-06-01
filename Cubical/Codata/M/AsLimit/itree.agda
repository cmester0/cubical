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
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M

open import Cubical.HITs.SetQuotients

open import Cubical.Functions.Embedding

M-coinduction :
  ∀ {ℓ ℓ'} {S : Container ℓ}
  → (k : M S → Type ℓ')
  → ((x : P₀ S (M S)) → k (in-fun x))
  ---------------
  → ((x : M S) → (k x))
M-coinduction k x x₁ =
  transport (λ i → k (in-inverse-out i x₁))
  (case out-fun x₁ return (λ x₂ → k (in-fun x₂)) of x)

M-coinduction-const :
  ∀ {ℓ ℓ'} {S : Container ℓ}
  → {k : Set ℓ'}
  → ((x : P₀ S (M S)) → k)
  ---------------
  → ((x : M S) → k)
M-coinduction-const {k = k} x x₁ =
  case out-fun x₁ return (λ x₂ → k) of x
  
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

mutual
  data ITree (E : Type₀ -> Type₁) (R : Type₀) : Set₁ where
    Ret : R -> ITree E R
    Tau : ∞ITree E R → ITree E R
    Vis : ∀ {A : Type₀} -> E A -> (A -> ∞ITree E R) -> ITree E R

  record ∞ITree (E : Type₀ -> Type₁) (R : Type₀) : Set₁ where
    coinductive
    field
      force : ITree E R

open ∞ITree

postulate
  itree-eq : ∀ E R → itree E R ≡ ITree E R

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
  data _∼it_ {E R} : (_ _ : itree E R) → Set₁ where
    ∼ret : ∀ r → ret r ∼it ret r
    ∼tau : ∀ t u → t ∞∼it u → tau t ∼it tau u
    ∼tauL : ∀ t u → t ∼it tau u → tau t ∼it tau u
    ∼tauR : ∀ t u → tau t ∼it u → tau t ∼it tau u
    ∼vis : ∀ {A} (e : E A) k1 k2 → (∀ x → k1 x ∞∼it k2 x) → vis e k1 ∼it vis e k2

  record _∞∼it_ {E R} (x y : itree E R) : Set₁ where
    coinductive
    field
      force : x ∼it y

quotiented-itree : ∀ E R → Set₁
quotiented-itree E R = itree E R / _∼it_

mutual
  data _∼IT_ {E R} : (_ _ : ITree E R) → Set₁ where
    ∼ret : ∀ r → Ret r ∼IT Ret r
    ∼tau : ∀ t u → force t ∞∼IT force u → Tau t ∼IT Tau u
    ∼tauL : ∀ t u → force t ∼IT Tau u → Tau t ∼IT Tau u
    ∼tauR : ∀ t u → Tau t ∼IT force u → Tau t ∼IT Tau u
    ∼vis : ∀ {A} (e : E A) k1 k2 → (∀ x → force (k1 x) ∞∼IT force (k2 x)) → Vis e k1 ∼IT Vis e k2

  record _∞∼IT_ {E R} (x y : ITree E R) : Set₁ where
    coinductive
    field
      force : x ∼IT y

quotiented-ITree : ∀ E R → Set₁
quotiented-ITree E R = ITree E R / _∼IT_

------------------------
-- ITrees / ∼ ≡ QIIT --
------------------------

mutual
  infix 4  _⊑_

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
_↑ {E = E} x = (x ≡ inl (inr tt))

_↑A :  ∀ {E : Type₀ → Type₁} {R : Type₀} → itree-S E R .fst → Set₁
_↑A {E = E} x = (Σ[ A ∈ Type₀ ] Σ[ e ∈ E A ] x ≡ inr (A , e))

_LE_ : ∀ {E : Type₀ → Type₁} {R : Type₀} → (_ _ : itree-S E R .fst) → Set₁
x LE y = (x ≡ y) ⊎ ((x ↑) × ((y ↑ → ⊥) ⊎ (y ↑A → ⊥)))

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

  isEmbedding→Injection→ :
    ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (a : A -> B)
    → (e : isEmbedding a)
    ----------------------
    → ∀ {x y : A} ->
    (a x ≡ a y) → (x ≡ y)
  isEmbedding→Injection→ a e {x = x} {y = y} = equivFun (invEquiv (cong a , e x y))

  shift' : ∀ {E : Type₀ → Type₁} {R : Type₀} → Seq E R → Seq E R
  shift' {E = E} {R = R} t =
    shift-seq t
      ((inl (inr tt)) ,
       (case fst t 0 return (λ x → ismon' (λ {0 → inl (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n}) 0) of
       λ {(inl (inl r)) → inr (refl , inl (inl≢inr ∘ (isEmbedding→Injection→ inl isEmbedding-inl)))
         ;(inl (inr tt)) → inl refl
         ;(inr (A , e)) → inr (refl , inl (inl≢inr ∘ sym))}))

  unshift : ∀ {E : Type₀ → Type₁} {R : Type₀} → Seq E R → Seq E R
  unshift (g , a) = g ∘ suc , a ∘ suc

  unshift-shift : ∀ {E : Type₀ → Type₁} {R : Type₀} t {va-mon} → unshift {E = E} {R = R} (shift-seq t va-mon) ≡ t
  unshift-shift (g , a) = refl

  shift-unshift : ∀ {E : Type₀ → Type₁} {R : Type₀} t → shift-seq {E = E} {R = R} (unshift t) (fst t 0 , snd t 0) ≡ t
  shift-unshift (g , a) =
    ΣPathP ((funExt λ {0 → refl ; (suc n) → refl }) , λ {i 0 → a 0 ; i (suc n) → a (suc n)})

abstract
  mutual
    Seq→ITree : ∀ {E R} → Seq E R → ITree E R
    Seq→ITree {E} {R} (s , q) = case s 0 of λ {(inl (inl r)) → Ret r
                                               ;(inl (inr tt)) → Tau (Seq→∞ITree (shift' (s , q)))
                                               ;(inr (A , e)) → Vis e λ x → Seq→∞ITree {!!}}

    Seq→∞ITree : ∀ {E R} → Seq E R → ∞ITree E R
    force (Seq→∞ITree {E} {R} s) = Seq→ITree s

  -- mutual
  --   ITree→Seq : ∀ {E R} → ITree E R → Seq E R
  --   ITree→Seq {E} {R} (Ret r) = (λ _ → inl (inl r)) , λ n → inl refl
  --   ITree→Seq {E} {R} (Tau t) = shift' (∞ITree→Seq t)
  --   ITree→Seq {E} {R} (Vis A e) = {!!}

  --   ∞ITree→Seq : ∀ {E R} → ∞ITree E R → Seq E R
  --   ∞ITree→Seq x = ITree→Seq (force x)

  -- itree→Qitree : ∀ {E R} → itree E R → Qitree E R
  -- itree→Qitree {E} {R} = M-coinduction-const
  --   λ {(inl (inl r) , b) → η r
  --     ;(inl (inr tt) , t) →
  --       ⊔ ({!!} , {!!})}
  --   where
  --     temp : M (itree-S E R) → ℕ → Qitree E R
  --     temp = M-coinduction-const
  --       λ {(inl (inl r) , b) n → η r 
  --         ;(inl (inr tt) , t) n → temp (t (lift tt)) (suc n)
  --         }
