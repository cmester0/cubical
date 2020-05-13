{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.partiality-monad where

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.itree
open import Cubical.Codata.M.AsLimit.M

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Foundations.HLevels

-- ismon : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → Set
-- ismon {A} g = (n : ℕ) → (g n ≡ g (suc n))
--             ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

-- ismon' : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → ℕ → Set
-- ismon' {A} g n = (g n ≡ g (suc n))
--                ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

-- record seq (A : Type₀) : Type₀ where
--   field
--     function : ℕ → A ⊎ Unit
--     monotone : ismon function

-- open seq

-- mutual
--   f-delay-seq' : ∀ {A} → (delay A) → (ℕ → A ⊎ Unit)
--   f-delay-seq' {A} = M-coinduction-const (ℕ → A ⊎ Unit) f-delay→seq

--   f-delay→seq : ∀ {A} → P₀ (delay-S A) (delay A) → (ℕ → A ⊎ Unit)
--   f-delay→seq (inl r , b) _ = inl r
--   f-delay→seq (inr r , b) 0 = inr r
--   f-delay→seq (inr r , b) (suc n) = f-delay-seq' (b tt) n
  
-- mutual
--   m-delay-seq' : ∀ {A} → (x : delay A) → ismon (f-delay-seq' {A} x)
--   m-delay-seq' {A} x = M-coinduction (λ y → ismon (f-delay-seq' {A} y)) m-delay-seq x

--   m-delay-seq : ∀ {A} → (x : P₀ (delay-S A) (M (delay-S A))) → ismon (f-delay-seq' (in-fun x))
--   m-delay-seq (inl r , b) = λ _ → inl refl
--   m-delay-seq (inr r , b) 0 = M-coinduction-const (ismon' (f-delay-seq' (in-fun (inr r , b))) 0) (λ {(inl _ , b) → ? ; (inr _ , b) → ?}) (b tt)
-- -- first element never defined if delay is later! , seq 0 = inr r , inl ?
--   m-delay-seq (inr r , b) (suc n) = {!!} -- case fst (f-delay-seq (b tt) n) 0 of ? -- when is the change defined ?? 
  
-- -- delay→seq : ∀ {A} → (delay A) → seq A
-- -- function (delay→seq {A} x) = f-delay-seq' x
-- -- monotone (delay→seq {A} x) = m-delay-seq' x

-- --   -- shift-seq : ∀ {A} → (t : Seq A) → Σ (A ⊎ Unit) (λ va → ismon' (λ {0 → va ; (suc n) → fst t n}) 0) → Seq A
-- --   -- shift-seq (g , a) (va , mon) = (λ {0 → va ; (suc n) → g n}) ,
-- --   -- monotone (λ {0 → mon ; (suc n) → a n})

-- --   -- shift' : ∀ {A} → Seq A → Seq A
-- --   -- shift' t =
-- --   --   shift-seq t
-- --   --     ((inr tt) ,
-- --   --      (case (fst t 0) return (λ x → ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0) of
-- --   --        λ {(inl r) → inr (refl , inl≢inr)
-- --   --          ;(inr tt) → inl refl}))

-- -- --     ∞delay→seq : ∀ {A} → P₀ (delay-S A) (delay A) → seq A
-- -- --     function (∞delay→seq {A} (inl a , _)) = (λ _ → inl a)
-- -- --     monotone (∞delay→seq {A} (inl a , _)) = (λ _ → inl refl)
-- -- --     function (∞delay→seq {A} (inr tt , t)) = (λ {0 → inr tt ; (suc n) → function (delay→seq (t tt)) n})
-- -- --     monotone (∞delay→seq {A} (inr tt , t)) = monotone shift' (delay→Seq (t tt))

-- -- -- ((inr tt) ,
-- -- --        (case (fst t 0) return (λ x → ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0) of
-- -- --          λ {(inl r) → inr (refl , inl≢inr)
-- -- --            ;(inr tt) → inl refl}))

--------------
-- Sequence --
--------------

module _ where
  ismon : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → Set
  ismon {A} g = (n : ℕ) → (g n ≡ g (suc n))
              ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

  ismon' : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → ℕ → Set
  ismon' {A} g n = (g n ≡ g (suc n))
                 ⊎ ((g n ≡ inr tt) × ((g (suc n) ≡ inr tt) → ⊥))

  Seq : Set → Set
  Seq A = (Σ (ℕ → A ⊎ Unit) (λ g → ismon g))

  shift-seq : ∀ {A} → (t : Seq A) → Σ (A ⊎ Unit) (λ va → ismon' (λ {0 → va ; (suc n) → fst t n}) 0) → Seq A
  shift-seq (g , a) (va , mon) = (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})

  shift' : ∀ {A} → Seq A → Seq A
  shift' t =
    shift-seq t
      ((inr tt) ,
       (case (fst t 0) return (λ x → ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0) of
         λ {(inl r) → inr (refl , inl≢inr)
           ;(inr tt) → inl refl}))

  unshift : ∀ {A} → Seq A → Seq A
  unshift (g , a) = g ∘ suc , a ∘ suc

  -- works for any -- (fst t 0)
  unshift-shift : ∀ {A} t {va-mon} → unshift {A = A} (shift-seq t va-mon) ≡ t
  unshift-shift {A = A} (g , a) = refl

  shift-unshift : ∀ {A} t → shift-seq {A = A} (unshift t) (fst t 0 , snd t 0) ≡ t
  shift-unshift (g , a) =
    ΣPathP ((funExt λ {0 → refl ; (suc n) → refl }) , λ {i 0 → a 0 ; i (suc n) → a (suc n)})

----------------------------------
-- Sequence equivalent to Delay --
----------------------------------

-- module _ where
--   {-# NON_TERMINATING #-}
--   mutual
--     ∞delay→Seq' : ∀ {A} → P₀ (delay-S A) (delay A) → Seq A
--     ∞delay→Seq' {A} (inl a , _) = (λ _ → inl a) , (λ _ → inl refl)
--     ∞delay→Seq' {A} (inr tt , t) = shift' (delay→Seq' (t tt))
  
--     delay→Seq' : ∀ {A} → (delay A) → Seq A
--     delay→Seq' {A} = M-coinduction-const (Seq A) ∞delay→Seq'

--   ∞delay→Seq : ∀ {A} → P₀ (delay-S A) (delay A) → Seq A  
--   ∞delay→Seq {A} (inl a , _) = (λ _ → inl a) , (λ _ → inl refl)
--   ∞delay→Seq {A} (inr tt , t) = shift' (delay→Seq' (t tt))
  
--   delay→Seq : ∀ {A} → (delay A) → Seq A
--   delay→Seq {A} = M-coinduction-const (Seq A) ∞delay→Seq

  -- TODO : this should equal (delay-tau (Seq→delay' (unshift (g , q))))
  -- private
  --   lift-x : ∀ {A} → Seq A → (n : ℕ) → Wₙ (delay-S A) n
  --   lift-x (g , q) 0 = lift tt
  --   lift-x (g , q) (suc n) = g 0 , λ _ → lift-x (unshift (g , q)) n

  --   lift-π : ∀ {A} → (t : Seq A) → (n : ℕ) → πₙ (delay-S A) (lift-x t (suc n)) ≡ (lift-x t n)
  --   lift-π (g , q) 0 = refl {x = lift tt}
  --   lift-π (g , q) (suc n) i = g 0 , λ _ → lift-π (unshift (g , q)) n i
                                              
  -- Seq→delay : ∀ {A} → Seq A → delay A
  -- Seq→delay (g , q) = case g 0 of λ {(inl r) → delay-ret r ; (inr tt) → (lift-x (g , q)) , (lift-π (g , q))}
  
  -- {-# NON_TERMINATING #-}
  -- Seq→delay' : ∀ {A} → Seq A → delay A
  -- Seq→delay' (g , q) = case g 0 of λ {(inl r) → delay-ret r ; (inr tt) → delay-tau (Seq→delay' (unshift (g , q)))}
  
  -- Seq→delay : ∀ {A} → Seq A → delay A
  -- Seq→delay (g , q) = case g 0 of λ {(inl r) → delay-ret r ; (inr tt) → delay-tau (Seq→delay' (unshift (g , q)))}

  -- ∞delay-Seq : ∀ {R} (b : P₀ (delay-S R) (delay R)) → Seq→delay (delay→Seq (in-fun b)) ≡ (in-fun b)
  -- ∞delay-Seq {R} (inl r , b) =
  --   Seq→delay (delay→Seq (in-fun (inl r , b)))
  --     ≡⟨ cong Seq→delay (cong (λ a → case a return (λ x₂ → Seq R) of ∞delay→Seq) (out-inverse-in-x (inl r , b))) ⟩
  --   delay-ret r
  --     ≡⟨ cong (λ a → in-fun (inl r , a)) (isContr→isProp isContr⊥→A (λ ()) b) ⟩
  --   in-fun (inl r , b) ∎
  -- ∞delay-Seq {R} (inr tt , t) =
  --   Seq→delay (delay→Seq (in-fun (inr tt , t)))
  --     ≡⟨ cong Seq→delay (cong (λ a → case a return (λ x₂ → Seq R) of ∞delay→Seq) (out-inverse-in-x (inr tt , t))) ⟩
  --   Seq→delay (∞delay→Seq (inr tt , t))
  --     ≡⟨ refl ⟩
  --   Seq→delay (shift' (delay→Seq' (t tt)))
  --     ≡⟨ refl ⟩
  --   delay-tau (Seq→delay' (unshift (shift' (delay→Seq' (t tt)))))
  --     ≡⟨ cong (delay-tau ∘ Seq→delay') unshift-shift (delay→Seq' (t tt)) ⟩
  --   delay-tau (Seq→delay' (delay→Seq' (t tt)))
  --     ≡⟨ ? ⟩ -- cong delay-tau (delay-Seq (t tt))
  --   in-fun (inr tt , t) ∎

  --   postulate
  --     delay-Seq : ∀ {R} (b : delay R) → Seq→delay (delay→Seq b) ≡ b
  --   -- delay-Seq = M-coinduction (λ x → Seq→delay (delay→Seq x) ≡ x) ∞delay-Seq

  -- Seq-delay : ∀ {R} (b : Seq R) → delay→Seq (Seq→delay b) ≡ b
  -- Seq-delay (g , q) = case g 0 of \{(inl r) -> refl ; (inr tt) -> delay→Seq (Seq→delay (g , q)) ≡⟨ cong shift (Seq-delay (unshift (g, q))) ⟩ shift-unshift (g, q) }

  -- delay-Seq-Iso : ∀ {A} → Iso (delay A) (Seq A)
  -- delay-Seq-Iso = (iso delay→Seq Seq→delay Seq-delay delay-Seq)

  -- delay≡Seq : ∀ {A} → delay A ≡ Seq A
  -- delay≡Seq = isoToPath delay-Seq-Iso

-----------------------
-- Sequence ordering --
-----------------------

open import Cubical.Data.Nat.Order

_↓seq_ : ∀ {A} → Seq A → A → Set
s ↓seq a = Σ[ n ∈ ℕ ] fst s n ≡ inl a

_⊑seq_ : ∀ {A} → ∀ (_ _ : Seq A) → Set
_⊑seq_ {A} s t = (a : A) → ∥ (s ↓seq a) ∥ → ∥ t ↓seq a ∥

_∼seq_ : ∀ {A} → ∀ (_ _ : Seq A) → Set
s ∼seq t = s ⊑seq t × t ⊑seq s

_↓′_ : ∀ {A} → Seq A → A → Set _
(f , _) ↓′ y = Σ[ m ∈ ℕ ] ((f m ≡ inl y) × (∀ n → (f n ≡ inr tt → ⊥) → m ≤ n))
  where open import Cubical.Data.Nat.Order

postulate
  ⇓′-propositional : ∀ {A} → isSet A → ∀ x {y : A} → isProp (x ↓′ y)
-- ⇓′-propositional A-set x@(f , _) {y} =
--   {!!} -- TODO
  -- let temp : Σ[ m ∈ ℕ ] (isProp ((f m ≡ inl y) × (∀ n → (f n ≡ inr tt → ⊥) → m ≤ n)))
  --     temp = {!!}
  -- in
  -- λ x' y' → transport Σ-split ({!!} , {!!})
  -- where open import Cubical.Data.Nat.Order

Other-singleton : {a : Level} {A : Set a} → A → Set a
Other-singleton {A = A} x = Σ-syntax A λ y → x ≡ y

inspect : ∀ {A : Set} -> (x : A ⊎ Unit) → Other-singleton x
inspect (inl r) = (inl r) , refl
inspect (inr tt) = (inr tt) , refl

⇓′→⇓ : ∀ {A} x {y : A} → x ↓′ y → x ↓seq y
⇓′→⇓ = λ x x₁ → fst x₁ , proj₁ (snd x₁)

----------------------
-- Partiality monad --
----------------------

-- Partiality monad (QIIT)
-- Paper: Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type (https://arxiv.org/abs/1610.09254)
-- Authors: Thorsten Altenkirch, Nils Anders Danielsson, Nicolai Kraus
-- Formalization: http://www.cse.chalmers.se/~nad/listings/partiality-monad/Partiality-monad.Inductive.html
mutual
  infix 10 <_>⊥
  infix 4  _⊑_

  abstract
    -- The partiality monad.

    data <_>⊥ {ℓ} (A : Type ℓ) : Type ℓ where
      never  : < A >⊥
      η      : A → < A >⊥
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

  abstract
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

abstract
  Maybe→⊥ : ∀ {A : Type₀} → A ⊎ Unit → < A >⊥
  Maybe→⊥ (inr tt)  = never
  Maybe→⊥ (inl y) = η y

  infix 4 _↑ _↓_

  -- x ↓ y means that the computation x has the value y.

  _↓_ : ∀ {A : Set} → A ⊎ Unit → A → Set
  x ↓ y = x ≡ inl y

  -- x ↑ means that the computation x does not have a value.

  _↑ :  ∀ {A : Set} → A ⊎ Unit → Set
  x ↑ = x ≡ inr tt

  LE : ∀ {A : Set} → A ⊎ Unit → A ⊎ Unit → Set
  LE x y = (x ≡ y) ⊎ ((x ↑) × (y ↑ → ⊥))

  Increasing-at : ∀ {A : Set} → ℕ → (ℕ → A ⊎ Unit) → Set
  Increasing-at n f = LE (f n) (f (suc n))

  Increasing : ∀ {A : Set} → (ℕ → A ⊎ Unit) → Set
  Increasing f = ∀ n → Increasing-at n f

  ≰→> : ∀ {m n} → (m ≤ n → ⊥) → n < m
  ≰→> {zero} {n} p = Cubical.Data.Empty.elim (p (zero-≤))
  ≰→> {suc m} {zero}  p = suc-≤-suc (zero-≤)
  ≰→> {suc m} {suc n} p = suc-≤-suc (≰→> (p ∘ suc-≤-suc))

  Dec : ∀ {p} → Set p → Set p
  Dec P = P ⊎ (P → ⊥)

  Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} →
              (A → B → Set ℓ) → Set (ℓ-max (ℓ-max a b) ℓ)
  Decidable _∼_ = ∀ x y → Dec (x ∼ y)

  _≤?_ : Decidable _≤_
  zero  ≤? n     = inl (zero-≤)
  suc m ≤? zero  = inr λ { x → ¬-<-zero x }
  suc m ≤? suc n = Cubical.Data.Sum.map suc-≤-suc (λ m≰n → m≰n ∘ pred-≤-pred) (m ≤? n)

  ≤⊎> : ∀ m n → (m ≤ n) ⊎ (n < m)
  ≤⊎> m n = Cubical.Data.Sum.map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→> (m ≤? n)

  postulate
    ↑-downwards-closed : ∀ {A} {f : ℕ → A ⊎ Unit} {m n} →
                         Increasing f → m ≤ n → f n ↑ → f m ↑
  -- ↑-downwards-closed = {!!}

  ↑<↓ : ∀ {A} {f : ℕ → A ⊎ Unit} {x m n} →
        Increasing f → (f m) ↑ → (f n) ↓ x → m < n
  ↑<↓ {A} {f} {x} {m} {n} inc fm↑ fn↓x with (≤⊎> n m)
  ... | inr m<n = m<n
  ... | inl n≤m = Cubical.Data.Empty.rec (inl≢inr (inl x ≡⟨ sym fn↓x ⟩ f n ≡⟨ ↑-downwards-closed inc n≤m fm↑ ⟩ inr tt ∎))

  ≰→≥ : ∀ {m n} → (m ≤ n → ⊥) → n ≤ m
  ≰→≥ p = ≤-trans (≤-suc ≤-refl) (≰→> p)

  total : ∀ m n → (m ≤ n) ⊎ (n ≤ m)
  total m n = Cubical.Data.Sum.map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→≥ (m ≤? n)

  cancel-inl : {A : Set} {B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inl x) (inl y) → x ≡ y
  cancel-inl {A} {B} {x = x} = λ p i → case p i of λ {(inl y) → const y x ; (inr y) → idfun A x}

  cancel-inr : {A : Set} {B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inr x) (inr y) → x ≡ y
  cancel-inr {A} {B} {x = x} = λ p i → case p i of λ { (inr y) → const y x ; (inl y) → idfun B x }

  ↓-step : ∀ {A : Set} {f} {x : A} {n} →
           Increasing f → f n ↓ x → f (suc n) ↓ x
  ↓-step {f = f} {x} {n} inc fn↓x = step'' (inc n)
    module ↓ where
    step'' : LE (f n) (f (suc n)) → f (suc n) ↓ x
    step'' (inl fn≡f1+n) =
      f (suc n)  ≡⟨ sym fn≡f1+n ⟩
      f n        ≡⟨ fn↓x ⟩
      inl x     ∎
    step'' (inr (fn↑ , _)) =
      Cubical.Data.Empty.rec (inl≢inr (inl x ≡⟨ sym fn↓x ⟩ f n ≡⟨ fn↑ ⟩ inr tt ∎))

  ↓-upwards-closed :
    ∀ {A} {f : ℕ → A ⊎ Unit} {m n x} →
    Increasing f → m ≤ n → f m ↓ x → f n ↓ x
  ↓-upwards-closed {A} {f} {x = x} inc (k , p) = ↓-upwards-closed-helper inc k p
    where
      ↓-upwards-closed-helper :
        ∀ {A} {f : ℕ → A ⊎ Unit} {m n x} →
        Increasing f → (k : ℕ) → (p : k + m ≡ n) → f m ↓ x → f n ↓ x
      ↓-upwards-closed-helper {A} {f} {x = x} _ 0 p = subst (λ a → f a ↓ x) p
      ↓-upwards-closed-helper {A} {f} {x = x} inc (suc n) p = subst (λ a → f a ↓ x) p ∘ ↓-step inc ∘ ↓-upwards-closed-helper inc n refl

  termination-value-unique :
    ∀ {A : Set} (x : Seq A) {y z} → x ↓seq y → x ↓seq z → y ≡ z
  termination-value-unique (f , inc) {y} {z} (m , fm↓y) (n , fn↓z)
    with total m n
  ... | inl m≤n = cancel-inl (inl y ≡⟨ sym (↓-upwards-closed inc m≤n fm↓y) ⟩  f n ≡⟨ fn↓z ⟩ inl z ∎)
  ... | inr n≤m = cancel-inl (inl y ≡⟨ sym fm↓y ⟩ f m ≡⟨ ↓-upwards-closed inc n≤m fn↓z ⟩ inl z ∎)

  ⇓→⇓′ : ∀ {A} x {y : A} → x ↓seq y → x ↓′ y
  ⇓→⇓′ x@(f , inc) = uncurry find-min
    where
      open import Cubical.Data.Nat.Order
      find-min : ∀ {y} m → f m ≡ inl y → x ↓′ y
      find-min 0 f0↓y = 0 , (f0↓y , (λ _ _ → zero-≤))
      find-min {y} (suc m) f-1+m↓y with inspect (f m)
      ... | (inr tt , fm↑) = (suc m) , (f-1+m↓y , 1+m-is-min)
        where
          1+m-is-min : ∀ n → (f n ≡ inr tt → ⊥) → m < n
          1+m-is-min n ¬fn↑ with inspect (f n)
          ... | (inr tt , fn↑) = Cubical.Data.Empty.elim (¬fn↑ fn↑)
          ... | (inl _ , fn↓) = ↑<↓ inc fm↑ fn↓
      ... | (inl y' , fm↓y') =
        let temp = find-min m fm↓y' in
        temp .fst , with-other-value (proj₁ (temp .snd)) , proj₂ (temp .snd)
        where
          with-other-value : ∀ {n} → f n ↓ y' → f n ↓ y
          with-other-value = subst (_ ↓_) (termination-value-unique x (_ , fm↓y') (_ , f-1+m↓y))

  ↓⇔∥↓∥ : ∀ {A} → isSet A → ∀ x {y : A} → (x ↓seq y → ∥ x ↓seq y ∥) × (∥ x ↓seq y ∥ → x ↓seq y)
  ↓⇔∥↓∥ A-set x {y} =
    (∣_∣) ,
    ⇓′→⇓ x ∘ Cubical.HITs.PropositionalTruncation.rec (⇓′-propositional A-set x {y = y}) (⇓→⇓′ x)

  Maybe→⊥-mono : ∀ {A : Type₀} {x y : A ⊎ Unit} → LE x y → (Maybe→⊥ x) ⊑ (Maybe→⊥ y)
  Maybe→⊥-mono {x = x} {y} (inl p) = subst (λ a → Maybe→⊥ x ⊑ Maybe→⊥ a) p (⊑-refl (Maybe→⊥ x))
  Maybe→⊥-mono {x = x} {y} (inr p) = subst (λ a → Maybe→⊥ a ⊑ Maybe→⊥ y) (sym (proj₁ p)) (never⊑ (Maybe→⊥ y))

  Seq→Inc-seq : ∀ {A} → Seq A → Increasing-sequence A
  Seq→Inc-seq (f , inc) = Maybe→⊥ ∘ f , Maybe→⊥-mono ∘ inc

  -- Turns increasing sequences of potential values into partial values.

  Seq→⊥ : ∀ {A} → Seq A → < A >⊥
  Seq→⊥ = ⊔ ∘ Seq→Inc-seq

  -- If every element in one increasing sequence is bounded by some
  -- element in another, then the least upper bound of the first
  -- sequence is bounded by the least upper bound of the second one.
  private
    ⊑→⨆⊑⨆ : ∀ {A : Set} {s₁ s₂ : Increasing-sequence A} {f : ℕ → ℕ} →
            (∀ n → fst s₁ n ⊑ fst s₂ (f n)) → ⊔ s₁ ⊑ ⊔ s₂
    ⊑→⨆⊑⨆ {s₁} {s₂} {f} s₁⊑s₂ =
      least-upper-bound _ _ λ n → ⊑-trans (s₁⊑s₂ n) (upper-bound _ _)

  -- A variant of the previous lemma.

  private
    ∃⊑→⨆⊑⨆ : ∀ {A : Set} {s₁ s₂ : Increasing-sequence A} →
             (∀ m → Σ[ n ∈ ℕ ] (fst s₁  m ⊑ fst s₂ n)) → ⊔ s₁ ⊑ ⊔ s₂
    ∃⊑→⨆⊑⨆ s₁⊑s₂ = ⊑→⨆⊑⨆ (snd ∘ s₁⊑s₂)

  Seq→⊥-mono : ∀ {A : Set} → isSet A → ∀ (x y : Seq A) → x ⊑seq y → Seq→⊥ x ⊑ Seq→⊥ y
  Seq→⊥-mono A-set x@(f , _) y@(g , _) x⊑y =
    ∃⊑→⨆⊑⨆ inc
    where
      inc : ∀ m → Σ[ n ∈ ℕ ] (Maybe→⊥ (f m) ⊑ Maybe→⊥ (g n))
      inc m with inspect (f m)
      ... | (inr tt , p) = 0 , subst (λ x₁ → Maybe→⊥ x₁ ⊑ Maybe→⊥ (g 0)) (sym p) (never⊑ (Maybe→⊥ (g 0))) -- never⊑ (Maybe→⊥ (g 0))
      ... | (inl r , p) = fst y↓z , subst (λ a → Maybe→⊥ (f m) ⊑ Maybe→⊥ a) (sym (snd y↓z))
                                    (subst (λ a → Maybe→⊥ a ⊑ η r) (sym p) (⊑-refl (η r)))
        where
          y↓z : y ↓seq r
          y↓z = let temp = x⊑y r in let temp' = proj₂ (↓⇔∥↓∥ A-set y) ∘ temp in temp' ∣ m , p ∣

  Seq→⊥-≈→≡ : ∀ {A} → isSet A → ∀ (x y : Seq A) → x ∼seq y → Seq→⊥ x ≡ Seq→⊥ y
  Seq→⊥-≈→≡ A-set x y (p , q) = α (Seq→⊥-mono A-set x y p) (Seq→⊥-mono A-set y x q)

  recc :
    ∀ {A B : Set} {R : A → A → Set} →
    (f : A → B) →
    (∀ x y → R x y → f x ≡ f y) →
    isSet B →
    A / R → B
  recc {A} {B} {R} f feq B-set ar =
    Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

  Seq/∼→⊥ : ∀ {A} → isSet A → (Seq A / _∼seq_) → < A >⊥
  Seq/∼→⊥ {A} A-set = recc Seq→⊥ (λ x y → Seq→⊥-≈→≡ A-set x y) ⊥-isSet

  private -- useful property
    postulate -- TODO
      η⊑⊔ : ∀ {A : Set} s q (r : A) → η r ⊑ ⊔ (s , q) → ∥ Σ[ n ∈ ℕ ] η r ⊑ s n ∥

  ⊑-refl-constr : ∀ {A : Set} {x y : < A >⊥} → x ≡ y → x ⊑ y
  ⊑-refl-constr {x = x} p = transport (λ i → x ⊑ p i) (⊑-refl x)

  -- weakly effective?
  Seq→⊥-isInjective : ∀ {A} → (A-set : isSet A) → (s t : Seq A) → Seq→⊥ s ≡ Seq→⊥ t → s ∼seq t
  Seq→⊥-isInjective {A} A-set s t x =
    lemma s t (⊑-refl-constr x) ,
    lemma t s (⊑-refl-constr (sym x))
    where
      postulate
        ⇓≃now⊑ : (x : Seq A) {y : A} → Iso (x ↓seq y) (η y ⊑ Seq→⊥ x)
    
      lemma : (x y : Seq A) → Seq→⊥ x ⊑ Seq→⊥ y → (∀ a → ∥ x ↓seq a ∥ → ∥ y ↓seq a ∥)
      lemma x y p a q =
        let temp'1 : ∥ x ↓seq a ∥
            temp'1 = q in
        let temp'2 : x ↓seq a
            temp'2 = proj₂ (↓⇔∥↓∥ A-set x) temp'1 in
        let temp'3 : η a ⊑ Seq→⊥ x
            temp'3 = Iso.fun (⇓≃now⊑ x) temp'2 in
        let temp'4 : η a ⊑ Seq→⊥ y
            temp'4 = ⊑-trans temp'3 p in
        let temp'5 : y ↓seq a
            temp'5 = Iso.inv (⇓≃now⊑ y) temp'4 in
        proj₁ (↓⇔∥↓∥ A-set y) temp'5

      -- Maybe→⊥-isEmbedding : isEmbedding Maybe→⊥
      -- Maybe→⊥-isEmbedding = {!!}

      -- Maybe→⊥-isInjective : ∀ (s t : A ⊎ Unit) → (Maybe→⊥ s ≡ Maybe→⊥ t) ≡ (s ≡ t)
      -- Maybe→⊥-isInjective s t = isEmbedding→Injection Maybe→⊥ {!!} tt

      -- sfad-helper :
      --   ∀ (t : Seq A) a
      --   → ∥ (Σ[ n ∈ ℕ ] η a ⊑ Maybe→⊥ (fst t n)) ∥
      --   ≡ ∥ (Σ[ n ∈ ℕ ] fst t n ≡ inl a) ∥
      -- sfad-helper t a =
      --   ∥ (Σ[ n ∈ ℕ ] η a ⊑ Maybe→⊥ (fst t n)) ∥
      --      ≡⟨ cong (λ k → ∥ (Σ[ n ∈ ℕ ] k n) ∥) (funExt λ n → isoToPath (η⊑x-x≡η-Iso (Maybe→⊥ (fst t n)) a)) ⟩
      --   ∥ (Σ[ n ∈ ℕ ] Maybe→⊥ (fst t n) ≡ η a) ∥
      --     ≡⟨ refl ⟩
      --   ∥ (Σ[ n ∈ ℕ ] Maybe→⊥ (fst t n) ≡ Maybe→⊥ (inl a)) ∥
      --     ≡⟨ cong (λ k → ∥ Σ[ n ∈ ℕ ] k n ∥) (funExt λ n → Maybe→⊥-isInjective (fst t n) (inl a)) ⟩
      --   ∥ (Σ[ n ∈ ℕ ] fst t n ≡ inl a) ∥ ∎

      -- sfad : ∀ s t → Seq→⊥ s ≡ Seq→⊥ t → (a : A) → ∥ s ↓seq a ∥ → ∥ t ↓seq a ∥
      -- sfad s t x a q =
      --   let (n , k) = proj₂ (↓⇔∥↓∥ A-set s) q in
      --   -- -- use Propositional truncation elim ?
      --   transport
      --     (sfad-helper t a)
      --     (η⊑⊔ (Maybe→⊥ ∘ fst t) (Maybe→⊥-mono ∘ snd t) a (Iso.inv (η⊑x-x≡η-Iso (Seq→⊥ t) a) (subst (λ x₁ → x₁ ≡ η a) x (Iso.fun (η⊑x-x≡η-Iso (Seq→⊥ s) a) (subst (λ x₂ → Maybe→⊥ x₂ ⊑ ⊔ ((Maybe→⊥ ∘ fst s) , (Maybe→⊥-mono ∘ snd s))) k (upper-bound ((Maybe→⊥ ∘ fst s) , (Maybe→⊥-mono ∘ snd s)) n))))))

  Seq/∼→⊥-isInjective : ∀ {A} → (A-set : isSet A) → isInjective (Seq/∼→⊥ A-set)
  Seq/∼→⊥-isInjective {A} A-set {x} {y} =
    elimProp
      {B = λ x → Seq/∼→⊥ A-set x ≡ Seq/∼→⊥ A-set y → x ≡ y}
      (λ x → isPropΠ λ _ x' y' → squash/ x y x' y') 
      (λ x →
        elimProp
          {B = λ y → Seq→⊥ x ≡ Seq/∼→⊥ A-set y → [ x ] ≡ y}
          (λ y → isPropΠ λ _ x' y' → squash/ [ x ] y x' y')
          (λ y → eq/ x y ∘ (Seq→⊥-isInjective A-set x y))
          y)
      x

  Seq/∼→⊥-isEmbedding : ∀ {A} → (A-set : isSet A) → isEmbedding (Seq/∼→⊥ A-set)
  Seq/∼→⊥-isEmbedding {A} A-set = injEmbedding squash/ ⊥-isSet (Seq/∼→⊥-isInjective A-set)

-- Axiom-of-countable-choice : (b : Level) → Set (lsuc b)
-- Axiom-of-countable-choice b =
--   {B : ℕ → Set b} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

  countable-choice : {!!}
  countable-choice = {!!}

  Seq→⊥-isSurjection : ∀ {A} → countable-choice → isSurjection (Seq→⊥ {A})
  Seq→⊥-isSurjection = {!!}
  
  Seq/∼→⊥-isSurjection : ∀ {A} → (A-set : isSet A) → isSurjection (Seq/∼→⊥ A-set)
  Seq/∼→⊥-isSurjection = {!!}

  seq/∼→⊥-isEquiv : ∀ {A} → (A-set : isSet A) → isEquiv (Seq/∼→⊥ A-set)
  seq/∼→⊥-isEquiv A-set = isEmbedding×isSurjection→isEquiv ((Seq/∼→⊥-isEmbedding A-set) , (Seq/∼→⊥-isSurjection A-set)) 

  ⊥-⊥-Iso : ∀ {A} → isSet A → (Seq A / _∼seq_) ≃ < A >⊥
  ⊥-⊥-Iso A-set = {!!} , (seq/∼→⊥-isEquiv A-set)

-- -------------------------------------------------------------------------
-- -- Alternative definition of partiality monad using HITs and not HIITs --
-- -------------------------------------------------------------------------

-- -- Another Partiality monad (HIT)
-- -- Paper: Quotienting the Delay Monad by WeakBisimilarity (https://niccoloveltri.github.io/mscs_final.pdf)
-- -- Authors: James Chapman, Tarmo Uustalu and Niccoló Veltri
-- -- Formalization: http://cs.ioc.ee/~niccolo/delay/
-- mutual
--   -- free countably-complete join semilattice
--   data P∞ (X : Type₀) : Type₀ where
--      η : X → P∞ X
--      ⊥P∞ : P∞ X
--      ⋁ : (ℕ → P∞ X) → P∞ X

--      v-sym : ∀ {x y} → (x v y) ≡ (y v x)
--      v-assoc : ∀ {x y z} → x v (y v z) ≡ (x v y) v z
--      v-now : ∀ {x} → x v x ≡ x
--      v-never : ∀ {x} → x v ⊥P∞ ≡ x
--      v-⋁ : ∀ {s : ℕ → P∞ X} (n : ℕ) → (s n) v (⋁ s) ≡ ⋁ s
--      v-⋁' : ∀ {s : ℕ → P∞ X} {x} → ((⋁ s) v x) ≡ (⋁ λ n → s n v x)

--      P∞-set : isSet (P∞ X)

--      -- f1 : ?

--   _v_ : ∀ {X} (x y : P∞ X) → P∞ X
--   x v y = ⋁ (λ {0 → x ; (suc n) → y})

--   _≤P∞_ : ∀ {X} (x y : P∞ X) → Type₀
--   x ≤P∞ y = (x v y) ≡ y

-- S' = P∞ Unit

-- Pₛ-Container : Container ℓ-zero
-- Pₛ-Container = S' , λ x → x ≡ η tt -- (η tt ≡ ⊤)

-- Pₛ-M-type : Set -- What is this??
-- Pₛ-M-type = M Pₛ-Container

-- Pₛ : Type₀ → Type₀
-- Pₛ = P₀ Pₛ-Container

-- -- if S is the free ωcppo on 1, then Pₛ X is the free ωcppo on X

-- h : ∀ {X} → X → Pₛ X
-- h x = (η tt) , (λ _ → x)
