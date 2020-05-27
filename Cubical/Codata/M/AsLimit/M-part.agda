{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.M-part where

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Codata.M

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

-- T-IxCont : IxCont Unit
-- T-IxCont = (λ x → Unit ⊎ Unit) , λ {_ (inl _) _ → ⊥ ; _ (inr _) _ → ℕ}

-- T0 = M T-IxCont tt

-- leaf : T0
-- leaf = inM tt (inl tt , λ _ ())

-- node : (ℕ → T0) → T0
-- node f = inM tt (inr tt , λ _ → f)

-- ∼-IxCont : IxCont (T0 × T0)
-- ∼-IxCont = (λ {(x , y) → ((x ≡ leaf) × (y ≡ leaf))
--                         ⊎ ((Σ[ fg ∈ (ℕ → T0) × (ℕ → T0)] (x ≡ node (proj₁ fg)) × (y ≡ node (proj₂ fg))) ⊎ (Σ[ fg ∈ (ℕ → T0) × (ℕ → ℕ)] (x ≡ node (proj₁ fg)) × (y ≡ node (proj₁ fg ∘ proj₂ fg)) × isEquiv (proj₂ fg)))})
--          , λ {(x , y) (inl _) _ → ⊥
--              ;(x , y) (inr (inl (fg , _))) (v , w) → Σ[ n ∈ ℕ ] (proj₁ fg n ≡ v) × (proj₂ fg n ≡ w)
--              ;(x , y) (inr (inr _)) _ → ⊥}

-- _∼_ : T0 → T0 → Type₀
-- x ∼ y  = M (∼-IxCont) (x , y)

-- ∼leaf : leaf ∼ leaf
-- ∼leaf = inM (leaf , leaf) ((inl (refl , refl)) , λ _ ())

-- ∼node : {f g : ℕ → T0} → (∀ n → f n ∼ g n) → node f ∼ node g
-- ∼node {f} {g} p =
--   inM (node f , node g) ((inr (inl ((f , g) , (refl , refl)))) ,
--   λ {(v , w) (n , x , y) → transport (λ i → x i ∼ y i) (p n)})

-- perm : (f : ℕ → T0) → (g : ℕ → ℕ) → isEquiv g → node f ∼ node (f ∘ g)
-- perm f g x = inM (node f , node (f ∘ g)) ((inr (inr ((f , g) , (refl , refl , x)))) , λ _ ())


-- T : Set
-- T = M ((λ x → Unit ⊎ (Unit ⊎ {!!})) ,
--   λ {_ (inl _) _ → ⊥
--     ;_ (inr (inl _)) _ → ℕ
--     ;_ (inr (inr _)) _ → {!!}}) tt

-- leaf' : T
-- leaf' = inM tt (inl tt , λ _ ())

-- node' : (ℕ → T) → T
-- node' f = inM tt (inr (inl tt) , λ _ → f)

-- perm' : (f : ℕ → T0) → (g : ℕ → ℕ) → isEquiv g → node f ≡ node (f ∘ g)
-- perm' f g e = {!!} -- inM tt (inr (inr ?) , ?)


-- record Mii {ℓ} {X : Type ℓ} (C : IxCont X) (x : X) : Type ℓ where
--   coinductive
--   field
--     head : C .fst x
--     tails : ∀ y → C .snd x head y → M C y


-- data _∼_ : T0 → T0 → Set where
--   ∼leaf : leaf ∼ leaf
--   ∼node : {f g : ℕ → T0} → (∀ n → f n ∼ g n) → node f ∼ node g
--   perm : (g : ℕ → T0) → (f : ℕ → ℕ) → isEquiv f → node g ∼ node (g ∘ f)

-----------------------------
-- M-type partiality monad --
-----------------------------

mutual
  -- data <_>⊥ {ℓ} (A : Type ℓ) : Type ℓ where
  --   never  : < A >⊥
  --   η      : A → < A >⊥
  --   ⊔      : Increasing-sequence A → < A >⊥
  --   α      : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
  --   ⊥-isSet : isSet (< A >⊥)
  
  data ⊥' {ℓ} : Type ℓ where

  ⊥-IxCont : ∀ {ℓ} (A : Type ℓ) → IxCont {ℓ} (Lift Unit)
  ⊥-IxCont A = (λ _ → (Unit ⊎ (A ⊎ (Increasing-sequence A ⊎ (< A >⊥ × < A >⊥ ⊎ ((∀ {x} {y} → x ⊑ y → y ⊑ x → x ≡ y) ⊎ isSet (< A >⊥))))))) 
              , λ {_ _ _ → ⊥'}
                  
  <_>⊥ : ∀ {ℓ} (A : Type ℓ) → Type ℓ
  <_>⊥ A = M (⊥-IxCont A) (lift tt)
    
  order-cont : {ℓ : Level} (A : Type ℓ) → IxCont (< A >⊥ × < A >⊥)
  order-cont A = (λ {(x , y) → (x ≡ y) ⊎ (< A >⊥ ⊎ (x ≡ never))})
               , (λ {(x , y) (inl _) _ → ⊥'
                    ;(x , y) (inr (inl z)) (w , v) → ((x ≡ w) × (z ≡ v)) ⊎ ((z ≡ w) × (y ≡ v))
                    ;(x , y) (inr (inr _)) _ → ⊥'
                    })

  _⊑_ : {ℓ : Level} {A : Type ℓ} (_ _ : < A >⊥) → Type ℓ
  _⊑_ {A = A} x y = M (order-cont A) (x , y)

  Increasing-sequence : ∀ {ℓ} → Type ℓ → Type ℓ
  Increasing-sequence A = Σ[ f ∈ (ℕ → < A >⊥) ] ((n : ℕ) → f n ⊑ f (suc n))

  abstract
    never : ∀ {ℓ} {A : Type ℓ} → < A >⊥
    never = inM (lift tt) (inl tt , λ _ ())

    η : ∀ {ℓ} {A : Type ℓ} → A → < A >⊥
    η a = inM (lift tt) (inr (inl a) , λ _ ())

    ⊔ : ∀ {ℓ} {A : Type ℓ} → Increasing-sequence A → < A >⊥
    ⊔ a = inM (lift tt) (inr (inr (inl a)) , λ _ ())

    α : ∀ {ℓ} {A : Type ℓ} → ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
    α p q i = {!!}
    

  order-refl : ∀ {ℓ} {A : Type ℓ} (x : < A >⊥) → x ⊑ x
  order-refl x = inM (x , x) (inl refl , λ _ ())
  
  order-trans : ∀ {ℓ} {A : Type ℓ} (x y z : < A >⊥) → x ⊑ y → y ⊑ z → x ⊑ z
  order-trans x y z p q = inM (x , z) ((inr (inl y)) ,
      λ {(w , v) (inl (kx , ky)) → transport (λ i → kx i ⊑ ky i) p
        ;(w , v) (inr (kx , ky)) → transport (λ i → kx i ⊑ ky i) q})
  
  order-never : ∀ {ℓ} {A : Type ℓ} (x : < A >⊥) → never ⊑ x
  order-never x = inM (never , x) (inr (inr refl) , λ _ ())


  -- (inl refl , λ ())

  -- order-trans : ∀ {ℓ} {A : Type ℓ} (x y z : part-mona A) → order-m A x y → order-m A y z → order-m A x z
  -- order-trans x y z p q = in-fun (inr z , λ {(inl _) → {!!}})

  -- data _⊑_ {ℓ} {A : Set ℓ} : < A >⊥ → < A >⊥ → Set ℓ where
  --   ⊑-refl            : ∀ x → x ⊑ x
  --   ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  --   never⊑            : ∀ x → never ⊑ x
  --   upper-bound       : ∀ s → Is-upper-bound s (⊔ s)
  --   least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⊔ s ⊑ ub
  --   ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

  -- order-cont : {ℓ : Level} (A : Type ℓ) → Container ℓ
  -- order-cont A = (part-mona A ⊎
  --                 ((part-mona A × part-mona A × part-mona A) ⊎
  --                 part-mona A))
  --              , (λ {(inl _) → ⊥'
  --                   ;(inr (inl _)) → Lift (Unit ⊎ Unit)
  --                   ;(inr (inr _)) → ⊥'})
               
  -- -- Σ[ _ : part ] 0 = refl
  -- -- Σ[ x y z : part ] (1 + 1) = trans

  -- order-m : {ℓ : Level} (A : Type ℓ) → Type ℓ
  -- order-m A = M (order-cont A)

  -- order-refl : ∀ {ℓ} {A : Type ℓ} (x : part-mona A) → order-m A
  -- order-refl x = in-fun (inl x , (λ ()))

  -- order-trans : ∀ {ℓ} {A : Type ℓ} (x y z : part-mona A) → order-m A → order-m A → order-m A
  -- order-trans x y z p q = in-fun (inr (inl (x , y , z)) , λ {(lift (inl _)) → p ; (lift (inr _)) → q})
    
  -- order-never : ∀ {ℓ} {A : Type ℓ} (x : part-mona A) → order-m A
  -- order-never x = in-fun (inr (inr x) , (λ ()))

  -- data _⊑_ {ℓ} {A : Set ℓ} : < A >⊥ → < A >⊥ → Set ℓ where
  --   ⊑-refl            : ∀ x → x ⊑ x
  --   ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  --   never⊑            : ∀ x → never ⊑ x
  --   upper-bound       : ∀ s → Is-upper-bound s (⊔ s)
  --   least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⊔ s ⊑ ub
  --   ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)
