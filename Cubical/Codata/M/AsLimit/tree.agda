{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.tree where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Codata.M.AsLimit.Container
-- open import Cubical.Codata.M.AsLimit.itree
open import Cubical.Codata.M.AsLimit.M


-- record temp {A : SEt} {B : Set} : Set where


-- temp = λ (A : Type₀) → M ((A ⊎ Unit) × A , λ {(inl _ , _) → ⊥ ; (inr _ , _) → Unit})
data ⊥₁ : Type₁ where

record temp {A : Set} {B : Set} : Set₁ where
  coinductive
  field
    hd : Type₀
    hd' : hd -> Type₀
    hd'' : (x : hd) → hd' x -> temp {A} {B}

temp-construction = M ((Σ[ hd ∈ Type₀ ] (Σ[ hd' ∈ (hd → Type₀) ] Unit)) , λ {(hd , hd' , _) → Lift (Σ[ x ∈ hd ] hd' x)})

hd-con : temp-construction → Type₀
hd-con x = out-fun x .fst .fst

hd-con' : (x : temp-construction) → hd-con x → Type₀
hd-con' x y = out-fun x .fst .snd .fst y

hd-con'' : (x : temp-construction) → (k : hd-con x) → hd-con' x k → temp-construction
hd-con'' x y z = out-fun x .snd (lift (y , z))


afds : Unit ⊎ Unit → Set
afds (inl tt) = ℕ
afds (inr tt) = Unit

afds' : (Unit ⊎ Unit) → (Unit ⊎ Unit) → Set
afds' x = _⊎_ (afds x) ∘ afds

uncurry'
  : ∀{ℓ ℓ′ ℓ″} {A : Type ℓ} {B : Type ℓ′} {C : A → B → Type ℓ″}
  → ((x : A) → (y : B) → C x y)
  → (p : A × B) → C (proj₁ p) (proj₂ p)
uncurry' f (x , y) = f x y

asfd = M ((Unit ⊎ Unit) × (Unit ⊎ Unit) , uncurry' afds')

asfd'' = M (Unit ⊎ Unit , afds)

as : asfd'' → Unit ⊎ Unit
as x = out-fun x .fst

as' : (x : asfd'') → afds (as x) → asfd''
as' x y = out-fun x .snd y

as''₁ : asfd → Unit ⊎ Unit
as''₁ x = proj₁ (out-fun x .fst)

as''₂ : asfd → Unit ⊎ Unit
as''₂ x = proj₂ (out-fun x .fst)

ksad : forall (x : asfd) -> (fst (out-fun x)) ≡ ((as''₁ x) , (as''₂ x))
ksad (a , b) with fst (a (suc 0))
... | (x , y) = refl

as'''₁ : (x : asfd) → afds (as''₁ x) → asfd
as'''₁ x@(a , b) y =
  out-fun x .snd (subst (uncurry' afds') (sym (ksad x)) (inl y))
  
as'''₂ : (x : asfd) → afds (as''₂ x) → asfd
as'''₂ x@(a , b) y =
  out-fun x .snd (subst (uncurry' afds') (sym (ksad x)) (inr y))

-- hd'temp : ∀ {A B} → temp {A} {B} → ((A → temp {A} {B}) × B)
-- hd'temp x = {!!}

-- ret : ∀ {A} → A × A → temp A 
-- ret x = in-fun ((inl x , {!!}) , λ ())

-- hd : ∀ {A} → temp A → A
-- hd x = proj₂ (out-fun x .fst)

-- Bottom element raised
-- data ⊥₁ : Type₁ where

-- TREES
tree-S : Type₀ → Container (ℓ-zero)
tree-S X = (Unit ⊎ Unit) , (λ { (inl _) -> ⊥ ; (inr _) -> X } )

tree : Type₀ → Type₀
tree X = M (tree-S X)

tree-leaf : ∀ {X} → tree X
tree-leaf = in-fun (inl tt , λ ())

tree-node : ∀ {X} -> (X -> tree X) -> tree X
tree-node {X = X} k = in-fun (inr tt , k)

mutual
  data T (A : Set) : Set₁ where
    T-leaf : T A
    T-node : (A → ∞T A) → T A

  record ∞T (A : Set) : Set₁ where
    coinductive
    field
      force : T A

open ∞T

module lift-props where
  private
    variable
      ℓ : Level
      S : Container ℓ
      x : M S

  lift-x : {ℓ : Level} {S : Container ℓ} → (n : ℕ) → (x : M S) → Wₙ S n
  lift-x 0 x = lift tt
  lift-x (suc n) x = x .fst (suc n) .fst , λ x' → lift-x n x
    
  lift-π : {ℓ : Level} {S : Container ℓ} → (n : ℕ) → (x : M S) → πₙ S (lift-x (suc n) x) ≡ lift-x n x
  lift-π 0 x = refl
  lift-π (suc n) x i = {!!} , λ x' → lift-π n x i 

-- hte : ∀ X → Iso (tree X) (T X)
-- hte X = iso into outof {!!} {!!} -- into-outof outof-into
--   where
--     mutual
--       into : tree X → T X
--       into = M-coinduction-const (T X) Pinto

--       Pinto : P₀ (tree-S X) (tree X) → T X
--       Pinto (inl tt , _) = T-leaf
--       Pinto (inr tt , f) = T-node (∞into ∘ f)

--       ∞into : tree X → ∞T X
--       force (∞into x) = into x

--     outof : T X → tree X
--     outof T-leaf = tree-leaf
--     outof (T-node f) = lift-to-M lift-x lift-π (T-node f)
--       where
--         lift-x : (n : ℕ) (t : T X) → Wₙ (tree-S X) n
--         lift-x 0 t = lift tt
--         lift-x (suc n) (T-leaf) = inl tt , λ ()
--         lift-x (suc n) (T-node f) = inr tt , λ x → lift-x n (force (f x))

--         lift-π : (n : ℕ) (t : T X) → πₙ (tree-S X) (lift-x (suc n) t) ≡ lift-x n t
--         lift-π 0 t = refl
--         lift-π (suc n) (T-leaf) i = inl tt , (isContr→isProp isContr⊥→A (snd (πₙ (tree-S X) (lift-x (suc (suc n)) T-leaf))) λ ()) i
--         lift-π (suc n) (T-node f) i = (inr tt) , (λ x → lift-π n (force (f x)) i)

--     etarh : ∀ b → into (in-fun (inr tt , b)) ≡ T-node (∞into ∘ b)
--     etarh b = cong Pinto (out-inverse-in-x (inr tt , b))

--     outof-into : ∀ b → outof (into b) ≡ b
--     outof-into = M-coinduction (λ x → outof (into x) ≡ x)
--       λ {(inl tt , b) → cong in-fun (ΣPathP ( refl , isContr→isProp isContr⊥→A (λ ()) b))
--         ; (inr r , b) →
--           outof (into (in-fun (inr r , b)))
--             ≡⟨ cong outof (cong Pinto (out-inverse-in-x (inr tt , b))) ⟩
--           outof (T-node (∞into ∘ b))
--             ≡⟨ {!!} ⟩
--           in-fun (inr r , b) ∎}

    -- into-outof : ∀ b → into (outof b) ≡ b
    -- into-outof T-leaf = refl
    -- into-outof (T-node f) =
    --   into (outof (T-node f))
    --     ≡⟨ refl ⟩
    --   T-node {!!}
    --     ≡⟨ {!!} ⟩
    --   T-node f ∎

-- (λ x →
--        ∞into
--        ((λ n →
--            fst
--            (Iso.fun
--             (Σ-ap-iso
--              (Cubical.Foundations.Transport.pathToIso
--               (λ i →
--                  (n₁ : ℕ) →
--                  funExt
--                  (λ n₂ i₁ →
--                     snd (tree-S X)
--                     (Cubical.Codata.M.AsLimit.M.Base.α-iso-step-5-Iso-helper0
--                      (fst (tree-S X)) (snd (tree-S X))
--                      (λ n₃ →
--                         Cubical.Codata.M.AsLimit.tree.lift-x f (suc n₃) (T-node f) .fst)
--                      (λ n₃ i₂ →
--                         Cubical.Codata.M.AsLimit.tree.lift-π f (suc n₃) (T-node f) i₂ .fst)
--                      n₂ i₁) →
--                     Wₙ (fst (tree-S X) , snd (tree-S X)) n₂)
--                  i n₁))
--              (λ u →
--                 Cubical.Foundations.Transport.pathToIso
--                 (λ i →
--                    (n₁ : ℕ) →
--                    funExt
--                    (λ n₂ →
--                       isoToPath
--                       (Cubical.Codata.M.AsLimit.M.Base.α-iso-step-5-Iso-helper1-Iso
--                        (fst (tree-S X)) (snd (tree-S X))
--                        (λ n₃ →
--                           Cubical.Codata.M.AsLimit.tree.lift-x f (suc n₃) (T-node f) .fst)
--                        (λ n₃ i₁ →
--                           Cubical.Codata.M.AsLimit.tree.lift-π f (suc n₃) (T-node f) i₁ .fst)
--                        u n₂))
--                    i n₁)))
--             ((λ n₁ →
--                 Cubical.Codata.M.AsLimit.tree.lift-x f (suc n₁) (T-node f) .snd)
--              ,
--              (λ n₁ i →
--                 Cubical.Codata.M.AsLimit.tree.lift-π f (suc n₁) (T-node f) i
--                 .snd)))
--            n x)
--         ,
--         (λ n i →
--            snd
--            (Iso.fun
--             (Σ-ap-iso
--              (Cubical.Foundations.Transport.pathToIso
--               (λ i₁ →
--                  (n₁ : ℕ) →
--                  funExt
--                  (λ n₂ i₂ →
--                     snd (tree-S X)
--                     (Cubical.Codata.M.AsLimit.M.Base.α-iso-step-5-Iso-helper0
--                      (fst (tree-S X)) (snd (tree-S X))
--                      (λ n₃ →
--                         Cubical.Codata.M.AsLimit.tree.lift-x f (suc n₃) (T-node f) .fst)
--                      (λ n₃ i₃ →
--                         Cubical.Codata.M.AsLimit.tree.lift-π f (suc n₃) (T-node f) i₃ .fst)
--                      n₂ i₂) →
--                     Wₙ (fst (tree-S X) , snd (tree-S X)) n₂)
--                  i₁ n₁))
--              (λ u →
--                 Cubical.Foundations.Transport.pathToIso
--                 (λ i₁ →
--                    (n₁ : ℕ) →
--                    funExt
--                    (λ n₂ →
--                       isoToPath
--                       (Cubical.Codata.M.AsLimit.M.Base.α-iso-step-5-Iso-helper1-Iso
--                        (fst (tree-S X)) (snd (tree-S X))
--                        (λ n₃ →
--                           Cubical.Codata.M.AsLimit.tree.lift-x f (suc n₃) (T-node f) .fst)
--                        (λ n₃ i₂ →
--                           Cubical.Codata.M.AsLimit.tree.lift-π f (suc n₃) (T-node f) i₂ .fst)
--                        u n₂))
--                    i₁ n₁)))
--             ((λ n₁ →
--                 Cubical.Codata.M.AsLimit.tree.lift-x f (suc n₁) (T-node f) .snd)
--              ,
--              (λ n₁ i₁ →
--                 Cubical.Codata.M.AsLimit.tree.lift-π f (suc n₁) (T-node f) i₁
--                 .snd)))
--            n i x)))


-- data _∼tree_ {X} : (_ _ : tree X) → Type (ℓ-suc ℓ-zero) where
--   ∼leaf : tree-leaf ∼tree tree-leaf
--   ∼node :
--     ∀ (a b : X → tree X)
--     → (∀ x → a x ∼tree b x)
--     → tree-node a ∼tree tree-node b
--   ∼rel : (e : X → X) → isEquiv e → (f : X → tree X) → tree-node f ∼tree tree-node (f ∘ e)

-- adfs : Type₀ → Type₁
-- adfs X = tree X / _∼tree_

-- data TQ (A : Set) : Set₁ where
--   leaf : TQ A
--   node : (A → TQ A) → TQ A
--   mix : (e : A → A) → isEquiv e → (f : A → TQ A) → node f ≡ node (f ∘ e)
