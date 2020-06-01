{-# OPTIONS --cubical --guardedness #-}

module Cubical.Codata.M.AsLimit.Binary-tree where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat using (ℕ ; suc ; _+_ )
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper

open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; rec to ∥rec∥)

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

data b : Set where
  leaf : b
  node : (ℕ → b) → b

data _∼_ : (_ _ : b) → Set where
  ∼leaf : leaf ∼ leaf
  ∼node : ∀ {f g} → ((v : ℕ) → f v ∼ g v) → node f ∼ node g
  ∼perm : ∀ f → (g : (ℕ) → (ℕ)) → isEquiv g → node f ∼ node (f ∘ g)

mutual
  data T : Set where
    leaf : T
    node : (ℕ → ∞T) → T
    perm : ∀ f → (g : (ℕ) → (ℕ)) → isEquiv g → node f ≡ node (f ∘ g)
    T-isSet : isSet T

  record ∞T : Set where
    coinductive
    field
      force : T

open ∞T

mutual
  b→T : b → T
  b→T leaf = leaf
  b→T (node f) = node (b→∞T ∘ f)

  b→∞T : b → ∞T
  force (b→∞T b) = b→T b

mutual
  b→T-∼→≡ : ∀ {x y} → x ∼ y → b→T x ≡ b→T y
  b→T-∼→≡ (∼leaf) = refl {x = leaf}
  b→T-∼→≡ (∼node {f} {g} p) = cong {B = λ _ → T} node (funExt (b→∞T-∼→≡ ∘ p))
  b→T-∼→≡ (∼perm f g e) = perm (b→∞T ∘ f) g e

  b→∞T-∼→≡ : ∀ {x y} → x ∼ y → b→∞T x ≡ b→∞T y
  force (b→∞T-∼→≡ p i) = b→T-∼→≡ p i

recc :
  ∀ {A B : Set} {R : A → A → Set} →
  (f : A → B) →
  (∀ x y → R x y → f x ≡ f y) →
  isSet B →
  A / R → B
recc {A} {B} {R} f feq B-set ar =
  Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

b/∼→T : b / _∼_ → T
b/∼→T = recc b→T (λ _ _ → b→T-∼→≡) T-isSet

isInjective : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Type _
isInjective f = ∀{w x} → f w ≡ f x → w ≡ x

postulate
  node-is-embedding : ∀ {f g : ℕ -> ∞T} → Iso {ℓ = ℓ-zero} {ℓ' = ℓ-zero} (T.node f ≡ node g) (force ∘ f ≡ force ∘ g)

node≢leaf : {f : ℕ -> ∞T} -> T.node f ≡ leaf -> ⊥
node≢leaf x = subst (λ { T.leaf → T ; (T.node f) → ⊥ ; _ -> {!!} }) (sym x) (x i1)

b→T-injective : ∀ {x y} → b→T x ≡ b→T y → x ∼ y
b→T-injective {x = leaf} {y = leaf} p = ∼leaf
b→T-injective {x = node f} {y = leaf} p = rec (node≢leaf p)
b→T-injective {x = leaf} {y = node g} p = rec (node≢leaf (sym p))
b→T-injective {x = node f} {y = node g} p =
  let temp = Iso.fun node-is-embedding p in 
  ∼node (b→T-injective ∘ (funExt⁻ temp))

b/∼→T-injective : isInjective b/∼→T
b/∼→T-injective {x} {y} =
  elimProp
    {A = b}
    {R = _∼_}
    {B = λ x → b/∼→T x ≡ b/∼→T y → x ≡ y}
    (λ x → isPropΠ λ _ → squash/ x y)
    (λ x →
      elimProp
        {A = b}
        {R = _∼_}
        {B = λ y → b/∼→T [ x ] ≡ b/∼→T y → [ x ] ≡ y}
        (λ y → isPropΠ λ _ → squash/ [ x ] y)
        (λ y → eq/ x y ∘ b→T-injective)
        y)
    x
    
-- The axiom of countable choice, stated in a corresponding way.

Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥


  -- recc :
  --   ∀ {A B : Set} {R : A → A → Set} →
  --   (f : A → B) →
  --   (∀ x y → R x y → f x ≡ f y) →
  --   isSet B →
  --   A / R → B
  -- recc {A} {B} {R} f feq B-set ar =
  --   Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

mutual
  T-elim : ∀ {ℓ} (P : T → Set ℓ) -> ((t : ∞T) -> P (force t)) → ((t : T) → isProp (P t)) → (P leaf) → ((f : ℕ → ∞T) → ((n : ℕ) → P (force (f n))) → P (node f)) → (t : T) → P t
  T-elim P _ pr lf nd (leaf) = lf
  T-elim P v pr lf nd (node f) = nd f (v ∘ f)
  T-elim P _ pr lf nd (perm f g e i) =
    isOfHLevel→isOfHLevelDep 1 pr (T-elim P _ pr lf nd (node f)) (T-elim P _ pr lf nd (node (f ∘ g))) (perm f g e) i
  T-elim P _ pr lf nd (T-isSet a b p q i j) =
    isOfHLevel→isOfHLevelDep 2 (isProp→isSet ∘ pr) (T-elim P _ pr lf nd a) (T-elim P _ pr lf nd b) (cong (T-elim P _ pr lf nd) p) (cong (T-elim P _ pr lf nd) q) (T-isSet a b p q) i j

  -- ∞T-elim : ∀ {ℓ} (P : T → Set ℓ) → (t : ∞T) → P (force t)
  -- ∞T-elim P ∞P v t = transport (v t) (T-elim P ∞P v {!!} {!!} {!!} (force t))

b→T-surjective : Axiom-of-countable-choice ℓ-zero → isSurjection (b→T)
b→T-surjective acc =    
  T-elim (λ x → ∥ fiber b→T x ∥) (λ t → b→T-surjective acc (force t)) {!!} 
    (∣ leaf , refl ∣)
    (λ f p → ∥map∥ (λ x → node (fst ∘ x) , (node (b→∞T ∘ fst ∘ x) ≡⟨ (λ i → node (funExt (let temp = (snd ∘ x) in {!!}) i)) ⟩ node f ∎)) (acc p))
    -- b→T-surjective acc (f n)
    
