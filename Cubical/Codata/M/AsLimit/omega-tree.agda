{-# OPTIONS --cubical --guardedness #-}

module Cubical.Codata.M.AsLimit.omega-tree where

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

data b (X : Set) : Set where
  leaf : X → b X
  node : (ℕ → b X) → b X

data _∼_ {X : Set} : (_ _ : b X) → Set where
  ∼leaf : ∀ {a b} → a ≡ b → leaf a ∼ leaf b
  ∼node : ∀ {f g} → ((v : ℕ) → f v ∼ g v) → node f ∼ node g
  ∼perm : ∀ f → (g : (ℕ) → (ℕ)) → isEquiv g → node f ∼ node (f ∘ g)

data T (X : Set) : Set where
  leaf : X → T X
  node : (ℕ → T X) → T X
  perm : ∀ f → (g : (ℕ) → (ℕ)) → isEquiv g → node f ≡ node (f ∘ g)

postulate
  T-isSet : ∀ {X} → isSet (T X)

T-rec : ∀ {X} {ℓ} (P : Set ℓ) → isProp P → (X → P) → ((ℕ → T X) → P) → T X → P
T-rec P pr lf nd (leaf x) = lf x
T-rec P pr lf nd (node f) = nd f
T-rec P pr lf nd (perm f g e i) = pr (T-rec P pr lf nd (node f)) (T-rec P pr lf nd (node (f ∘ g))) i
-- T-rec P pr lf nd (T-isSet a b p q i j) = isProp→isSet pr (T-rec P pr lf nd a) (T-rec P pr lf nd b) (cong (T-rec P pr lf nd) p) (cong (T-rec P pr lf nd) q) i j

T-elim : ∀ {X} {ℓ} (P : T X → Set ℓ) → ((t : T X) → isProp (P t)) → ((x : X) → P (leaf x)) → ((f : ℕ → T X) → P (node f)) → (t : T X) → P t
T-elim P pr lf nd (leaf x) = lf x
T-elim P pr lf nd (node f) = nd f
T-elim P pr lf nd (perm f g e i) =
  isOfHLevel→isOfHLevelDep 1 pr (T-elim P pr lf nd (node f)) (T-elim P pr lf nd (node (f ∘ g))) (perm f g e) i
-- T-elim P pr lf nd (T-isSet a b p q i j) =
--   isOfHLevel→isOfHLevelDep 2 (isProp→isSet ∘ pr) (T-elim P pr lf nd a) (T-elim P pr lf nd b) (cong (T-elim P pr lf nd) p) (cong (T-elim P pr lf nd) q) (T-isSet a b p q) i j

b→T : ∀ {X} → b X → T X
b→T (leaf x) = leaf x
b→T (node f) = node (b→T ∘ f)

b→T-∼→≡ : ∀ {X} {x y : b X} → x ∼ y → b→T x ≡ b→T y
b→T-∼→≡ (∼leaf p) = cong (b→T ∘ leaf) p
b→T-∼→≡ {X} (∼node {f} {g} p) = cong {B = λ _ → T X} node (funExt (b→T-∼→≡ ∘ p))
b→T-∼→≡ (∼perm f g e) = perm (b→T ∘ f) g e

recc :
  ∀ {A B : Set} {R : A → A → Set} →
  (f : A → B) →
  (∀ x y → R x y → f x ≡ f y) →
  isSet B →
  A / R → B
recc {A} {B} {R} f feq B-set ar =
  Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

b/∼→T : ∀ {X} → b X / _∼_ → T X
b/∼→T = recc b→T (λ _ _ → b→T-∼→≡) T-isSet

isInjective : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Type _
isInjective f = ∀{w x} → f w ≡ f x → w ≡ x

postulate
  node-is-embedding :
    ∀ {X} → {f g : ℕ -> T X} → Iso {ℓ = ℓ-zero} {ℓ' = ℓ-zero} (T.node f ≡ node g) (f ≡ g)
  leaf-is-embedding :
    ∀ {X} → {a b : X} → Iso {ℓ = ℓ-zero} {ℓ' = ℓ-zero} (T.leaf a ≡ leaf b) (a ≡ b)

node≢leaf : {X : Set} → {f : ℕ -> T X} {a : X} -> T.node f ≡ leaf a -> ⊥
node≢leaf {X = X} x = subst T-case (sym x) (x i0)
  where
    T-case : T X → Type₀
    T-case (leaf _) = T X
    T-case (node _) = ⊥
    T-case (perm f g e i) = ⊥
    -- T-case (T-isSet a b p q i j) = {!!} -- TODO

b→T-injective : ∀ {X} {x y : b X} → b→T x ≡ b→T y → x ∼ y
b→T-injective {x = leaf a} {y = leaf b} p = ∼leaf  (Iso.fun leaf-is-embedding p)
b→T-injective {x = node f} {y = leaf b} p = rec (node≢leaf p)
b→T-injective {x = leaf a} {y = node g} p = rec (node≢leaf (sym p))
b→T-injective {x = node f} {y = node g} p = ∼node (b→T-injective ∘ (funExt⁻ (Iso.fun node-is-embedding p)))

b/∼→T-injective : ∀ X → isInjective b/∼→T
b/∼→T-injective X {x} {y} =
  elimProp
    {A = b X}
    {R = _∼_}
    {B = λ x → b/∼→T x ≡ b/∼→T y → x ≡ y}
    (λ x → isPropΠ λ _ → squash/ x y)
    (λ x →
      elimProp
        {A = b X}
        {R = _∼_}
        {B = λ y → b/∼→T [ x ] ≡ b/∼→T y → [ x ] ≡ y}
        (λ y → isPropΠ λ _ → squash/ [ x ] y)
        (λ y → eq/ x y ∘ b→T-injective)
        y)
    x
    
-- The axiom of countable choice, stated in a corresponding way.

Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

{-# NON_TERMINATING #-}
b→T-surjective : ∀ {X} → Axiom-of-countable-choice ℓ-zero → isSurjection (b→T {X = X})
b→T-surjective {X = X} acc =    
  T-elim (λ x → ∥ fiber b→T x ∥) (λ _ → propTruncIsProp)
    (λ x → ∣ (leaf x) , refl ∣)
    (λ f → ∥map∥ (λ x → (node (fst ∘ x)) , (node (b→T ∘ (fst ∘ x)) ≡⟨ (λ i → node (funExt (snd ∘ x) i)) ⟩ node f ∎)) (acc (λ (n : ℕ) → b→T-surjective acc (f n))) )

{-# NON_TERMINATING #-}
b/∼→T-surjective : ∀ {X} → Axiom-of-countable-choice ℓ-zero → isSurjection (b/∼→T {X = X})
b/∼→T-surjective {X = X} acc =
  T-elim (λ x → ∥ fiber b/∼→T x ∥) (λ _ → propTruncIsProp)
    (λ x → ∣ [ leaf x ] , refl ∣)
    (λ f → ∥map∥ (λ x → ([ node (fst ∘ x) ]) , (node (b→T ∘ (fst ∘ x)) ≡⟨ (λ i → node (funExt (snd ∘ x) i)) ⟩ node f ∎)) (acc (λ (n : ℕ) → b→T-surjective acc (f n))))

b/∼≡T : ∀ {X} → Axiom-of-countable-choice ℓ-zero → b X / _∼_ ≡ T X
b/∼≡T {X = X} acc = ua (b/∼→T , (isEmbedding×isSurjection→isEquiv (injEmbedding squash/ T-isSet (b/∼→T-injective X) , b/∼→T-surjective acc)))
