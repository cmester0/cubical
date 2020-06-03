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
open import Cubical.HITs.SetQuotients renaming (elim to elim/ ; rec to rec/)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.HLevels

mutual
  data Delay (R : Type₀) : Type₀ where
    now : R → Delay R
    later : Delay R → Delay R

-- Weak bisimularity for delay monad
mutual
  data _∼_ {R : Type₀} : (_ _ : Delay R) → Type₀ where
    ∼now : ∀ (s r : R) → s ≡ r → now s ∼ now r
    ∼later-l : ∀ t u → t ∼ u → later t ∼ u
    ∼later-r : ∀ t u → t ∼ u → t ∼ later u
    ∼later : ∀ t u → t ∼ u → later t ∼ later u

-- Partiality monad (QIIT)
data <_>⊥ (A : Type₀) : Type₀ where
  now : A → < A >⊥
  later : < A >⊥ → < A >⊥
  later-l : ∀ t u → t ≡ u → later t ≡ u
  -- later-r : ∀ t u → t ≡ u → t ≡ later u -- obsolete
  -- later-c : ∀ t u → t ≡ u → later t ≡ later u -- obsolete by embedding of constructors
  ⊥-isSet : isSet (< A >⊥)

postulate
  now-embedding : ∀ {R : Set} {a b : R} → Iso (<_>⊥.now a ≡ now b) (a ≡ b)
  later-embedding : ∀ {R : Set} {a b : < R >⊥} → (<_>⊥.later a ≡ later b) ≡ (a ≡ b)

later-r : ∀ {A : Type₀} (t u : < A >⊥) → t ≡ u → t ≡ later u
later-r  t u p = sym (later-l u t (sym p))

later-c : ∀ {A : Type₀} (t u : < A >⊥) → t ≡ u → later t ≡ later u
later-c t u p = transport (sym later-embedding) p

Delay→⊥ : ∀ {R} → Delay R → < R >⊥
Delay→⊥ (now a) = now a
Delay→⊥ (later t) = later (Delay→⊥ t)

Delay→⊥-∼→≡ : ∀ {R} → {x y : Delay R} → x ∼ y → Delay→⊥ x ≡ Delay→⊥ y
Delay→⊥-∼→≡ (∼now s r p) = cong now p
Delay→⊥-∼→≡ (∼later-l t u p) = later-l (Delay→⊥ t) (Delay→⊥ u) (Delay→⊥-∼→≡ p)
Delay→⊥-∼→≡ (∼later-r t u p) = later-r  (Delay→⊥ t) (Delay→⊥ u) (Delay→⊥-∼→≡ p)
Delay→⊥-∼→≡ (∼later t u p) = later-c (Delay→⊥ t) (Delay→⊥ u) (Delay→⊥-∼→≡ p)

Delay/∼→⊥ : ∀ {R} → Delay R / _∼_ → < R >⊥
Delay/∼→⊥ = rec/ Delay→⊥ (λ _ _ → Delay→⊥-∼→≡) ⊥-isSet

Delay→⊥-≡→∼ : ∀ {R} → {x y : Delay R} → Delay→⊥ x ≡ Delay→⊥ y → x ∼ y
Delay→⊥-≡→∼ {x = now a} {y = now b} p = ∼now a b (Iso.fun (now-embedding {a = a} {b = b}) p)
Delay→⊥-≡→∼ {x = later a} {y = now b} p =
  ∼later-l a (now b) (Delay→⊥-≡→∼ (subst (λ k → k ≡ now b) (later-l (Delay→⊥ a) (Delay→⊥ a) refl) p))
Delay→⊥-≡→∼ {x = now a} {y = later b} p =
  ∼later-r (now a) b (Delay→⊥-≡→∼ (subst (λ k → now a ≡ k) (later-l (Delay→⊥ b) (Delay→⊥ b) refl) p))
Delay→⊥-≡→∼ {x = later a} {y = later b} p =
  ∼later a b (Delay→⊥-≡→∼ (transport later-embedding p))

Delay/∼→⊥-isInjective : ∀ {R} → isInjective (Delay/∼→⊥ {R = R})
Delay/∼→⊥-isInjective {R = R} {x} {y} =
  elimProp
    {A = Delay R}
    {R = _∼_}
    {B = λ x → Delay/∼→⊥ x ≡ Delay/∼→⊥ y → x ≡ y}
    (λ x → isPropΠ λ _ → squash/ x y)
    (λ a → elimProp
      {A = Delay R}
      {R = _∼_}
      {B = λ y → Delay/∼→⊥ [ a ] ≡ Delay/∼→⊥ y → [ a ] ≡ y}
      (λ y → isPropΠ λ _ → squash/ [ a ] y)
      (λ b → eq/ a b ∘ Delay→⊥-≡→∼)
      y)
    x

Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

{-# NON_TERMINATING #-}
⊥-rec :
  ∀ {A : Set} (P : < A >⊥ → Set)
  → (∀ a → isProp (P a))
  → ((a : A) → P (now a))
  → (x : < A >⊥) → P x
⊥-rec P Pprop pn (now a) = pn a
⊥-rec P Pprop pn (later x) = subst P (later-r x x refl) (⊥-rec P Pprop pn x) -- problem here
⊥-rec P Pprop pn (later-l t u p i) = isOfHLevel→isOfHLevelDep 1 Pprop ((⊥-rec P Pprop pn) (later t)) ((⊥-rec P Pprop pn) u) (later-l t u p) i
⊥-rec P Pprop pn (⊥-isSet a b p q i j) = isOfHLevel→isOfHLevelDep 2 (isProp→isSet ∘ Pprop) ((⊥-rec P Pprop pn) a) ((⊥-rec P Pprop pn) b) (cong (⊥-rec P Pprop pn) p) (cong (⊥-rec P Pprop pn) q) (⊥-isSet a b p q) i j

Delay/∼→⊥-isSurjective : ∀ {R} → Axiom-of-countable-choice ℓ-zero → isSurjection (Delay/∼→⊥ {R = R})
Delay/∼→⊥-isSurjective acc =
  ⊥-rec
    (λ y → ∥ fiber Delay/∼→⊥ y ∥)
    (λ _ → propTruncIsProp)
    λ a → ∣ [ now a ] , refl ∣
