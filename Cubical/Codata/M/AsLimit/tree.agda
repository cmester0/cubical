{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.tree where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; elim to ∥elim∥ ; rec to ∥rec∥)
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

-- open import Cubical.Codata.M.AsLimit.Container
-- open import Cubical.Codata.M.AsLimit.itree
-- open import Cubical.Codata.M.AsLimit.M

data T₀ : Set where
  T₀-leaf : T₀
  T₀-node : (ℕ → T₀) → T₀

data _∼T₀_ : (_ _ : T₀) → Set where
  leaf∼ : T₀-leaf ∼T₀ T₀-leaf
  node∼ : {f g : ℕ → T₀} → ({n : ℕ} → f n ∼T₀ g n) → T₀-node f ∼T₀ T₀-node g
  perm∼ : (g : ℕ → T₀) (f : ℕ → ℕ) → isEquiv f → T₀-node g ∼T₀ T₀-node (g ∘ f)

data T : Set where
    leaf : T
    node : (ℕ → T) → T
    perm : (g : ℕ → T) → (f : ℕ → ℕ) → isEquiv f → node g ≡ node (g ∘ f)

-- makes life easier..
postulate
  T-isSet : isSet T
  T₀-isProp : isProp T₀

T₀→T : T₀ → T
T₀→T T₀-leaf = leaf
T₀→T (T₀-node f) = node (T₀→T ∘ f)

∼-≡ : ∀ {a b} → a ∼T₀ b → T₀→T a ≡ T₀→T b
∼-≡ (leaf∼) = refl
∼-≡ (node∼ f) = cong node (funExt λ n → ∼-≡ (f {n}))
∼-≡ (perm∼ g f p) = perm (T₀→T ∘ g) f p

T₀/∼→T : T₀ / _∼T₀_ → T
T₀/∼→T = Cubical.HITs.SetQuotients.elim (λ _ → T-isSet) T₀→T λ _ _ → ∼-≡

postulate
  asfd : isInjective node

leaf≢node : ∀ {f} → leaf ≡ node f → ⊥
leaf≢node x = subst (λ { leaf → T ; _ → ⊥ }) x (x i0)

T₀→T-isInjective : ∀ {w x} → T₀→T w ≡ T₀→T x → w ∼T₀ x
T₀→T-isInjective {w = T₀-leaf} {x = T₀-leaf} p = leaf∼
T₀→T-isInjective {w = T₀-node f} {x = T₀-node g} p = node∼ λ {n} → (T₀→T-isInjective ∘ (Iso.inv funExtIso (asfd p))) n
T₀→T-isInjective {w = T₀-node f} {x = T₀-leaf} p = Cubical.Data.Empty.rec (leaf≢node (sym p))
T₀→T-isInjective {w = T₀-leaf} {x = T₀-node g} p = Cubical.Data.Empty.rec (leaf≢node p)

T₀/∼→T-isInjective : isInjective T₀/∼→T
T₀/∼→T-isInjective {x} {y} = -- {w = [ x ]} {x = [ y ]} 
  elimProp
    {A = T₀}
    {R = _∼T₀_}
    {B = λ x → T₀/∼→T x ≡ T₀/∼→T y → x ≡ y}
    (λ x → isPropΠ λ _ → squash/ x y)
    (λ x → elimProp
               {A = T₀}
               {R = _∼T₀_}
               {B = λ y → T₀/∼→T [ x ] ≡ T₀/∼→T y → [ x ] ≡ y}
               (λ y → isPropΠ λ _ → squash/ [ x ] y)
               (λ y → eq/ x y ∘ T₀→T-isInjective)
               y)
    x

Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

T₀/∼→T-isSurjective : Axiom-of-countable-choice ℓ-zero → isSurjection T₀/∼→T
T₀/∼→T-isSurjective _ leaf = ∣ [ T₀-leaf ] , refl ∣
T₀/∼→T-isSurjective acc (node f) =
  Iso.fun (propTruncIdempotentIso squash)
  (∥map∥ (λ g →
   ∥map∥ (λ x →
     [ T₀-node (fst ∘ x) ] , cong node (funExt λ (n : ℕ) → cong T₀/∼→T (snd (x n)) ∙ (snd (g n))))
   (acc (λ (n : ℕ) → []surjective (fst (g n)))))
   (acc (T₀/∼→T-isSurjective acc ∘ f)))
T₀/∼→T-isSurjective acc (perm a b e i) =
  let temp : ∥ fiber T₀/∼→T (perm a b e i) ∥
      temp =
        -- Iso.fun (propTruncIdempotentIso squash)
        (Iso.fun (propTruncIdempotentIso squash)
          (∥map∥ (λ g →
           ∥map∥ (λ x →
             let temp' : T₀→T ∘ (fst ∘ x) ≡ a
                 temp' = (funExt λ (n : ℕ) → cong T₀/∼→T (snd (x n)) ∙ (snd (g n))) in
             let temps = ∼-≡ (perm∼ (fst ∘ x) b e) in
             let temps' : node a ≡ node (a ∘ b)
                 temps' = transport (λ j → node (temp' j) ≡ node (temp' j ∘ b)) temps in
             -- let temps'' : temps' ≡ perm a b e
             --     temps'' = T-isSet (node a) (node (a ∘ b)) temps' (perm a b e) in
             -- let tempsss : T₀→T (T₀-node (fst ∘ x)) ≡ T₀→T (T₀-node (fst ∘ x ∘ b))
             --     tempsss = T₀→T (T₀-node (fst ∘ x)) ≡⟨ cong node temp' ⟩ node a ≡⟨ temps' ⟩ node (a ∘ b) ≡⟨ cong (λ k → node (k ∘ b)) (sym temp') ⟩ T₀→T (T₀-node (fst ∘ x ∘ b)) ∎ in
             let temasd : [ T₀-node (fst ∘ x) ] ≡ [ T₀-node (fst ∘ x ∘ b) ]
                 temasd = eq/ (T₀-node (fst ∘ x)) (T₀-node (fst ∘ x ∘ b)) (perm∼ (fst ∘ x) b e)
             in
             let hd : node (T₀→T ∘ fst ∘ x) ≡ node (T₀→T ∘ fst ∘ x ∘ b)
                 hd = node (T₀→T ∘ fst ∘ x) ≡⟨ cong node temp' ⟩ node a ≡⟨ temps' ⟩ node (a ∘ b) ≡⟨ cong (λ k → node (k ∘ b)) (sym temp') ⟩ node (T₀→T ∘ fst ∘ x ∘ b) ∎
             in
             -- let tesadf :
             --            Square
             --              (node a ≡⟨ temps' ⟩ node (a ∘ b) ∎)
             --              (node (T₀→T ∘ fst ∘ x) ≡⟨ cong node {!!} ⟩ node (T₀→T ∘ fst ∘ x ∘ b) ∎)
             --              (node a ≡⟨ cong node (sym temp') ⟩ T₀→T (T₀-node (fst ∘ x)) ∎)
             --              (node (a ∘ b) ≡⟨ cong (λ k → node (k ∘ b)) (sym temp') ⟩ T₀→T (T₀-node (fst ∘ x ∘ b)) ∎)
             --     tesadf = {!!}
             -- in
             -- hcomp (λ j → λ {(i = i0) → cong node temp' ; (i = i1) -> cong (\k -> node (k ∘ b)) temp'}) (elimEq/ {A = T₀} {R = _∼T₀_} {B = λ x → {!!}} (λ k → {!!}) {!!} {!!} {!!})
               temasd i , {!!}
             -- ∣ temasd i , compPath-filler {x = perm a b e} {y = {!!}} {z = {!!}} {!!} {!!} ? ? ∣
             )
             (acc (λ (n : ℕ) → []surjective (fst (g n)))))
             (acc (T₀/∼→T-isSurjective acc ∘ a))))
  in {!!}


  -- let temp'1 : ∥ fiber T₀/∼→T (node a) ∥
  --     temp'1 = T₀/∼→T-isSurjective acc (node a) in -- ∥map∥ fst
  -- let temp'2 : ∥ ((n : ℕ) -> fiber T₀/∼→T (a n)) ∥
  --     temp'2 = acc (T₀/∼→T-isSurjective acc ∘ a) in
  -- let temp'3 : ∥ (ℕ → T₀) ∥
  --     temp'3 = ∥map∥ (λ x → fst ∘ x) {!!} in -- ∥map∥ fst
  -- Iso.fun (propTruncIdempotentIso squash)
  -- (∥map∥
  --   (λ x → let temp = ∼-≡ (perm∼ x b e) in
  --           let tempp = T₀/∼→T-isSurjective acc (temp i) in -- T₀→T ∘ x ≡ a
  --           let temppp : T₀→T ∘ x ≡ a
  --               temppp = {!!}
  --           in
  --   transport (λ j → ∥ fiber T₀/∼→T (perm (temppp j) b e i) ∥) tempp)
  --   temp'3)

-- node (λ x₁ → T₀→T (x x₁)) ≡ node (λ x₁ → T₀→T ((x ∘ b) x₁))

  -- ∥ fiber T₀/∼→T (perm a b e i) ∥
  -- Σ[ x ∈ A ] T₀/∼→T x ≡ (perm a b e i)

  -- ∥rec∥ {!!} (λ x → ∣ {!!} , {!!} ∣) temp'3
  -- ∥map∥ (λ x → perm∼ x b e) (temp'3)
    -- rec2 {!!} (λ x x₁ → ∣ squash/ x x₁ {!!} {!!} {!!} {!!} , {!!} ∣) {!!} {!!}
    -- ∥ fiber T₀/∼→T (perm a b e i) ∥
  -- ∥map∥ {!!} (acc (T₀/∼→T-isSurjective acc ∘ a))
