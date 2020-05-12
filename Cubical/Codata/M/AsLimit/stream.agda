{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.stream where

open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

--------------------------------------
-- Stream definitions using M.AsLimit --
--------------------------------------

stream-S : ∀ A -> Container ℓ-zero
stream-S A = (A , (λ _ → Unit))

stream : ∀ (A : Type₀) -> Type₀
stream A = M (stream-S A)

cons : ∀ {A} -> A -> stream A -> stream A
cons x xs = in-fun (x , λ { tt -> xs } )

hd : ∀ {A} -> stream A -> A
hd {A} S = out-fun S .fst

tl : ∀ {A} -> stream A -> stream A
tl {A} S = out-fun S .snd tt

open Iso

hd' : ∀ {A} -> stream A -> A
hd' x = x .fst 1 .fst

tl' : ∀ {A} -> stream A -> stream A
tl' {A} s = (λ {0 → lift tt ; (suc n) → s .fst (suc (suc n)) .fst , {!!}}) , {!!}

-- (λ n → transport (λ i → Wₙ (stream-S A) n) (s .fst (suc n) .snd tt))

-- private
--   temp-x : ∀ {A} → P₀ (stream-S A) (stream A)  → (n : ℕ) → Wₙ (stream-S A) n
--   temp-x _ 0 = lift tt
--   temp-x (x , y) (suc 0) = x , λ _ → lift tt
--   temp-x (x , y) (suc (suc n)) = y tt .fst (suc n) .fst , λ _ → temp-x (x , y) (suc n)

--   temp-π : ∀ {A} → (p : P₀ (stream-S A) (stream A)) → (n : ℕ) → πₙ (stream-S A) (temp-x p (suc n)) ≡ temp-x p n
--   temp-π (x , y) 0 = refl
--   temp-π (x , y) (suc 0) i = {!!} , {!!} -- y tt .fst 1 .fst ≡ x ?

-- private
--   temp-x' : ∀ {A} → stream A → (n : ℕ) → Wₙ (stream-S A) n
--   temp-x' _ 0 = lift tt
--   temp-x' x (suc n) = (x .fst (suc (suc n)) .fst) , λ {tt → x .fst (suc n) .snd tt}

--   temp-π' : ∀ {A} → (x : stream A) → (n : ℕ) → πₙ (stream-S A) (temp-x' x (suc n)) ≡ temp-x' x n
--   temp-π' _ 0 = refl
--   temp-π' x (suc n) i = (x .snd (suc (suc n)) i .fst) , (λ {tt → x .snd (suc n) i .snd tt})

-- shift-stream : ∀ A → Iso (P₀ (stream-S A) (stream A)) (stream A)
-- fun (shift-stream A) (x , y) = temp-x (x , y), temp-π (x , y)
-- inv (shift-stream A) x = (x .fst 1 .fst) , λ {tt → temp-x' x , temp-π' x}
-- rightInv (shift-stream A) x =
--    fst (fun (shift-stream A) (inv (shift-stream A) x)) , {!!}
--     ≡⟨ ΣPathP (funExt (λ {0 → refl ; (suc 0) → refl ; (suc (suc n)) → refl}) , {!!}) ⟩
--    -- temp-x (x .fst 1 .fst , (λ { tt → temp-x' x , temp-π' x })) , {!!}
--    (λ {0 → lift tt
--      ;(suc 0) → x .fst 1 .fst , λ _ → lift tt
--      ;(suc (suc n)) → x .fst (suc (suc n)) .fst , λ {tt → temp-x (x .fst 1 .fst , λ { tt → temp-x' x , temp-π' x }) (suc n)}}) ,
--    {!!}
--     ≡⟨ ΣPathP ((funExt (λ {0 → refl ; (suc 0) → refl ; (suc (suc n)) → ΣPathP (refl , {!!})})) , {!!}) ⟩
--   (λ {0 → lift tt
--     ;(suc 0) → x .fst 1
--     ;(suc (suc n)) → x .fst (suc (suc n))}) , {!!}
--     ≡⟨ ΣPathP ((funExt (λ {0 → refl ; (suc 0) → refl ; (suc (suc n)) → refl})) , {!!}) ⟩
--   x ∎
-- leftInv (shift-stream A) x =
--    fst (inv (shift-stream A) (fun (shift-stream A) x)) , {!!}
--     ≡⟨ {!!} ⟩
--   fst (inv (shift-stream A) (fun (shift-stream A) x)) , {!!}
--     ≡⟨ {!!} ⟩
--   {!!} , {!!}
--     ≡⟨ {!!} ⟩
--   {!!} ∎
--   -- (λ {0 → lift tt
--   --    ;(suc 0) → x .fst 1 .fst , λ _ → lift tt
--   --    ;(suc (suc n)) → (temp-x' x (suc n) .fst) , {!!}}) , {!!}
