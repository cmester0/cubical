{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.QIIT-new where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
-- open import Cubical.Codata.M.AsLimit.itree

open import Cubical.HITs.SetQuotients

mutual
  data tree (R : Type₀) (E : Type₀) : Set where
    tree-leaf : R → tree R E
    tree-node : (E → ∞tree R E) → tree R E
  
  record ∞tree (R : Type₀) (E : Type₀) : Set where
    coinductive
    field
      force : tree R E

open ∞tree

infix 4 _↑ _↓_

_↓_ : ∀ {A : Set} → A ⊎ Unit → A → Set
x ↓ y = x ≡ inl y

_↑ :  ∀ {A : Set} → A ⊎ Unit → Set
x ↑ = x ≡ inr tt

_⊑maybe_ : ∀ {A : Set} → A ⊎ Unit → A ⊎ Unit → Set
x ⊑maybe y = (x ≡ y) ⊎ ((x ↑) × (y ↑ → ⊥))

Seq-tree : (R : Type₀) (E : Type₀) → Set
Seq-tree R E = (ℕ → E) → Σ[ s ∈ (ℕ → R ⊎ Unit) ] ((n : ℕ) → s n ⊑maybe s (suc n))

[⟩_,_⟨] : ∀ {ℓ} {A : Set ℓ} → A → (ℕ → A) → (ℕ → A)
[⟩ x , f ⟨] 0 = x
[⟩ x , f ⟨] (suc n) = f n -- (λ { 0 → x ; (suc n) → f n })

shift-Seq' :
  {R : Type₀} {E : Type₀}
  → (t : E → Seq-tree R E)
  --------------
  → Seq-tree R E
shift-Seq' t =
  λ e →
    [⟩ inr tt , fst (t (e 0) (e ∘ suc)) ⟨] ,
    λ {0 → (case fst (t (e 0) (e ∘ suc)) 0 return (λ x → inr tt ⊑maybe x) of λ { (inl r) → inr (refl , inl≢inr) ; (inr tt) → inl refl }) 
      ;(suc n) → snd (t (e 0) (e ∘ suc)) n }

-- Seq→tree : {!!}
-- Seq→tree s = {!!}

tree→Seq : ∀ {R} {E} → tree R E → Seq-tree R E
tree→Seq (tree-leaf r) = λ _ → (λ _ → inl r) , (λ _ → inl refl)
tree→Seq (tree-node k) = shift-Seq' λ e → tree→Seq (force (k e))

unshift-Seq :
  {R : Type₀} {E : Type₀}
  → Seq-tree R E
  → E
  --------------
  → Seq-tree R E
unshift-Seq se v = λ e → fst (se [⟩ v , e ⟨]) ∘ suc , snd (se [⟩ v , e ⟨]) ∘ suc

asfd : ∀ {R E} (e : E → Seq-tree R E) (v : E) → unshift-Seq (shift-Seq' e) v ≡ e v
asfd e v = refl

asfd' : ∀ {R E} (s : Seq-tree R E) (e : ℕ → E) → (shift-Seq' (unshift-Seq s)) e ≡ s e
asfd' s e =
  shift-Seq' (unshift-Seq s) e
    ≡⟨ ΣPathP ((funExt λ {0 → refl ; (suc n) → refl}) , λ {i 0 → case fst (unshift-Seq s (e 0) (e ∘ suc)) 0 return (λ x → inr tt ⊑maybe x) of {!!} ; i (suc n) → snd (unshift-Seq s (e 0) (e ∘ suc)) n}) ⟩
  ([⟩ inr tt , fst (unshift-Seq s (e 0) (e ∘ suc)) ⟨] ,
  λ { 0 → case fst (unshift-Seq s (e 0) (e ∘ suc)) 0 return (λ x → inr tt ⊑maybe x) of
    λ { (inl r) → inr (refl , inl≢inr)
      ; (inr tt) → inl refl }
    ; (suc n) → snd (unshift-Seq s (e 0) (e ∘ suc)) n })
    ≡⟨ ΣPathP ((funExt (λ { 0 → refl ; (suc n) → refl })) , (λ { i 0 → case fst (unshift-Seq s (e 0) (e ∘ suc)) 0 return (λ x → inr tt ⊑maybe x) of {!!} ; i (suc n) → snd (unshift-Seq s (e 0) (e ∘ suc)) n })) ⟩
  ([⟩ inr tt , fst (s [⟩ e 0 , e ∘ suc ⟨]) ∘ suc ⟨] ,
  λ { 0 → case fst (s [⟩ e 0 , e ∘ suc ⟨]) (suc 0) return (λ x → inr tt ⊑maybe x) of
    λ { (inl r) → inr (refl , inl≢inr)
      ; (inr tt) → inl refl }
    ; (suc n) → snd (s [⟩ e 0 , e ∘ suc ⟨]) (suc n) })
    ≡⟨ {!!} ⟩
  ([⟩ inr tt , fst (s e) ∘ suc ⟨] ,
  λ { 0 → case fst (s e) (suc 0) return (λ x → inr tt ⊑maybe x) of
    λ { (inl r) → inr (refl , inl≢inr)
      ; (inr tt) → inl refl }
    ; (suc n) → snd (s e) (suc n) })
    ≡⟨ {!!} ⟩ -- only true if inr tt ...
  s e ∎


  --   ≡⟨ refl ⟩
  -- [⟩ inr tt , fst (unshift-Seq s (e 0) (e ∘ suc)) ⟨] ,
  -- {!!}


-- (λ {0 → (case fst ((unshift-Seq s) (e 0) (e ∘ suc)) 0 return (λ x → inr tt ⊑maybe x) of λ { (inl r) → inr (refl , inl≢inr) ; (inr tt) → inl refl }) ;(suc n) → snd ((unshift-Seq s) (e 0) (e ∘ suc)) n })

-- mutual
--   helper : {R : Type₀} {E : Type₀} → (E → ∞tree R E) → E → tree R E
--   helper = _∘_ force

--   ∞tree→Seq-tree : {R : Type₀} {E : Type₀} → (E → ∞tree R E) → Seq-tree R E
--   s (∞tree→Seq-tree k) e = s (tree→Seq-tree (helper k (e 0))) (e ∘ suc)
--   q (∞tree→Seq-tree k) e = q (tree→Seq-tree (helper k (e 0))) (e ∘ suc)
  
--   tree→Seq-tree : {R : Type₀} {E : Type₀} → tree R E → Seq-tree R E
--   s (tree→Seq-tree (tree-leaf r)) _ _ = inl r
--   q (tree→Seq-tree (tree-leaf r)) _ _ = inl refl
--   tree→Seq-tree (tree-node k) = shift-Seq' (∞tree→Seq-tree k)
  
    -- shift-Seq (∞tree→Seq-tree k)
    --   (λ e →
    --     (inr tt) ,
    --     (case fst (cons (∞tree→Seq-tree k) e) 0 return (λ x → inr tt ⊑maybe x)
    --        of λ {(inl r) → inr (refl , inl≢inr)
    --             ;(inr tt) → inl refl}))
