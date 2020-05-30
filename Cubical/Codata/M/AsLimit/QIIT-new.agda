{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.QIIT-new where

open import Cubical.Data.Unit
open import Cubical.Data.Prod -- hiding (_×_)
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
-- open import Cubical.Codata.M.AsLimit.itree

open import Cubical.HITs.SetQuotients renaming (elim to /elim)
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; elim to ∥elim∥)

data bT : Set where
  bleaf : bT
  bnode : (ℕ → bT) → bT

data _∼bT_ : (_ _ : bT) → Set where
  leaf∼ : bleaf ∼bT bleaf
  node∼ : {f g : ℕ → bT} → ({n : ℕ} → f n ∼bT g n) → bnode f ∼bT bnode g
  perm∼ : (f : ℕ → bT) (g : ℕ → ℕ) → isEquiv g → bnode f ∼bT bnode (f ∘ g)

data bTp : Set where
    leaf : bTp
    node : (ℕ → bTp) → bTp
    perm : (f : ℕ → bTp) → (g : ℕ → ℕ) → isEquiv g → node f ≡ node (f ∘ g)
    bTp-isSet : isSet bTp

bT→bTp : bT → bTp
bT→bTp bleaf = leaf
bT→bTp (bnode f) = node (bT→bTp ∘ f)

recc :
  ∀ {A B : Set} {R : A → A → Set} →
  (f : A → B) →
  (∀ x y → R x y → f x ≡ f y) →
  isSet B →
  A / R → B
recc {A} {B} {R} f feq B-set ar =
  /elim {B = λ _ → B} (λ _ → B-set) f feq ar

∼→≡ : {x y : bT} → x ∼bT y → bT→bTp x ≡ bT→bTp y
∼→≡ leaf∼ = refl
∼→≡ (node∼ f) = cong node (funExt (λ x → ∼→≡ f))
∼→≡ (perm∼ f g e) = perm (bT→bTp ∘ f) g e

bT/∼→bTp : bT / _∼bT_ → bTp
bT/∼→bTp = recc bT→bTp (λ _ _ → ∼→≡) bTp-isSet

postulate
  bleaf≢bnode : ∀ {f} → bleaf ≡ bnode f → ⊥
  leaf≢node : ∀ {f} → leaf ≡ node f → ⊥
  nodeIsInjective : isInjective node
  
≡→∼ : {x y : bT} → bT→bTp x ≡ bT→bTp y → x ∼bT y
≡→∼ {x = bleaf} {y = bleaf} p = leaf∼
≡→∼ {x = bleaf} {y = bnode g} p = ⊥rec (leaf≢node p)
≡→∼ {x = bnode f} {y = bleaf} p = ⊥rec (leaf≢node (sym p))
≡→∼ {x = bnode f} {y = bnode g} p =
  node∼ λ {n} → ≡→∼ (Iso.inv funExtIso (nodeIsInjective p) n)

bT/∼→bTp-isInjective : isInjective bT/∼→bTp
bT/∼→bTp-isInjective {x} {y} =
  elimProp
    {A = bT}
    {R = _∼bT_}
    {B = λ x → bT/∼→bTp x ≡ bT/∼→bTp y → x ≡ y}
    (λ x → isPropΠ λ _ → squash/ x y)
    (λ x →
      elimProp
      {A = bT}
      {R = _∼bT_}
      {B = λ y → bT/∼→bTp [ x ] ≡ bT/∼→bTp y → [ x ] ≡ y}
      (λ y → isPropΠ λ _ → squash/ [ x ] y)
      (λ y → eq/ x y ∘ ≡→∼)
      y)
    x

private
  Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
  Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥
  
module ElimT
  (Tᴹ : bTp → Set)
  (leafᴹ : Tᴹ leaf)
  (nodeᴹ : {f : ℕ → bTp} → (fᴹ : (n : ℕ) → Tᴹ (f n)) → Tᴹ (node f))
  (permᴹ : {g : ℕ → bTp} (gᴹ : (n : ℕ) → Tᴹ (g n)) → (f : ℕ → ℕ) (p : isEquiv f)
         → PathP (λ x → Tᴹ (perm g f p x)) (nodeᴹ gᴹ) (nodeᴹ (gᴹ ∘ f))) where
    Elim : (t : bTp) → Tᴹ t
    Elim leaf = leafᴹ
    Elim (node f) = nodeᴹ (λ n → Elim (f n))
    Elim (perm g f p x) = permᴹ (λ n → Elim (g n)) f p x

bT/∼→bTp-isSurjection : isSurjection bT/∼→bTp
bT/∼→bTp-isSurjection =
  ElimT.Elim
    (∥_∥ ∘ fiber bT/∼→bTp)
    ∣ [ bleaf ] , refl ∣
    (λ {f} fᴹ →
      let temp' = Iso.fun (propTruncIdempotentIso propTruncIsProp) (∥map∥ (λ x → ∥map∥ (λ x (n : ℕ) → fst (x n)) (acc (λ n → []surjective (x n .fst))) ) (acc fᴹ)) in
      let temp = λ (n : ℕ) → Iso.fun (propTruncIdempotentIso propTruncIsProp) (∥map∥ (λ x → ∥map∥ (bT→bTp ∘ fst) ([]surjective (x .fst))) (fᴹ n)) in
      -- let temp'' : ∣ temp' ∣ ≡ temp
      --     temp'' = Iso.leftInv (propTruncIdempotentIso propTruncIsProp) temp
      -- in
      let temp''' : (n : ℕ) → temp n ≡ ∣ f n ∣
          temp''' n = elimProp {A = bT} {R = _∼bT_}
            {B = λ x → (∥map∥ (bT→bTp ∘ fst) ([]surjective x)) ≡ ∣ f n ∣}
            (λ x → isContr→isProp (isProp→isContrPath propTruncIsProp _ _))
            (λ x → cong ∣_∣ (bT→bTp x ≡⟨ {!!} ⟩ f n ∎))
            {!!}
      in
      ∥map∥ (λ x → [ bnode x ] , (node (bT→bTp ∘ x) ≡⟨ cong node (funExt (λ k → {!!})) ⟩ node f ∎)) temp') -- in [ bnode {!!} ] , {!!} -- (λ x₁ → bT→bTp (x x₁)) ≡ f
    {!!}
  
  where
    postulate
      acc : Axiom-of-countable-choice ℓ-zero

-- ∥map∥ (λ x → bT→bTp ∘ x) temp' ≡ ∣ f ∣

-- map2

-- -- T₀ = M ((Unit ⊎ Unit) , (λ {(inl _) → ⊥ ; (inr _) → ℕ}))

-- -- T₀-leaf : T₀
-- -- T₀-leaf = in-fun (inl tt , λ ())

-- -- T₀-node : (ℕ → T₀) → T₀
-- -- T₀-node f = in-fun (inr tt , f)

-- data T₀ : Set where
--   T₀-leaf : T₀
--   T₀-node : (ℕ → T₀) → T₀

-- data _∼T₀_ : (_ _ : T₀) → Set where
--   leaf∼ : T₀-leaf ∼T₀ T₀-leaf
--   node∼ : {f g : ℕ → T₀} → ({n : ℕ} → f n ∼T₀ g n) → T₀-node f ∼T₀ T₀-node g
--   perm∼ : (g : ℕ → T₀) (f : ℕ → ℕ) → isEquiv f → T₀-node g ∼T₀ T₀-node (g ∘ f)

-- data T : Set where
--     leaf : T
--     node : (ℕ → T) → T
--     perm : (g : ℕ → T) → (f : ℕ → ℕ) → isEquiv f → node g ≡ node (g ∘ f)
--     T-isSet : isSet T

-- -- mutual
-- --   data T : Set where
-- --     leaf : T
-- --     node : (ℕ → ∞T) → T
-- --     perm : (g : ℕ → ∞T) → (f : ℕ → ℕ) → isEquiv f → node g ≡ node (g ∘ f)
-- --     T-isSet : isSet T

-- --   record ∞T : Set where
-- --     coinductive
-- --     field
-- --       force : T

-- -- open ∞T

-- -- mutual
-- --   T₀→T : T₀ → T
-- --   T₀→T = M-coinduction-const T
-- --     λ {(inl tt , _) → leaf
-- --       ;(inr tt , f) → node (T₀→∞T ∘ f)}
  
-- --   T₀→∞T : T₀ → ∞T
-- --   force (T₀→∞T x) = T₀→T x

-- T₀→T : T₀ → T
-- T₀→T T₀-leaf = leaf
-- T₀→T (T₀-node f) = node (T₀→T ∘ f)

-- ∼-≡ : ∀ {a b} → a ∼T₀ b → T₀→T a ≡ T₀→T b
-- ∼-≡ (leaf∼) = refl
-- ∼-≡ (node∼ f) = cong node (funExt λ n → ∼-≡ (f {n}))
-- ∼-≡ (perm∼ g f p) = perm (T₀→T ∘ g) f p

-- T₀/∼→T : T₀ / _∼T₀_ → T
-- T₀/∼→T = Cubical.HITs.SetQuotients.elim (λ _ → T-isSet) T₀→T λ _ _ → ∼-≡

-- postulate
--   asfd : isInjective node
--   asdf : ∀ f → leaf ≡ node f → ⊥

-- T₀→T-isInjective : ∀ {w x} → T₀→T w ≡ T₀→T x → w ∼T₀ x
-- T₀→T-isInjective {w = T₀-leaf} {x = T₀-leaf} p = leaf∼
-- T₀→T-isInjective {w = T₀-node f} {x = T₀-node g} p = node∼ λ {n} → (T₀→T-isInjective ∘ (Iso.inv funExtIso (asfd p))) n
-- T₀→T-isInjective {w = T₀-node f} {x = T₀-leaf} p = Cubical.Data.Empty.elim (asdf _ (sym p))
-- T₀→T-isInjective {w = T₀-leaf} {x = T₀-node g} p = Cubical.Data.Empty.elim (asdf _ p)

-- T₀/∼→T-isInjective : isInjective T₀/∼→T
-- T₀/∼→T-isInjective {x} {y} = -- {w = [ x ]} {x = [ y ]} 
--   elimProp
--     {A = T₀}
--     {R = _∼T₀_}
--     {B = λ x → T₀/∼→T x ≡ T₀/∼→T y → x ≡ y}
--     (λ x → isPropΠ λ _ → squash/ x y)
--     (λ x → elimProp
--                {A = T₀}
--                {R = _∼T₀_}
--                {B = λ y → T₀/∼→T [ x ] ≡ T₀/∼→T y → [ x ] ≡ y}
--                (λ y → isPropΠ λ _ → squash/ [ x ] y)
--                (λ y → eq/ x y ∘ T₀→T-isInjective)
--                y)
--     x

-- Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
-- Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- T₀/∼→T-isSurjective : Axiom-of-countable-choice ℓ-zero → isSurjection T₀/∼→T
-- T₀/∼→T-isSurjective _ leaf = ∣ [ T₀-leaf ] , refl ∣
-- T₀/∼→T-isSurjective acc (node f) =
--   -- let sadf = acc (T₀/∼→T-isSurjective acc ∘ f) in
--   -- let temp : (x : (n : ℕ) → fiber T₀/∼→T (f n)) → (n : ℕ) → ∥ T₀ ∥
--   --     temp x n = Cubical.HITs.PropositionalTruncation.map fst ([]surjective (x n .fst)) in
--   -- let temp' : (x : (n : ℕ) → fiber T₀/∼→T (f n)) → ∥ T₀ ∥
--   --     temp' x = Cubical.HITs.PropositionalTruncation.map T₀-node (acc (temp x)) in
--   -- let temp'' : ∥ T₀ ∥
--   --     temp'' = Cubical.HITs.PropositionalTruncation.elim (λ a x y → {!!}) temp' sadf in

--   let temp' = {!!} in
--   let temp = Cubical.HITs.PropositionalTruncation.map {!!} {!!} in
--   {!!}

--   -- acc (T₀/∼→T-isSurjective acc ∘ f)
--   -- acc (λ (n : ℕ) → []surjective (x n .fst))

--     -- Cubical.HITs.PropositionalTruncation.map (λ x → [ x ] ,
--     --   (T₀/∼→T [ x ] ≡⟨ {!!} ⟩ T₀→T x ≡⟨ {!!} ⟩ node f ∎)) (temp' {!!})
-- --  (λ x → [ T₀-node (λ n → {!!}) ] , {!!})

-- -- let temp = []surjective {!!} in {!!}

--   -- ((x : ℕ) → fiber T₀/∼→T (f x)) → fiber T₀/∼→T (node f)

--   -- let temp = Cubical.HITs.PropositionalTruncation.map {A = ℕ → T₀} {B = T₀} T₀-node (acc λ n → let temp = f n in {!!}) in
--   -- ∣ [ T₀-node {!!} ] , (T₀/∼→T [ T₀-node {!!} ] ≡⟨ refl ⟩ node {!!} ≡⟨ {!!} ⟩ node f ∎) ∣

-- -- ∣ [ T₀-node (λ n → let temp = T₀/∼→T-isSurjective acc (f n) in {!!}) ] , {!!} ∣
--   -- (A → B) → (∥ A ∥ → ∥ B ∥)


-- -- asfd : {ℓ : Level} {S : Container ℓ} → (_⊑_ : S .fst → S .fst → Type ℓ) → Type ℓ
-- -- asfd {ℓ} {S = S} _⊑_ =
-- --   Σ[ s₀ ∈ S .fst ]
-- --   Σ[ s ∈ (ℕ → (Σ[ a ∈ S .fst ] S .snd a) → S .fst) ]
-- --     ((p : Σ[ a ∈ (S .fst) ] (S .snd a)) → s₀ ⊑ s 0 p) × 
-- --     ((n : ℕ) → (p : Σ-syntax (S .fst) λ a → S .snd a) → s n p ⊑ s (suc n) p)

-- -- asfd'' : {ℓ : Level} {S : Container ℓ} → (_⊑_ : S .fst → S .fst → Type ℓ)
-- --        → M S → (asfd _⊑_)
-- -- asfd'' _⊑_ p =
-- --   (p .fst 1 .fst) ,
-- --   ((λ x y → p .fst (suc x) .fst) ,
-- --   ((λ x → {!!}) , λ n p₁ → {!!}))
  
-- -- asfd' : {ℓ : Level} {S : Container ℓ} → (_⊑_ : S .fst → S .fst → Type ℓ)
-- --       → (asfd _⊑_) → M S
-- -- asfd' _⊑_ p =
-- --   (λ {0 → lift tt ; (suc 0) → {!!} ; (suc n) → {!!}}) , {!!}

-- -- -- -- Sierpinski set as as Hit
-- -- -- record Sierpinski (S : {!!}) : Set where
-- -- --   field
-- -- --     1ₛ : S
-- -- --     0ₛ : S
-- -- --     _∧s_ : S → S → S
-- -- --     ⋁_ : (ℕ → S) → S
    

-- -- -- -- The partiality monad
-- -- -- partiality-container : {ℓ : Level} → (S : Type ℓ) → S → Container ℓ
-- -- -- partiality-container S 1ₛ = S , λ v → v ≡ 1ₛ

-- -- -- partiality-monad : {ℓ : Level} → (S : Type ℓ) → S → Type ℓ
-- -- -- partiality-monad S 1ₛ = M (partiality-container S 1ₛ)

-- -- mutual
-- --   data tree (R : Type₀) (E : Type₀) : Set where
-- --     tree-leaf : R → tree R E
-- --     tree-node : (E → ∞tree R E) → tree R E
  
-- --   record ∞tree (R : Type₀) (E : Type₀) : Set where
-- --     coinductive
-- --     field
-- --       force : tree R E

-- -- open ∞tree

-- -- infix 4 _↑ _↓_

-- -- _↓_ : ∀ {A : Set} → A ⊎ Unit → A → Set
-- -- x ↓ y = x ≡ inl y

-- -- _↑ :  ∀ {A : Set} → A ⊎ Unit → Set
-- -- x ↑ = x ≡ inr tt

-- -- _⊑maybe_ : ∀ {A : Set} → A ⊎ Unit → A ⊎ Unit → Set
-- -- x ⊑maybe y = (x ≡ y) ⊎ ((x ↑) × (y ↑ → ⊥))




-- -- Seq-tree : (R : Type₀) (E : Type₀) → Set
-- -- Seq-tree R E =
-- --    Σ[ s₀ ∈ R ⊎ Unit ]
-- --   (Σ[ s ∈ (ℕ → R ⊎ Unit) ]
-- --   ( (E → s₀ ⊑maybe s 0)
-- --   × ((n : ℕ) → E → s n ⊑maybe s (suc n))))

-- -- [⟩_,_⟨] : ∀ {ℓ} {A : Set ℓ} → A → (ℕ → A) → (ℕ → A)
-- -- [⟩ x , f ⟨] 0 = x
-- -- [⟩ x , f ⟨] (suc n) = f n -- (λ { 0 → x ; (suc n) → f n })

-- -- never⊑ : {R : Type₀} (x : R ⊎ Unit) → inr tt ⊑maybe x
-- -- never⊑ (inl a) = inr (refl , inl≢inr)
-- -- never⊑ (inr tt) = inl refl

-- -- shift-Seq :
-- --   {R : Type₀} {E : Type₀}
-- --   → (t : Seq-tree R E)
-- --   → (v : (Σ[ s₀ ∈ R ⊎ Unit ] (E → s₀ ⊑maybe (fst t))))
-- --   --------------
-- --   → Seq-tree R E
-- -- shift-Seq {R} {E} (a , b , c , d) (s₀ , p₀) =
-- --   s₀ , [⟩ a , b ⟨] , p₀ , λ {0 → c ; (suc n) → d n }

-- -- shift-Seq' :
-- --   {R : Type₀} {E : Type₀}
-- --   → Seq-tree R E
-- --   --------------
-- --   → Seq-tree R E
-- -- shift-Seq' {R} {E} (a , b , c , d) =
-- --   shift-Seq (a , b , c , d) (inr tt , λ _ → never⊑ a)

-- -- unshift-Seq :
-- --   {R : Type₀} {E : Type₀}
-- --   → Seq-tree R E
-- --   --------------
-- --   → Seq-tree R E
-- -- unshift-Seq t =
-- --   fst (snd t) 0 , (fst (snd t) ∘ suc , (proj₂ (snd (snd t)) 0 , proj₂ (snd (snd t)) ∘ suc))
-- -- -- unshift-Seq (a , b , c , d) = b 0 , (b ∘ suc , (d 0 , d ∘ suc))

-- -- asfd : ∀ {R E} (t : Seq-tree R E) → unshift-Seq (shift-Seq' t) ≡ t
-- -- asfd (a , b , c , d) = refl

-- -- helper : ∀ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {x y : A × B}
-- --        → proj₁ x ≡ proj₁ y
-- --        → proj₂ x ≡ proj₂ y
-- --        → x ≡ y
-- -- helper {x = (a , b)} {y = (c , d)} p q = λ i → (p i) , (q i)

-- -- postulate
-- --   asfd' : ∀ {R E} (t : Seq-tree R E) → shift-Seq (unshift-Seq t) (fst t , proj₁ (snd (snd t))) ≡ t

-- -- tree→Seq : ∀ {R} {E} → tree R E → Seq-tree R E
-- -- tree→Seq (tree-leaf r) = (inl r) , ((λ _ → inl r) , ((λ _ → inl refl) , λ _ _ → inl refl))
-- -- tree→Seq (tree-node k) = shift-Seq' (tree→Seq (force (k {!!})))



-- -- -- Seq-tree : (R : Type₀) (E : Type₀) → Set
-- -- -- Seq-tree R E = (ℕ → E) → Σ[ s ∈ (ℕ → R ⊎ Unit) ] ((n : ℕ) → s n ⊑maybe s (suc n))

-- -- -- [⟩_,_⟨] : ∀ {ℓ} {A : Set ℓ} → A → (ℕ → A) → (ℕ → A)
-- -- -- [⟩ x , f ⟨] 0 = x
-- -- -- [⟩ x , f ⟨] (suc n) = f n -- (λ { 0 → x ; (suc n) → f n })
-- -- -- never⊑ : {R : Type₀} (x : R ⊎ Unit) → inr tt ⊑maybe x
-- -- -- never⊑ (inl a) = inr (refl , inl≢inr)
-- -- -- never⊑ (inr tt) = inl refl

-- -- -- shift-Seq' :
-- -- --   {R : Type₀} {E : Type₀}
-- -- --   → (t : E → Seq-tree R E)
-- -- --   --------------
-- -- --   → Seq-tree R E
-- -- -- shift-Seq' t =
-- -- --   λ e →
-- -- --     [⟩ inr tt , fst (t (e 0) (e ∘ suc)) ⟨] ,
-- -- --     λ {0 → never⊑ (fst (t (e 0) (e ∘ suc)) 0) 
-- -- --       ;(suc n) → snd (t (e 0) (e ∘ suc)) n }

-- -- -- -- Seq→tree : {!!}
-- -- -- -- Seq→tree s = {!!}

-- -- -- tree→Seq : ∀ {R} {E} → tree R E → Seq-tree R E
-- -- -- tree→Seq (tree-leaf r) = λ _ → (λ _ → inl r) , (λ _ → inl refl)
-- -- -- tree→Seq (tree-node k) = shift-Seq' λ e → tree→Seq (force (k e))

-- -- -- unshift-Seq :
-- -- --   {R : Type₀} {E : Type₀}
-- -- --   → Seq-tree R E
-- -- --   → E
-- -- --   --------------
-- -- --   → Seq-tree R E
-- -- -- unshift-Seq se v = λ e → fst (se [⟩ v , e ⟨]) ∘ suc , snd (se [⟩ v , e ⟨]) ∘ suc

-- -- -- asfd : ∀ {R E} (e : E → Seq-tree R E) (v : E) → unshift-Seq (shift-Seq' e) v ≡ e v
-- -- -- asfd e v = refl

-- -- -- -- postulate
-- -- -- --   never⊑ : {R : Type₀} (x : R ⊎ Unit) → inr tt ⊑maybe x
-- -- -- -- -- never⊑ = {!!}

-- -- -- -- asfd' : ∀ {R E} (s : Seq-tree R E) (e : ℕ → E) →
-- -- -- --   (shift-Seq' (unshift-Seq λ x → {!!})) e ≡ s e
-- -- -- -- asfd' s e =
-- -- -- --   shift-Seq' (unshift-Seq s) e
-- -- -- --     ≡⟨ ΣPathP ((funExt λ {0 → refl ; (suc n) → refl}) ,
-- -- -- --        λ {i 0 → never⊑ (fst (unshift-Seq s (e 0) (e ∘ suc)) 0)
-- -- -- --          ;i (suc n) → snd (unshift-Seq s (e 0) (e ∘ suc)) n}) ⟩
-- -- -- --   ([⟩ inr tt , fst ((unshift-Seq s) (e 0) (e ∘ suc)) ⟨] ,
-- -- -- --     λ {0 → never⊑ (fst ((unshift-Seq s) (e 0) (e ∘ suc)) 0) 
-- -- -- --       ;(suc n) → snd ((unshift-Seq s) (e 0) (e ∘ suc)) n })
-- -- -- --     ≡⟨ ΣPathP ((funExt (λ { 0 → refl ; (suc n) → {!!} })) , λ {i 0 → never⊑ (fst (unshift-Seq s (e 0) (e ∘ suc)) 0) ; i (suc n) → {!!}}) ⟩
-- -- -- --   ([⟩ inr tt , fst (s [⟩ (e 1) , (e ∘ suc) ⟨]) ∘ suc ⟨] ,
-- -- -- --     λ {0 → never⊑ ((fst (s [⟩ ((e ∘ suc) 0) , (e ∘ suc) ⟨]) ∘ suc) 0) 
-- -- -- --       ;(suc n) → (snd (s [⟩ ((e ∘ suc) 0) , (e ∘ suc) ⟨]) ∘ suc) n })
-- -- -- --     ≡⟨ {!!} ⟩
-- -- -- --   ([⟩ inr tt , fst (s (e ∘ suc)) ⟨] ,
-- -- -- --     λ {0 → never⊑ (fst (s (e ∘ suc)) 0)
-- -- -- --       ;(suc n) → snd (s (e ∘ suc)) n} ) 
-- -- -- --     ≡⟨ {!!} ⟩ -- only true if inr tt ...
-- -- -- --   s e ∎


-- -- -- -- (λ {0 → (case fst ((unshift-Seq s) (e 0) (e ∘ suc)) 0 return (λ x → inr tt ⊑maybe x) of λ { (inl r) → inr (refl , inl≢inr) ; (inr tt) → inl refl }) ;(suc n) → snd ((unshift-Seq s) (e 0) (e ∘ suc)) n })

-- -- -- -- mutual
-- -- -- --   helper : {R : Type₀} {E : Type₀} → (E → ∞tree R E) → E → tree R E
-- -- -- --   helper = _∘_ force

-- -- -- --   ∞tree→Seq-tree : {R : Type₀} {E : Type₀} → (E → ∞tree R E) → Seq-tree R E
-- -- -- --   s (∞tree→Seq-tree k) e = s (tree→Seq-tree (helper k (e 0))) (e ∘ suc)
-- -- -- --   q (∞tree→Seq-tree k) e = q (tree→Seq-tree (helper k (e 0))) (e ∘ suc)
  
-- -- -- --   tree→Seq-tree : {R : Type₀} {E : Type₀} → tree R E → Seq-tree R E
-- -- -- --   s (tree→Seq-tree (tree-leaf r)) _ _ = inl r
-- -- -- --   q (tree→Seq-tree (tree-leaf r)) _ _ = inl refl
-- -- -- --   tree→Seq-tree (tree-node k) = shift-Seq' (∞tree→Seq-tree k)
  
-- -- --     -- shift-Seq (∞tree→Seq-tree k)
-- -- --     --   (λ e →
-- -- --     --     (inr tt) ,
-- -- --     --     (case fst (cons (∞tree→Seq-tree k) e) 0 return (λ x → inr tt ⊑maybe x)
-- -- --     --        of λ {(inl r) → inr (refl , inl≢inr)
-- -- --     --             ;(inr tt) → inl refl}))
