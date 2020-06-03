{-# OPTIONS --cubical --guardedness --safe #-}

module Cubical.Codata.M.AsLimit.QIIT-examples where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients renaming (rec to rec/ ; elim to elim/)
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥)

-- Delay monad defined as an M-type
tree-S : (R : Type₀) -> Container ℓ-zero
tree-S R = (R ⊎ Unit) , λ { (inl _) -> ⊥ ; (inr tt) -> ℕ }

tree : (R : Type₀) -> Type₀
tree R = M (tree-S R)

leaf : {R : Type₀} -> R -> tree R
leaf r = in-fun (inl r , λ ())

node : {R : Type₀} -> (ℕ → tree R) -> tree R
node f = in-fun (inr tt , f)

-- Weak bisimularity for delay monad
data _∼_ {R : Type₀} : (_ _ : tree R) → Type₀ where
  ∼now : ∀ (s r : R) → s ≡ r → leaf s ∼ leaf r
  ∼later : ∀ f g → (∀ n → f n ∼ g n) → node f ∼ node g
  ∼perm : ∀ f (g : ℕ → ℕ) → isEquiv g → node f ∼ node (f ∘ g)

Quotient-Container : ∀ {ℓ} → (S : Container ℓ) → (G : S .fst → Set ℓ) → Container ℓ
Quotient-Container (A , B) G = A , λ a → B a → G a

P₀-Q : ∀ {ℓ} → (S : Container ℓ) → ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ) → Type ℓ → Type ℓ
P₀-Q (A , B) ∼ₛ X = Σ[ a ∈ A ] ((B a → X) / ∼ₛ {a = a})

P₁-Q :
  ∀ {ℓ} → (S : Container ℓ) → {X Y : Type ℓ}
  → (∼ₛ : {X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)
  → (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → ∼ₛ x y → ∼ₛ (f ∘ x) (f ∘ y))
  → (f : X → Y)
  → P₀-Q S ∼ₛ X → P₀-Q S ∼ₛ Y
P₁-Q S {X = X} {Y = Y} ∼ₛ ∼ₛ-comp f (a , g) =
  a ,
  elim/
    {A = S .snd a → X}
    {R = ∼ₛ}
    {B = λ _ → (S .snd a → Y) / ∼ₛ}
    (λ x → squash/)
    (λ g → [ f ∘ g ])
    (λ x y r → eq/ (f ∘ x) (f ∘ y) (∼ₛ-comp f r))
    g

poly-quot' : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Set (ℓ-suc ℓ)
poly-quot' {ℓ} S R R-comm =
  Σ[ abs ∈ ({X : Set ℓ} → P₀ S X → P₀-Q S R X) ]
    ((∀ {X} → isSurjection (abs {X})) × ({X Y : Set ℓ} (f : X → Y) (x : P₀ S X) → abs (P₁ f x) ≡ P₁-Q S R R-comm f (abs x)))

poly-quot : ∀ {ℓ} → (S : Container ℓ) → Set (ℓ-suc ℓ)
poly-quot {ℓ} S =
  Σ[ F₀ ∈ (Type ℓ -> Type ℓ)]
  Σ[ F₁ ∈ ({X Y : Set ℓ} (f : X → Y) → F₀ X → F₀ Y)]
  Σ[ abs ∈ ({X : Set ℓ} → P₀ S X → F₀ X) ]
    ((∀ {X} → isSurjection (abs {X})) × ({X Y : Set ℓ} (f : X → Y) (x : P₀ S X) → abs (P₁ f x) ≡ F₁ f (abs x)))

-- Weak bisimularity for delay monad
∼perm' : {R : Type₀} {X : Type₀} {a : tree-S R .fst} → (tree-S R .snd a → X) → (tree-S R .snd a → X) → Type₀
∼perm' {a = inr tt} f h = Σ[ g ∈ (ℕ → ℕ) ] (isEquiv g × (f ∘ g ≡ h))
∼perm' {a = inl r} _ _ = Unit -- always true

∼perm'-comm :  {R : Type₀} {X Y : Type₀} (f : X → Y) {a : tree-S R .fst} → {x y : tree-S R .snd a → X} → ∼perm' x y → ∼perm' (f ∘ x) (f ∘ y)
∼perm'-comm f {a = inr tt} p = (p .fst) , ((proj₁ (p .snd)) , λ i → f ∘ proj₂ (p .snd) i)
∼perm'-comm f {a = inl r} tt = tt

asdf : ∀ {R} → poly-quot' (tree-S R) ∼perm' ∼perm'-comm
asdf {R = R} =
  (λ {(inl r , b) → inl r , [ b ] ; (inr tt , f) → inr tt , [ f ]}) ,
  (λ {(inl r , b) → ∥map∥ (λ {(v , p) → (inl r , v) , (ΣPathP (refl , p))}) ([]surjective b)
     ;(inr tt , f) → ∥map∥ (λ {(g , p) → (inr tt , g) , ((inr tt , [ g ]) ≡⟨ ΣPathP (refl , p) ⟩ (inr tt , f) ∎)}) ([]surjective f) }) ,
  λ {f (inl r , b) → refl
    ;f (inr tt , g) → refl}

-- TODO: Take the limit!

delay-conta : ∀ {R} → Container ℓ-zero
delay-conta {R = R} =
  Quotient-Container (tree-S R) λ x → ⊥

-- Trivial Quotient
asfdhtr : ∀ {R} → poly-quot (tree-S R)
asfdhtr {R} = P₀ (tree-S R) , P₁ , {!!}

-- -- -- Weak bisimularity for delay monad
-- -- data _∼_ {R : Type₀} : (_ _ : tree R) → Type₀ where
-- --   ∼now : ∀ (s r : R) → s ≡ r → leaf s ∼ leaf r
-- --   ∼later : ∀ f g → (∀ n → f n ∼ g n) → node f ∼ node g
-- --   ∼perm : ∀ f (g : ℕ → ℕ) → isEquiv g → node f ∼ node (f ∘ g)

-- F₀' : {R : Type₀} → Type₀ → Type₀
-- F₀' {R = R} X =
--   Σ (tree-S R .fst) λ {(inl r) → ⊥ → X
--                       ;(inr tt) → Σ[ f ∈ (ℕ → X) ] ((g : ℕ → ℕ) → isEquiv g → (Σ[ v ∈ ((ℕ -> X) → X) ] (v f ≡ v (f ∘ g))))}

-- F₁' : ∀ {R : Type₀} {X Y : Type₀} (f : X -> Y) -> F₀' {R = R} X -> F₀' {R = R} Y
-- F₁' {R = R} {Y = Y} a ((inl r) , b) = inl r , λ ()
-- F₁' {R = R} {Y = Y} a ((inr tt) , (f , p)) = inr tt , (a ∘ f , λ g e → (λ h → a (p g e .fst f)) , refl)

-- -- Only at the level of containers
-- asfdhtr' : ∀ {R} → poly-quot (tree-S R)
-- asfdhtr' {R} =
--   F₀' {R = R} , F₁' ,
--   ((λ {(inl r , b) → inl r , (λ ()) ; (inr tt , f) → inr tt , (f , λ g e → (λ _ → f 0) , refl)})
--   ,((λ {(inl r , b) → ∣ (inl r , b) , ΣPathP (refl , isContr→isProp isContr⊥→A (λ ()) b) ∣
--        ;(inr tt , (f , p)) → ∣ (inr tt , f) , ΣPathP (refl , ΣPathP (refl , {!!})) ∣}) ,
--   {!!}))



-- F₀' : {R : Type₀} → Type₀ → Type₀
-- F₀' {R = R} X = Σ (tree-S R .fst) λ {(inl r) → ⊥ → X ; (inr tt) → Σ[ f ∈ (ℕ → X) ] Σ (ℕ → ℕ) (λ g → isEquiv g × (f ≡ f ∘ g))}

-- F₁' : ∀ {R : Type₀} {X Y : Type₀} (f : X -> Y) -> F₀' {R = R} X -> F₀' {R = R} Y
-- F₁' {R = R} {Y = Y} a ((inl r) , b) = inl r , λ ()
-- F₁' {R = R} {Y = Y} a ((inr tt) , (f , g , e , p)) = inr tt , (a ∘ f , (g , (e , λ i → a ∘ (p i))))

-- -- Only at the level of containers
-- asfdhtr' : ∀ {R} → poly-quot (tree-S R)
-- asfdhtr' {R} =
--   F₀' {R = R} , F₁' ,
--   ((λ {(inl r , b) → inl r , (λ ()) ; (inr tt , f) → inr tt , (f , idEquiv ℕ .fst , ((idEquiv ℕ .snd) , refl))})
--   ,((λ {(inl r , b) → ∣ (inl r , b) , ΣPathP (refl , isContr→isProp isContr⊥→A (λ ()) b) ∣
--        ;(inr tt , (f , g , e , p)) → ∣ (inr tt , f) , ΣPathP (refl , (ΣPathP (refl , ΣPathP ({!!} , {!!})))) ∣}) ,
--   {!!}))

-- b→T : ∀ {X} → b X → T X
-- b→T (leaf x) = leaf x
-- b→T (node f) = node (b→T ∘ f)

-- b→T-∼→≡ : ∀ {X} {x y : b X} → x ∼ y → b→T x ≡ b→T y
-- b→T-∼→≡ (∼leaf p) = cong (b→T ∘ leaf) p
-- b→T-∼→≡ {X} (∼node {f} {g} p) = cong {B = λ _ → T X} node (funExt (b→T-∼→≡ ∘ p))
-- b→T-∼→≡ (∼perm f g e) = perm (b→T ∘ f) g e

-- recc :
--   ∀ {A B : Set} {R : A → A → Set} →
--   (f : A → B) →
--   (∀ x y → R x y → f x ≡ f y) →
--   isSet B →
--   A / R → B
-- recc {A} {B} {R} f feq B-set ar =
--   Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar

-- b/∼→T : ∀ {X} → b X / _∼_ → T X
-- b/∼→T = recc b→T (λ _ _ → b→T-∼→≡) T-isSet

-- sequence' : ∀ {ℓ} -> Type ℓ → Container ℓ -> Chain ℓ
-- X (sequence' X S) n = Wₙ S n
-- π (sequence' X S) {n} = πₙ S {n}

-- -- Only at the level of containers
-- asfdhtr' : ∀ {R} → poly-quot (tree-S R)
-- asfdhtr' {R} = F₀' {R = R} , F₁' , ((λ {(a , b) → (λ x → let temp = πₙ (tree-S R) (x .fst , {!!}) in {!!}) , {!!}}) , {!!}) -- π {!!} {!!}

-- ∀ f (g : ℕ → ℕ) → isEquiv g → node f ∼ node (f ∘ g)

-- λ { (a , g) ->  a , f ∘ g }
