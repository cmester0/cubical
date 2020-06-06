{-# OPTIONS --cubical --guardedness #-}

module Cubical.Codata.M.AsLimit.QIIT-examples where

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Bool

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude

open import Cubical.Codata.M.AsLimit.Container
open import Cubical.Codata.M.AsLimit.M
open import Cubical.Codata.M.AsLimit.helper

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients renaming (rec to rec/ ; elim to elim/)
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥map∥ ; rec to ∥rec∥ ; elim to ∥elim∥)

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

Wₙ' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) -> ℕ -> Type ℓ
Wₙ' S R 0 = Lift Unit
Wₙ' S R (suc n) = P₀-Q S R (Wₙ' S R n)

πₙ' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) -> {n : ℕ} -> Wₙ' S R (suc n) -> Wₙ' S R n
πₙ' _ _ _ {0} _ = lift tt
πₙ' S R R-comm {suc n} = P₁-Q S R R-comm (πₙ' S R R-comm {n})

sequence' : ∀ {ℓ} -> (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) -> Chain ℓ
X (sequence' S R R-comm) n = Wₙ' S R n
π (sequence' S R R-comm) {n} = πₙ' S R R-comm {n}

QM : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Type ℓ
QM S R R-comm = limit-of-chain (sequence' S R R-comm)

poly-quot : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Set (ℓ-suc ℓ)
poly-quot {ℓ} S R R-comm =
  Σ[ abs ∈ ({X : Set ℓ} → P₀ S X → P₀-Q S R X) ]
    ((∀ {X} → isSurjection (abs {X})) × ({X Y : Set ℓ} (f : X → Y) (x : P₀ S X) → abs (P₁ f x) ≡ P₁-Q S R R-comm f (abs x))) -- Is one of these properties not enought?

-- postulate
--   shift-quotient : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → Iso (QM S R R-comm) (P₀-Q S R (QM S R R-comm))


function : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → {X : Type ℓ} → (a : S .fst) → (S .snd a → X) / R → S .snd a → ∥ X ∥
function S R a f' x = ∥map∥ (λ {(f , _) → f x}) ([]surjective f')

  -- P₀ S (M S)
  --    Iso⟨ Σ-ap-iso₂ (λ x → iso (λ f → (λ n z → f z .fst n) , λ n i a → f a .snd n i)
  --                              (λ (u , q) z → (λ n → u n z) , λ n i → q n i z)
  --                              (λ _ → refl)
  --                              (λ _ → refl)) ⟩
  -- (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → X (sequence S) n) ] ((n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)))
  --   Iso⟨ invIso α-iso-step-5-Iso ⟩
  -- (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
  --       Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
  --          ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
  --                              (πₙ S ∘ u (suc n))
  --                              (u n)))
  --     Iso⟨ α-iso-step-1-4-Iso-lem-12 ⟩
  -- M S ∎Iso

function' : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → {X : Type ℓ} → (a : S .fst) → isProp (S .snd a → X) → (S .snd a → X) / R → S .snd a → X
function' S R a  prop f' = ∥rec∥ (prop) (λ x → x) (∥map∥ fst ([]surjective f'))

remove-double : {ℓ : Level} {A : Type ℓ} → ∥ ∥ A ∥ ∥ → ∥ A ∥
remove-double {A = A} = ∥rec∥ propTruncIsProp (λ (x : ∥ A ∥) → x)

-- shift-quotient-iso : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm → Iso (P₀-Q S R (QM S R R-comm)) (QM S R R-comm) 



shift-quotient-pre : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm → M S → P₀-Q S R (M S)
shift-quotient-pre S@(A , B) R R-comm (abs , (comm , sqr)) x = abs (out-fun x)

shift-quotient-pre'2 : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm → P₀-Q S R (M S) → P₀-Q S R (QM S R R-comm)
shift-quotient-pre'2 S@(A , B) R R-comm (abs , (comm , sqr)) x = {!!}

shift-quotient-iso : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm → Iso (Σ[ a ∈ S .fst ] (S .snd a → QM S R R-comm)) (QM S R R-comm)
shift-quotient-iso S@(A , B) R R-comm (abs , (comm , sqr))  =
  iso
    (λ x → {!!})
    {!!}
    {!!}
    {!!}

-- shift-quotient-iso : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm → Iso (Σ[ a ∈ S .fst ] (S .snd a → QM S R R-comm)) (QM S R R-comm) 
-- shift-quotient-iso S@(A , B) R R-comm (abs , (comm , sqr))  = -- (B (fst (x .fst (suc n))) → Wₙ' (A , B) R n)
--   (Σ[ a ∈ A ] (((B a → (QM S R R-comm))) ))
--     Iso⟨ Σ-ap-iso₂ (λ a → iso (λ f → (λ n z → f z .fst n) , (λ n i a → f a .snd n i))
--                                (λ {(u , q) z → (λ n → u n z) , (λ n i → q n i z)})
--                               (λ _ → refl)
--                               λ _ → refl) ⟩
--   (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → (B a → Wₙ' S R n)) ] ((n : ℕ) → πₙ' S R R-comm ∘ u (suc n) ≡ u n )))
--     Iso⟨ invIso α-iso-step-5-Iso ⟩
--   (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
--         Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S R n) ]
--            ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S R n)
--                                (πₙ' S R R-comm ∘ u (suc n))
--                                (u n)))
--     Iso⟨ iso (λ {((a , d) , b , c) → (λ n → b (suc n) {!!}) , (λ n i → {!!})})
--             {!!}
--             {!!}
--             {!!} ⟩
--   (Σ[ x ∈ ((n : ℕ) → Wₙ' S R (suc n)) ] ((n : ℕ) → πₙ' S R R-comm (x (suc n)) ≡ x n))
--     Iso⟨ sdfa ⟩ -- α-iso-step-1-4-Iso-lem-12
--   Σ[ u ∈ ((n : ℕ) → Wₙ' S R n) ] ((n : ℕ) → πₙ' S R R-comm (u (suc n)) ≡ u n) ∎Iso
--   where
--   open Iso

--   postulate
--     acc : {!!}

--   α-iso-step-1-4 :
--     Iso (limit-of-chain (shift-chain (sequence' S R R-comm)))
--         (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
--         (Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S R n) ]
--            ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S R n) (πₙ' S R R-comm ∘ u (suc n)) (u n))))
--   α-iso-step-1-4 =
--     (iso
--       (λ a →
--         ((λ n → a .fst n .fst) , (λ n i → a .snd n i .fst)) ,
--         ((λ n → {!!}) , (λ n x₁ → {!!}))) -- a .fst n .snd -- a .snd n x₁ .snd
--       (λ a →
--         (λ n → (a .fst .fst n) , [ (a .snd .fst n) ]) ,
--         (λ n i → a .fst .snd n i , [ a .snd .snd n i ]))
--       (λ b → refl)
--       (λ a → {!!}))
      
--   sdfa : Iso (limit-of-chain (shift-chain (sequence' S R R-comm))) (limit-of-chain (sequence' S R R-comm))
--   sdfa =
--     iso (λ x → (λ {0 → lift tt ; (suc n) -> x .fst n}) , (λ { 0 → refl {x = lift tt} ; (suc n) → x .snd n }))
--         (λ x → x .fst ∘ suc , x .snd ∘ suc)
--         (λ {(b , c) → ΣPathP (funExt (λ { 0 → refl ; (suc n) → refl }) , λ {i 0 → refl ; i (suc n) → c (suc n)})})
--         (λ a → ΣPathP (refl , refl))

--   α-iso-step-5-Iso-helper0 :
--     ∀ (a,p : Σ[ a ∈ (ℕ -> A)] ((n : ℕ) → a (suc n) ≡ a n))
--     → (n : ℕ)
--     → a,p .fst n ≡ a,p .fst 0
--   α-iso-step-5-Iso-helper0 _ 0 = refl
--   α-iso-step-5-Iso-helper0 (a , p) (suc n) = p n ∙ α-iso-step-5-Iso-helper0 (a , p) n

--   α-iso-step-5-Iso-helper1-Iso :
--           ∀ (a,p : Σ[ a ∈ (ℕ -> A)] ((n : ℕ) → a (suc n) ≡ a n))
--           → (u : (n : ℕ) → B (a,p .fst n) → Wₙ' S R n)
--           → (n : ℕ)
--           → Iso (PathP (λ x → B (a,p .snd n x) → Wₙ' S R n) (πₙ' S R R-comm ∘ u (suc n)) (u n))
--               (πₙ' S R R-comm ∘ (subst (\k -> B k → Wₙ' S R (suc n)) (α-iso-step-5-Iso-helper0 a,p (suc n))) (u (suc n)) ≡ subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (u n))
--   α-iso-step-5-Iso-helper1-Iso  a,p@(a , p) u n  =
--          PathP (λ x → B (p n x) → Wₙ' S R n) (πₙ' S R R-comm ∘ u (suc n)) (u n)
--            Iso⟨ pathToIso (PathP≡Path (λ x → B (p n x) → Wₙ' S R n) (πₙ' S R R-comm ∘ u (suc n)) (u n)) ⟩
--          subst (λ k → B k → Wₙ' S R n) (p n) (πₙ' S R R-comm ∘ u (suc n)) ≡ (u n)
--            Iso⟨ (invIso (temp sfad)) ⟩
--          (subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (subst (λ k → B k → Wₙ' S R n) (p n) (πₙ' S R R-comm ∘ u (suc n)))
--                 ≡
--          subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (u n))
--            Iso⟨ pathToIso (λ i → (sym (substComposite (λ k → B k → Wₙ' S R n) (p n) (α-iso-step-5-Iso-helper0 a,p n) (πₙ' S R R-comm ∘ u (suc n)))) i
--                              ≡ subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (u n)) ⟩
--          subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p (suc n)) (πₙ' S R R-comm ∘ u (suc n))
--            ≡
--          subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (u n)
--            Iso⟨ pathToIso (λ i → (substCommSlice (λ k → B k → Wₙ' S R (suc n)) (λ k → B k → Wₙ' S R n) (λ a x x₁ → (πₙ' S R R-comm) (x x₁)) ((α-iso-step-5-Iso-helper0 a,p) (suc n)) (u (suc n))) i
--                           ≡ subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (u n)) ⟩
--          πₙ' S R R-comm ∘ subst (λ k → B k → Wₙ' S R (suc n)) (α-iso-step-5-Iso-helper0 a,p (suc n)) (u (suc n))
--            ≡
--          subst (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n) (u n) ∎Iso
--          where
--            abstract
--              temp = iso→fun-Injection-Iso-x

--            private
--              sfad : Iso (B (a n) → Wₙ' S R n) (B (a 0) → Wₙ' S R n)
--              sfad = (pathToIso (cong (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n)))
           
--   α-iso-step-5-Iso :
--          Iso
--            (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
--              Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S R n) ]
--                ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S R n)
--                                    (πₙ' S R R-comm ∘ u (suc n))
--                                    (u n)))
--              (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → Wₙ' S R n) ] ((n : ℕ) → πₙ' S R R-comm ∘ (u (suc n)) ≡ u n)))
--   α-iso-step-5-Iso =
--     Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) (λ a,p →
--     Σ-ap-iso (pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → B k → Wₙ' S R n) (α-iso-step-5-Iso-helper0 a,p n)))) λ u →
--               pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → isoToPath (α-iso-step-5-Iso-helper1-Iso a,p u n))))

  -- α-iso-step-1-4-Iso-lem-12 :
  --       Iso (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A)] ((n : ℕ) → a (suc n) ≡ a n)) ]
  --                 (Σ[ u ∈ ((n : ℕ) → B (a .fst n) → Wₙ' S R n) ]
  --                     ((n : ℕ) → PathP (λ x → B (a .snd n x) → Wₙ' S R n)
  --                                         (πₙ' S R R-comm ∘ u (suc n))
  --                                         (u n))))
  --           (limit-of-chain ((λ x → Wₙ' S R {!!}) ,, {!!}))
  -- fun α-iso-step-1-4-Iso-lem-12 (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , [ b .fst n ]}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , [ b .snd m i ] }
  -- inv α-iso-step-1-4-Iso-lem-12 x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → x .fst (suc n) .snd) , λ n i → x .snd (suc n) i .snd
  
  -- fun α-iso-step-1-4-Iso-lem-12 (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i }
  -- inv α-iso-step-1-4-Iso-lem-12 x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → (x .fst) (suc n) .snd) , λ n i → (x .snd) (suc n) i .snd
  -- fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = lift tt
  -- fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = refl i
  -- snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = refl
  -- snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = c (suc n)
  -- leftInv α-iso-step-1-4-Iso-lem-12 (a , b) = refl

-- shift : ∀ {ℓ} (S : Container ℓ) -> P₀ S (M S) ≡ M S
-- shift S = isoToPath (shift-iso S) -- lemma 13 & lemma 12


-- Q-in-fun : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → (P₀-Q S R (QM S R R-comm)) → (QM S R R-comm)
-- Q-in-fun S R R-comm x = Iso.fun (shift-quotient-iso S R R-comm {!!} {!!}) x

-- Q-out-fun : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → (QM S R R-comm) → (P₀-Q S R (QM S R R-comm))
-- Q-out-fun S R R-comm x = Iso.inv (shift-quotient-iso S R R-comm {!!} {!!}) x

-- M→QM : ∀ {ℓ} → (S : Container ℓ) → (R : ({X : Type ℓ} {a : S .fst} → (S .snd a → X) → (S .snd a → X) → Type ℓ)) → (R-comm : (∀ {X Y} → (f : X → Y) → {a : S .fst} → {x y : S .snd a → X} → R x y → R (f ∘ x) (f ∘ y))) → poly-quot S R R-comm → M S → QM S R R-comm
-- M→QM S R R-comm (abs , (sur , comm)) x = let temp' = comm abs {!!} in let temp = (abs (out-fun x)) in  Q-in-fun S R R-comm (abs {!!})


-- -- Weak bisimularity for delay monad
-- ∼perm' : {R : Type₀} {X : Type₀} {a : tree-S R .fst} → (tree-S R .snd a → X) → (tree-S R .snd a → X) → Type₀
-- ∼perm' {a = inr tt} f h = Σ[ g ∈ (ℕ → ℕ) ] (isEquiv g × (f ∘ g ≡ h))
-- ∼perm' {a = inl r} _ _ = Unit -- always true

-- ∼perm'-comm :  {R : Type₀} {X Y : Type₀} (f : X → Y) {a : tree-S R .fst} → {x y : tree-S R .snd a → X} → ∼perm' x y → ∼perm' (f ∘ x) (f ∘ y)
-- ∼perm'-comm f {a = inr tt} p = (p .fst) , ((proj₁ (p .snd)) , cong (λ a → f ∘ a) (proj₂ (p .snd)))

-- ∼perm'-comm f {a = inl r} tt = tt

-- asdf : ∀ {R} → poly-quot (tree-S R) ∼perm' ∼perm'-comm
-- asdf {R = R} =
--   (λ {(inl r , b) → inl r , [ b ] ; (inr tt , f) → inr tt , [ f ]}) ,
--   (λ {(inl r , b) → ∥map∥ (λ {(v , p) → (inl r , v) , (ΣPathP (refl , p))}) ([]surjective b)
--      ;(inr tt , f) → ∥map∥ (λ {(g , p) → (inr tt , g) , ((inr tt , [ g ]) ≡⟨ ΣPathP (refl , p) ⟩ (inr tt , f) ∎)}) ([]surjective f) }) ,
--   λ {f (inl r , b) → refl
--     ;f (inr tt , g) → refl}


