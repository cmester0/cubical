{-# OPTIONS --cubical --guardedness --safe #-}

-- Construction of M-types from
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

module Cubical.Codata.M.AsLimit.M.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Nat as ℕ using (ℕ ; suc ; _+_ )
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Nat.Algebra

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sum

open import Cubical.Codata.M.AsLimit.helper
open import Cubical.Codata.M.AsLimit.Container

open import Cubical.Codata.M.AsLimit.Coalg.Base

open Iso

private
  limit-collapse : ∀ {ℓ} {S : Container ℓ} (X : ℕ → Type ℓ) (l : (n : ℕ) → X n → X (suc n)) → (x₀ : X 0) → ∀ (n : ℕ) → X n
  limit-collapse X l x₀ 0 = x₀
  limit-collapse {S = S} X l x₀ (suc n) = l n (limit-collapse {S = S} X l x₀ n)

lemma11-Iso :
  ∀ {ℓ} {S : Container ℓ} (X : ℕ → Type ℓ) (l : (n : ℕ) → X n → X (suc n))
  → Iso (Σ[ x ∈ ((n : ℕ) → X n)] ((n : ℕ) → x (suc n) ≡ l n (x n)))
         (X 0)
fun (lemma11-Iso X l) (x , y) = x 0
inv (lemma11-Iso {S = S} X l) x₀ = limit-collapse {S = S} X l x₀ , (λ n → refl {x = limit-collapse {S = S} X l x₀ (suc n)})
rightInv (lemma11-Iso X l) _ = refl
leftInv (lemma11-Iso {ℓ = ℓ} {S = S} X l) (x , y) i =
  let temp = χ-prop (x 0) (fst (inv (lemma11-Iso {S = S} X l) (fun (lemma11-Iso {S = S} X l) (x , y))) , refl , (λ n → refl {x = limit-collapse {S = S} X l (x 0) (suc n)})) (x , refl , y)
  in temp i .fst , proj₂ (temp i .snd)
  where
    open AlgebraPropositionality
    open NatSection
    open NatFiber

    X-fiber-over-ℕ : (x₀ : X 0) -> NatFiber NatAlgebraℕ ℓ
    Fiber (X-fiber-over-ℕ x₀) = X
    fib-zero (X-fiber-over-ℕ x₀) = x₀
    fib-suc (X-fiber-over-ℕ x₀) {n} xₙ = l n xₙ

    X-section : (x₀ : X 0) → (z : Σ[ x ∈ ((n : ℕ) → X n)] (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n))) -> NatSection (X-fiber-over-ℕ x₀)
    NatSection.section (X-section x₀ z) = fst z
    sec-comm-zero (X-section x₀ z) = proj₁ (snd z)
    sec-comm-suc (X-section x₀ z) = proj₂ (snd z)

    Z-is-Section : (x₀ : X 0) →
      Iso (Σ[ x ∈ ((n : ℕ) → X n)] (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
          (NatSection (X-fiber-over-ℕ x₀))
    NatSection.section (fun (Z-is-Section x₀) (x , (z , y))) = x
    sec-comm-zero (fun (Z-is-Section x₀) (x , (z , y))) = z
    sec-comm-suc (fun (Z-is-Section x₀) (x , (z , y))) = y
    inv (Z-is-Section x₀) x = NatSection.section x , (sec-comm-zero x , sec-comm-suc x)
    rightInv (Z-is-Section x₀) _ = refl
    leftInv (Z-is-Section x₀) (x , (z , y)) = refl

    -- S≡T
    χ-prop' : (x₀ : X 0) → isProp (NatSection (X-fiber-over-ℕ x₀))
    χ-prop' x₀ a b = SectionProp.S≡T isNatInductiveℕ (X-section x₀ (inv (Z-is-Section x₀) a)) (X-section x₀ (inv (Z-is-Section x₀) b))

    χ-prop : (x₀ : X 0) → isProp (Σ[ x ∈ ((n : ℕ) → X n) ] (x 0 ≡ x₀) × (∀ n → (x (suc n)) ≡ l n (x n)))
    χ-prop x₀ =  λ a b → fun (iso→fun-Injection-Iso-x (Z-is-Section x₀)) (χ-prop' x₀ (fun (Z-is-Section x₀) a) (fun (Z-is-Section x₀) b))
    -- subst isProp (sym (isoToPath (Z-is-Section x₀))) (χ-prop' x₀)

-----------------------------------------------------
-- Shifting the limit of a chain is an equivalence --
-----------------------------------------------------

-- mutual
--   private
--     shift-iso'-fun-x : ∀ {ℓ} (S : Container ℓ) → (k : P₀ S (M S)) → (n : ℕ) → Wₙ S n
--     shift-iso'-fun-x S =
--       λ { _ 0 → lift tt
--         ; k (suc n) → k .fst , (λ x₁ → shift-iso'-fun-x S (inv (shift-iso' S) (k .snd x₁)) n) }
    
--   shift-iso' : ∀ {ℓ} (S : Container ℓ) -> Iso (P₀ S (M S)) (M S)
--   fun (shift-iso' {ℓ} S@(A , B)) (x , y) =
--     {!!} ,
--     {!!}
--     where
--       Wₙ' : (ℕ → A) → ℕ -> Type ℓ
--       Wₙ' a 0 = Lift Unit
--       Wₙ' a (suc n) = (B (a n) → Wₙ' a n) -- Σ[ a ∈ A ] (B a -> X)

--       -- asfd : (n : ℕ) → Wₙ' (λ n → x) n → Wₙ

--       temp : (n : ℕ) → Wₙ' (λ n → x) n
--       temp 0 = lift tt
--       temp 1 = λ k → lift tt
--       temp (suc (suc n)) = λ k → temp (suc n) (y k .fst (suc n) .fst)

--       temp' : (n : ℕ) → Wₙ S n
--       temp' 1 = x , λ k → y k .fst 0
--   inv (shift-iso' {ℓ} S@(A , B)) x = (x .fst 1 .fst) , λ k → (λ {0 → lift tt ; (suc 0) → {!!}}) , {!!} --  , λ k → temp , ? -- temp'
--     where
--       temp : (n : ℕ) → B (x .fst (suc n) .fst) → Wₙ S (suc n)
--       temp n k  = (x .fst (suc (suc n)) .fst) , (λ _ → x .fst (suc n) .snd k)

--       -- temp' : (n : ℕ) → B (x .fst (suc 0) .fst) → Wₙ (PX,Pπ S) n
--       -- temp' 0 k = lift tt
--       -- temp' (suc 0) k = (x .fst (suc (suc 0)) .fst) , (λ x₁ → x .fst (suc 0) .snd k)
--       -- temp' (suc 1) k = {!!}

--       -- x .fst (suc n) .fst , λ k → x .fst {!!} .snd {!!}
--       -- temp' : (n : ℕ) → πₙ S (temp (suc n)) ≡ temp n
--       -- temp' 0 = refl
--       -- temp' (suc n) i = (x .snd (suc (suc n)) i .fst) , λ _ → temp' n i
--   rightInv (shift-iso' S@(A , B)) b = {!!}
--     -- fun (shift-iso' S) (inv (shift-iso' S) b)
--     --   ≡⟨ refl ⟩
--     -- fun (shift-iso' S) (b .fst 1 .fst , λ k → b)
--     --   ≡⟨ ΣPathP ((funExt (λ {0 → refl ; (suc n) → refl})) , λ {i 0 → refl ; i (suc n) → {!!}}) ⟩
--     -- (λ {0 → lift tt ; (suc n) → b .fst 1 .fst , λ k → b .fst n}) ,
--     -- (λ {0 → refl ; (suc n) i → {!!}}) -- b .fst 1 .fst , λ k → b .snd n i
--     --   ≡⟨ ΣPathP (funExt (λ {0 → refl ; (suc n) → ΣPathP ((b .fst 1 .fst ≡⟨ temp n ⟩ b .fst (suc n) .fst ∎) , {!!})}) , {!!}) ⟩
--     -- (λ {0 → lift tt ; (suc n) → b .fst (suc n) .fst , λ k → b .fst (suc n) .snd k}) ,
--     -- (λ {0 → refl ; (suc n) i → b .snd (suc n) i .fst , λ k → b .snd (suc n) i .snd k})
--     --   ≡⟨ ΣPathP ((funExt (λ {0 → refl ; (suc n) → refl})) , λ {i 0 → refl ; i (suc n) → b .snd (suc n)}) ⟩
--     -- b ∎
--     -- where
--     --   ga : Iso (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) A 
--     --   ga = lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)

--     --   a : ℕ → A
--     --   a n = b .fst (suc n) .fst

--     --   p : (n : ℕ) → a (suc n) ≡ a n
--     --   p n i = b .snd (suc n) i .fst

--     --   temp : (n : ℕ) → b .fst (suc 0) .fst ≡ b .fst (suc n) .fst -- should be trivial..
--     --   temp 0 = refl
--     --   temp (suc n) = temp n ∙ {!!} -- b .fst (suc n) .fst ≡ b .fst (suc (suc n)) .fst

-- Shift is equivalence (12) and (13) in the proof of Theorem 7
-- https://arxiv.org/pdf/1504.02949.pdf
-- "Non-wellfounded trees in Homotopy Type Theory"
-- Benedikt Ahrens, Paolo Capriotti, Régis Spadotti

-- TODO: This definition is inefficient, it should be updated to use some cubical features!
shift-iso : ∀ {ℓ} (S : Container ℓ) -> Iso (P₀ S (M S)) (M S)
shift-iso S@(A , B) =
  P₀ S (M S)
     Iso⟨ Σ-ap-iso₂ (λ x → iso (λ f → (λ n z → f z .fst n) , λ n i a → f a .snd n i)
                               (λ (u , q) z → (λ n → u n z) , λ n i → q n i z)
                               (λ _ → refl)
                               (λ _ → refl)) ⟩
  (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → X (sequence S) n) ] ((n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)))
    Iso⟨ invIso α-iso-step-5-Iso ⟩
  (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
        Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
           ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                               (π (sequence S) ∘ u (suc n))
                               (u n)))
      Iso⟨ α-iso-step-1-4-Iso-lem-12 ⟩
  M S ∎Iso
  where
  α-iso-step-5-Iso-helper0 :
    ∀ (a,p : Σ[ a ∈ (ℕ -> A)] ((n : ℕ) → a (suc n) ≡ a n))
    → (n : ℕ)
    → a,p .fst n ≡ a,p .fst 0
  α-iso-step-5-Iso-helper0 _ 0 = refl
  α-iso-step-5-Iso-helper0 (a , p) (suc n) = p n ∙ α-iso-step-5-Iso-helper0 (a , p) n

  α-iso-step-5-Iso-helper1-Iso :
          ∀ (a,p : Σ[ a ∈ (ℕ -> A)] ((n : ℕ) → a (suc n) ≡ a n))
          → (u : (n : ℕ) → B (a,p .fst n) → Wₙ S n)
          → (n : ℕ)
          → Iso (PathP (λ x → B (a,p .snd n x) → Wₙ S n) (πₙ S ∘ u (suc n)) (u n))
              (πₙ S ∘ (subst (\k -> B k → Wₙ S (suc n)) (α-iso-step-5-Iso-helper0 a,p (suc n))) (u (suc n)) ≡ subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (u n))
  α-iso-step-5-Iso-helper1-Iso  a,p@(a , p) u n  =
         PathP (λ x → B (p n x) → Wₙ S n) (πₙ S ∘ u (suc n)) (u n)
           Iso⟨ pathToIso (PathP≡Path (λ x → B (p n x) → Wₙ S n) (πₙ S ∘ u (suc n)) (u n)) ⟩
         subst (λ k → B k → Wₙ S n) (p n) (πₙ S ∘ u (suc n)) ≡ (u n)
           Iso⟨ (invIso (temp sfad)) ⟩
         (subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (subst (λ k → B k → Wₙ S n) (p n) (πₙ S ∘ u (suc n)))
                ≡
         subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (u n))
           Iso⟨ pathToIso (λ i → (sym (substComposite (λ k → B k → Wₙ S n) (p n) (α-iso-step-5-Iso-helper0 a,p n) (πₙ S ∘ u (suc n)))) i
                             ≡ subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (u n)) ⟩
         subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p (suc n)) (πₙ S ∘ u (suc n))
           ≡
         subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (u n)
           Iso⟨ pathToIso (λ i → (substCommSlice (λ k → B k → Wₙ S (suc n)) (λ k → B k → Wₙ S n) (λ a x x₁ → (πₙ S) (x x₁)) ((α-iso-step-5-Iso-helper0 a,p) (suc n)) (u (suc n))) i
                          ≡ subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (u n)) ⟩
         πₙ S ∘ subst (λ k → B k → Wₙ S (suc n)) (α-iso-step-5-Iso-helper0 a,p (suc n)) (u (suc n))
           ≡
         subst (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n) (u n) ∎Iso
         where
           abstract
             temp = iso→fun-Injection-Iso-x

           private
             sfad : Iso (B (a n) → Wₙ S n) (B (a 0) → Wₙ S n)
             sfad = (pathToIso (cong (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n)))
           
  α-iso-step-5-Iso :
         Iso
           (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A) ] ((n : ℕ) → a (suc n) ≡ a n)) ]
             Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
               ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                                   (π (sequence S) ∘ u (suc n))
                                   (u n)))
             (Σ[ a ∈ A ] (Σ[ u ∈ ((n : ℕ) → B a → X (sequence S) n) ] ((n : ℕ) → π (sequence S) ∘ (u (suc n)) ≡ u n)))
  α-iso-step-5-Iso =
    Σ-ap-iso (lemma11-Iso {S = S} (λ _ → A) (λ _ x → x)) (λ a,p →
    Σ-ap-iso (pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → cong (λ k → B k → Wₙ S n) (α-iso-step-5-Iso-helper0 a,p n)))) λ u →
              pathToIso (cong (λ k → (n : ℕ) → k n) (funExt λ n → isoToPath (α-iso-step-5-Iso-helper1-Iso a,p u n))))

  α-iso-step-1-4-Iso-lem-12 :
        Iso (Σ[ a ∈ (Σ[ a ∈ ((n : ℕ) → A)] ((n : ℕ) → a (suc n) ≡ a n)) ]
                  (Σ[ u ∈ ((n : ℕ) → B (a .fst n) → X (sequence S) n) ]
                      ((n : ℕ) → PathP (λ x → B (a .snd n x) → X (sequence S) n)
                                          (π (sequence S) ∘ u (suc n))
                                          (u n))))
            (limit-of-chain (sequence S))
  fun α-iso-step-1-4-Iso-lem-12 (a , b) = (λ { 0 → lift tt ; (suc n) → (a .fst n) , (b .fst n)}) , λ { 0 → refl {x = lift tt} ; (suc m) i → a .snd m i , b .snd m i }
  inv α-iso-step-1-4-Iso-lem-12 x = ((λ n → (x .fst) (suc n) .fst) , λ n i → (x .snd) (suc n) i .fst) , (λ n → (x .fst) (suc n) .snd) , λ n i → (x .snd) (suc n) i .snd
  fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = lift tt
  fst (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = refl i
  snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) 0 = refl
  snd (rightInv α-iso-step-1-4-Iso-lem-12 (b , c) i) (suc n) = c (suc n)
  leftInv α-iso-step-1-4-Iso-lem-12 (a , b) = refl

shift : ∀ {ℓ} (S : Container ℓ) -> P₀ S (M S) ≡ M S
shift S = isoToPath (shift-iso S) -- lemma 13 & lemma 12

-- Transporting along shift

in-fun : ∀ {ℓ} {S : Container ℓ} -> P₀ S (M S) -> M S
in-fun {S = S} = fun (shift-iso S)

out-fun : ∀ {ℓ} {S : Container ℓ} -> M S -> P₀ S (M S)
out-fun {S = S@(A , B)} = inv (shift-iso S)

-- Property of functions into M-types

lift-to-M : ∀ {ℓ ℓ'} {S : Container ℓ} {A : Type ℓ'}
  → (x : (n : ℕ) -> A → X (sequence S) n)
  → ((n : ℕ) → (a : A) →  π (sequence S) (x (suc n) a) ≡ x n a)
  ---------------
  → (A → M S)
lift-to-M x p a = (λ n → x n a) , λ n i → p n a i

lift-direct-M : ∀ {ℓ} {S : Container ℓ}
  → (x : (n : ℕ) → X (sequence S) n)
  → ((n : ℕ) →  π (sequence S) (x (suc n)) ≡ x n)
  ---------------
  → M S
lift-direct-M x p = x , p
