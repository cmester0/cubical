{-# OPTIONS --cubical --guardedness #-} --safe

module Cubical.Codata.M.AsLimit.partiality-monad where

{-
  Inspired by  Code related to the paper 
  "Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type" (https://arxiv.org/pdf/1610.09254.pdf)
  Thorsten Altenkirch, Nils Anders Danielsson and Nicolai Kraus
  Located at: http://www.cse.chalmers.se/~nad/publications/altenkirch-danielsson-kraus-partiality/README.html
-}

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to empty-rec)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_×_)

-- open import Cubical.Codata.M.AsLimit.Container
-- open import Cubical.Codata.M.AsLimit.itree
-- open import Cubical.Codata.M.AsLimit.M

open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥rec∥ ; map to ∥map∥)
open import Cubical.HITs.SetQuotients renaming (elim to elim/ ; rec to rec/)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.HLevels

data Delay (R : Set) : Set where
  now : R → Delay R
  later : Delay R → Delay R

-- Weak bisimularity for delay monad
mutual
  data _∼delay_ {R} : (_ _ : Delay R) → Set where
    ∼now : ∀ (r s : R) → r ≡ s → now r ∼delay now s
    ∼later-l : ∀ t u → t ∼delay u → later t ∼delay u
    ∼later-r : ∀ t u → t ∼delay u → t ∼delay later u
    ∼later : ∀ t u → t ∼delay u → later t ∼delay later u
  --   ∼later : ∀ t u → t ∞∼delay u → later t ∼delay later u

  -- record _∞∼delay_ {R} (x y : Delay R) : Set where
  --   coinductive
  --   field
  --     force : x ∼delay y

--------------
-- Maybe --
--------------

infix 4 _↑ _↓_

-- x ↓ y means that the computation x has the value y.

_↓_ : ∀ {A : Set} → A ⊎ Unit → A → Set
x ↓ y = x ≡ inl y

-- x ↑ means that the computation x does not have a value.
                                                      
_↑ :  ∀ {A : Set} → A ⊎ Unit → Set
x ↑ = x ≡ inr tt

LE : ∀ {A : Set} → A ⊎ Unit → A ⊎ Unit → Set
LE x y = (x ≡ y) ⊎ ((x ↑) × (y ↑ → ⊥))

--------------
-- Sequence --
--------------

module _ where
  ismon : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → Set
  ismon {A} g = (n : ℕ) → LE (g n) (g (suc n))

  ismon' : ∀ {A : Set} → (g : ℕ → A ⊎ Unit) → ℕ → Set
  ismon' {A} g n = LE (g n) (g (suc n))

  Seq : Set → Set
  Seq A = (Σ[ g ∈ (ℕ → A ⊎ Unit) ] (ismon g))

  shift-seq : ∀ {A : Set} → (t : Seq A) → Σ (A ⊎ Unit) (λ va → ismon' (λ {0 → va ; (suc n) → fst t n}) 0) → Seq A
  shift-seq (g , a) (va , mon) = (λ {0 → va ; (suc n) → g n}) , (λ {0 → mon ; (suc n) → a n})

  shift'-case-fun : ∀ {A : Set} → (t : Seq A) → (x : A ⊎ Unit) -> ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0
  shift'-case-fun t x =
    (case x return (λ x → ismon' (λ { 0 → (inr tt) ; (suc 0) → x ; (suc (suc n)) → fst t n }) 0) of
         λ {(inl r) → inr (refl , inl≢inr)
           ;(inr tt) → inl refl})

  shift' : ∀ {A : Set} → Seq A → Seq A
  shift' t =
    shift-seq t ((inr tt) , shift'-case-fun t (fst t 0))

  unshift : ∀ {A} → Seq A → Seq A
  unshift (g , a) = g ∘ suc , a ∘ suc

  -- works for any -- (fst t 0)
  unshift-shift : ∀ {A} t {va-mon} → unshift {A = A} (shift-seq t va-mon) ≡ t
  unshift-shift {A = A} t = refl

  shift-unshift : ∀ {A} t → shift-seq {A = A} (unshift t) (fst t 0 , snd t 0) ≡ t
  shift-unshift (g , a) =
    ΣPathP ((funExt λ {0 → refl ; (suc n) → refl }) , λ {i 0 → a 0 ; i (suc n) → a (suc n)})

  now-seq : {A : Set} -> A -> Seq A
  now-seq a = (λ _ → inl a) , (λ _ → inl refl)

----------------------------------
-- Sequence equivalent to Delay --
----------------------------------

  Delay→Seq : ∀ {A : Set} → Delay A → Seq A
  Delay→Seq (now a) = now-seq a
  Delay→Seq (later t) = shift' (Delay→Seq t)
  
  private
    {-# NON_TERMINATING #-}
    Seq→Delay' : ∀ {A : Set} → Seq A → Delay A
    Seq→Delay' t = case fst t 0 of λ {(inl r) → now r ; (inr tt) → later (Seq→Delay' (unshift t))}

  insert-fun : ∀ {A} (b : Seq A) → (A ⊎ Unit) → Delay A
  insert-fun b (inl r) = now r
  insert-fun b (inr tt) = later (Seq→Delay' (unshift b))

  Seq→Delay : ∀ {A : Set} → Seq A → Delay A
  Seq→Delay t = case fst t 0 of (insert-fun t) -- λ {(inl r) → now r ; (inr tt) → later (Seq→Delay' (unshift t))}

  temp : ∀ {A} (b : Seq A) → (n : ℕ) → Σ (A ⊎ Unit) (λ va → (fst b n ≡ va) × ismon' (fst b) n)
  temp b n = fst b n , refl , snd b n

  asfd : ∀ {A} (b : Seq A) (r : A) → inl r ≡ fst b 0 → (n : ℕ) → inl r ≡ fst b n
  asfd b r p 0 = p 
  asfd b r p (suc n) = asfd b r p n ∙ sym (case snd b n of (λ { (inl q) → sym q ; (inr (q , _)) → empty-rec (inl≢inr (asfd b r p n ∙ q)) }))

  fadsasfgd : ∀ {A} → isSet (A ⊎ Unit) → (b : Seq A) (n : ℕ) → isProp (LE (fst b n) (fst b (suc n)))
  fadsasfgd A-set b n (inl p) (inl q) = cong inl (A-set (fst b n) (fst b (suc n)) p q)
  fadsasfgd A-set b n (inl p) (inr (x , q)) = empty-rec (q (sym p ∙ x))
  fadsasfgd A-set b n (inr (x , q)) (inl p) = empty-rec (q (sym p ∙ x))
  fadsasfgd A-set b n (inr (x , p)) (inr (y , q)) =
    cong inr λ i → A-set (fst b n) (inr tt) x y i , λ v → isProp⊥ (p v) (q v) i

  famm : ∀ {A} → isSet (A ⊎ Unit) → (b : Seq A) (r : A) → inl r ≡ fst b 0 → now-seq r ≡ b
  famm A-set b r q =
    ΣPathP (funExt (asfd b r q) ,
      transport (sym (PathP≡Path (λ i → ismon (funExt (asfd b r q) i)) (λ _ → inl refl) (snd b)))
        (funExt λ (n : ℕ) → fadsasfgd A-set b n (transport (λ i → ismon (funExt (asfd b r q) i)) (λ _ → inl refl) n) (snd b n)))

  postulate
    elp : ∀ {A} → isSet (A ⊎ Unit) -> (b : Seq A) -> Delay→Seq (Seq→Delay' b) ≡ b

  elp' : ∀ {A} → isSet (A ⊎ Unit) → (b : Seq A) → (fst b 0 ≡ inr tt) → shift' (unshift b) ≡ b
  elp' A-set b q =
    shift-seq (unshift b) (inr tt , shift'-case-fun (unshift b) (fst b 1))
      ≡⟨ cong (λ a → shift-seq (unshift b) a)
         (ΣPathP (sym q ,
           transport (sym (PathP≡Path (λ i → ismon' (λ { 0 → sym q i ; (suc n) → fst b (suc n) }) 0) (shift'-case-fun (unshift b) (fst b (suc 0))) (snd b 0)))
                     (fadsasfgd A-set b 0 (transport (λ i → ismon' (λ { 0 → sym q i ; (suc n) → fst b (suc n) }) 0) (shift'-case-fun (unshift b) (fst b (suc 0)))) (snd b 0)))) ⟩
    shift-seq (unshift b) (fst b 0 , snd b 0)
      ≡⟨ shift-unshift b ⟩
    b ∎

  Seq-Delay : ∀ {A} → isSet (A ⊎ Unit) -> (b : Seq A) → Delay→Seq (Seq→Delay b) ≡ b
  Seq-Delay {A = A} A-set b with temp b 0
  ... | (inl r , q , _) =
    Delay→Seq ((insert-fun b) (fst b 0))
      ≡⟨ (λ i → Delay→Seq (insert-fun b (q i))) ⟩
    Delay→Seq (now r)
      ≡⟨ refl ⟩
    (now-seq r)
      ≡⟨ famm A-set b r (sym q) ⟩ 
    b ∎
  ... | (inr tt , q , _) =
    Delay→Seq ((insert-fun b) (fst b 0))
      ≡⟨ (λ i → Delay→Seq (insert-fun b (q i))) ⟩
    shift' (Delay→Seq (Seq→Delay' (unshift b)))
      ≡⟨ cong shift' (elp A-set (unshift b)) ⟩
    shift' (unshift b)
      ≡⟨ elp' A-set b q ⟩
    b ∎

  postulate
    Delay'-Seq : ∀ {A : Set} (b : Delay A) → Seq→Delay' (Delay→Seq b) ≡ b

  Delay-Seq : ∀ {A : Set} (b : Delay A) → Seq→Delay (Delay→Seq b) ≡ b
  Delay-Seq (now r) = refl
  Delay-Seq {A = A} (later t) = later (Seq→Delay' (unshift (shift' (Delay→Seq t)))) ≡⟨ (λ i → later (Seq→Delay' (unshift-shift {A = A} (Delay→Seq t) {va-mon = (fst (Delay→Seq t) 0) , inl refl} i))) ⟩ later (Seq→Delay' (Delay→Seq t)) ≡⟨ cong later (Delay'-Seq t) ⟩ later t ∎

  delay-Seq-Iso : ∀ {A} → isSet (A ⊎ Unit) -> Iso (Delay A) (Seq A)
  delay-Seq-Iso A-set = (iso Delay→Seq Seq→Delay (Seq-Delay A-set) Delay-Seq)

  delay≡Seq : ∀ {A} → isSet (A ⊎ Unit) -> Delay A ≡ Seq A
  delay≡Seq A-set = isoToPath (delay-Seq-Iso A-set)
  
  -----------------------
  -- Sequence ordering --
  -----------------------
  
  _↓seq_ : ∀ {A} → Seq A → A → Set
  s ↓seq a = Σ[ n ∈ ℕ ] fst s n ≡ inl a
  
  _⊑seq_ : ∀ {A} → ∀ (_ _ : Seq A) → Set
  _⊑seq_ {A} s t = (a : A) → ∥ (s ↓seq a) ∥ → ∥ t ↓seq a ∥

  _∼seq_ : ∀ {A} → ∀ (_ _ : Seq A) → Set
  s ∼seq t = s ⊑seq t × t ⊑seq s

  -- TODO: show the equivalence lifts to the quotient!

  ⊑seq-refl : ∀ {A : Set} (x : Seq A) → x ⊑seq x
  ⊑seq-refl x = λ a → idfun ∥ x ↓seq a ∥

  asfdasdf : forall {A : Set} (a : A) (b : Seq A) -> b ↓seq a -> (shift' b) ↓seq a
  asfdasdf a b (n , p) = suc n , p

  asfdasdf' : forall {A : Set} (a : A) (b : Seq A) -> (shift' b) ↓seq a -> b ↓seq a
  asfdasdf' a b (0 , p) = 0 , sym (asfd (shift' b) a (sym p) 1)
  asfdasdf' a b ((suc n) , p) = n , p

  ∼seq-refl : forall {A : Set} (a : Seq A) -> a ∼seq a
  ∼seq-refl = λ a → (λ a₁ x → x) , (λ a₁ x → x)

  shift-sim : forall {A : Set} (a b : Seq A) -> a ∼seq b -> (shift' a) ∼seq b
  shift-sim a b (p , q) =
    (λ v x → p v (∥map∥ (asfdasdf' v a) x)) ,
    (λ v x → ∥map∥ (asfdasdf v a) (q v x))

  shift-sym : forall {A : Set} (a b : Seq A) -> a ∼seq b -> b ∼seq  a
  shift-sym a b (p , q) = q , p

  ∼Delay→∼Seq : ∀ {A : Set} → {x y : Delay A} → x ∼delay y → (Delay→Seq x) ∼seq (Delay→Seq y)
  ∼Delay→∼Seq (∼now a b p) =
    subst (λ k → now-seq a ∼seq now-seq k) p (∼seq-refl (now-seq a))
  ∼Delay→∼Seq (∼later-l t u p) =
    shift-sim (Delay→Seq t) (Delay→Seq u) (∼Delay→∼Seq p)
  ∼Delay→∼Seq (∼later-r t u p) =
    shift-sym (Delay→Seq (later u)) (Delay→Seq t) (shift-sim (Delay→Seq u) (Delay→Seq t) (shift-sym (Delay→Seq t) (Delay→Seq u) (∼Delay→∼Seq p)))
  ∼Delay→∼Seq (∼later t u p) =
    shift-sym (Delay→Seq (later u)) (Delay→Seq (later t)) (shift-sim (Delay→Seq u) (Delay→Seq (later t)) (shift-sym (Delay→Seq (later t)) (Delay→Seq u) (shift-sim (Delay→Seq t) (Delay→Seq u) (∼Delay→∼Seq p))))    

  kappa : {A : Set} -> (x : A ⊎ Unit) -> (y : A ⊎ Unit) -> (Σ[ x' ∈ (A ⊎ Unit) ] x' ≡ x) × (Σ[ y' ∈ (A ⊎ Unit) ] y' ≡ y)
  kappa x y = (x , refl) , (y , refl)


  postulate
    ∼Seq→∼Delay' : ∀ {A : Set} → {x y : Seq A} → x ∼seq y → Seq→Delay' x ∼delay Seq→Delay' y
    ∼Seq→∼Delay'' : ∀ {A : Set} → {x y : Seq A} → x ∼seq y → Seq→Delay x ∼delay Seq→Delay' y 
    ∼Seq→∼Delay''' : ∀ {A : Set} → {x y : Seq A} → x ∼seq y → Seq→Delay' x ∼delay Seq→Delay y 

  asfdasdf'' : forall {A : Set} (a : A) (b : Seq A) -> b ↓seq a -> (unshift b) ↓seq a
  asfdasdf'' a b (0 , p) = 0 , sym (asfd b a (sym p) 1)
  asfdasdf'' a b ((suc n) , p) = n , p

  asfdasdf''' : forall {A : Set} (a : A) (b : Seq A) -> (unshift b) ↓seq a -> b ↓seq a 
  asfdasdf''' a b (n , p) = suc n , p

  ∼seq-now-eq : ∀ {A : Set} {a b : A} → now-seq a ∼seq now-seq b → a ≡ b
  ∼seq-now-eq {a = a} {b} (p , q) = let temp = p a in {!!}

  kva : ∀ {A : Set} y {r a : A} → y ↓seq r → y ↓seq a → r ≡ a
  kva y {r = r} {a} (0 , p) (m , q) = transport (isEmbedding→Injection-x inl isEmbedding-inl r a) (asfd y r (sym p) m ∙ q)
  kva y {r = r} {a} ((suc n) , p) (m , q) = {!!}

  kva' : {A : Set} → isSet (A) → ∀ y {r a : A} → ∥ y ↓seq r ∥ → ∥ y ↓seq a ∥ → r ≡ a
  kva' A-set y {r} {a} p q = ∥rec∥ (A-set r a) (λ p' → ∥rec∥ (A-set r a) (λ q' → kva y p' q') q) p

  asdf : ∀ {A : Set} {y} {r : A} → now-seq r ⊑seq y → y ∼seq now-seq r
  asdf {y = y} {r} p = (λ a x → let temp = p r ∣ 0 , refl ∣ in {!!}) , p

  A-Unit-set : ∀ {A : Set} → isSet A → isSet (A ⊎ Unit)
  A-Unit-set A-set (inl r) (inl a) p q =
    let temp = (A-set r a (transport (isEmbedding→Injection-x inl isEmbedding-inl r a) p) (transport (isEmbedding→Injection-x inl isEmbedding-inl r a) q)) in
    let temp' = transport (isEmbedding→Injection-x inl isEmbedding-inl r a) p ≡
                transport (isEmbedding→Injection-x inl isEmbedding-inl r a) q
                  ≡⟨ isEmbedding→Injection-x (transport (isEmbedding→Injection-x inl isEmbedding-inl r a)) (iso→isEmbedding (pathToIso (isEmbedding→Injection-x inl isEmbedding-inl r a))) p q ⟩
                p ≡ q ∎
    in transport temp' temp
  A-Unit-set A-set (inl r) (inr tt) p q = empty-rec (inl≢inr p)
  A-Unit-set A-set (inr tt) (inl b) p q = empty-rec (inl≢inr (sym p))
  A-Unit-set A-set (inr tt) (inr tt) p q =
    let temp = (isProp→isSet (isContr→isProp (tt , (λ y i → tt)))) in
    let temp' = (temp tt tt (transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) p) (transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) q)) in
    let temp'' = transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) p ≡
                 transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt) q
                   ≡⟨ isEmbedding→Injection-x (transport (isEmbedding→Injection-x inr isEmbedding-inr tt tt)) (iso→isEmbedding (pathToIso (isEmbedding→Injection-x inr isEmbedding-inr tt tt))) p q ⟩
                 p ≡ q ∎
    in
    transport temp'' temp'
  
  ∼Seq→∼Delay : ∀ {A : Set} → (isSet A) → {x y : Seq A} → x ∼seq y → Seq→Delay x ∼delay Seq→Delay y 
  ∼Seq→∼Delay A-set {x = x} {y} (a , b) =
    case kappa (x .fst 0) (y .fst 0) return (λ { ((a , _) , (b , _)) → insert-fun x a ∼delay insert-fun y b }) of
      λ {((inl r , p) , (inl s , q)) → ∼now r s (kva' A-set x ∣ 0 , sym p ∣ (b s ∣ 0 , sym q ∣))
        ;((inl r , p) , (inr tt , q)) →
          let temp = 
                   (∼later-r (Seq→Delay x) (Seq→Delay' (unshift y)) (∼Seq→∼Delay''
                     ((λ a₁ x₁ → ∥map∥ (λ x₂ → asfdasdf'' a₁ y x₂) (a a₁ x₁)) ,
                     (λ a₁ x₁ → (b a₁ (∥map∥ (asfdasdf''' a₁ y) x₁))))))
          in
            transport (λ i → Seq→Delay (sym (famm (A-Unit-set A-set) x r p) i) ∼delay later (Seq→Delay' (unshift y))) temp
        ;((inr tt , p) , (inl s , q)) →
          let temp = 
                   (∼later-l (Seq→Delay' (unshift x)) (Seq→Delay y) (∼Seq→∼Delay'''
                     ((λ a₁ x₁ → a a₁ (∥map∥ (asfdasdf''' a₁ x) x₁)) ,
                     (λ a₁ x₁ → ∥map∥ (λ x₂ → asfdasdf'' a₁ x x₂) (b a₁ x₁)))))
          in
            transport (λ i → later (Seq→Delay' (unshift x)) ∼delay (Seq→Delay (sym (famm (A-Unit-set A-set) y s q) i))) temp

        ;((inr tt , p) , (inr tt , q)) → ∼later (Seq→Delay' (unshift x)) (Seq→Delay' (unshift y)) (∼Seq→∼Delay' (
              (λ a₁ x₁ → ∥map∥ (asfdasdf'' a₁ y) (a a₁ (∥map∥ (asfdasdf''' a₁ x) x₁))) ,
              (λ a₁ x₁ → ∥map∥ (asfdasdf'' a₁ x) (b a₁ (∥map∥ (asfdasdf''' a₁ y) x₁)))))}

  akka : ∀ {A : Set} → (A-set : isSet A) → {x y : Seq A} (r : x ∼seq y) → PathP (λ x₁ → Seq-Delay (A-Unit-set A-set) x x₁ ∼seq Seq-Delay (A-Unit-set A-set) y x₁) (∼Delay→∼Seq (∼Seq→∼Delay A-set r)) r
  akka A-set r = {!!}

  akka' : ∀ {A : Set} → (A-set : isSet A) → {x y : Delay A} (r : x ∼delay y) → PathP (λ x₁ → Delay-Seq x x₁ ∼delay Delay-Seq y x₁) (∼Seq→∼Delay A-set (∼Delay→∼Seq r)) r
  akka' A-set (∼now a b p) i = ∼now a b (A-set a b (kva' A-set (now-seq a) ∣ 0 , sym refl ∣ (proj₂ (∼Delay→∼Seq (∼now a b p)) b ∣ 0 , sym refl ∣)) p i)
  akka' A-set (∼later-l x y p) = {!!}


  delay/∼≡Seq/∼ : forall {A : Set} → (isSet A) -> Iso (Delay A / _∼delay_) (Seq A / _∼seq_)
  delay/∼≡Seq/∼ A-set =
    iso fun inv right left
    where
      fun = (rec/ ([_] ∘ Delay→Seq) (λ x y r → eq/ (Delay→Seq x) (Delay→Seq y) (∼Delay→∼Seq r)) squash/)
      inv = (rec/ ([_] ∘ Seq→Delay) (λ x y r → eq/ (Seq→Delay x) (Seq→Delay y) (∼Seq→∼Delay A-set r)) squash/)

      right : ∀ b → fun (inv b) ≡ b
      right [ b ] = [ (Delay→Seq (Seq→Delay b)) ] ≡⟨ cong [_] (Seq-Delay (A-Unit-set A-set) b) ⟩ [ b ] ∎
      right (eq/ a b r i) = (λ j → eq/ (Seq-Delay (A-Unit-set A-set) a j) (Seq-Delay (A-Unit-set A-set) b j) (akka A-set r j) i) ∙ refl
      right (squash/ a b p q i j) k = (squash/ (right a k) (right b k) (λ h → right (p h) k) (λ h → right (q h) k) i j)

      left : ∀ b → inv (fun b) ≡ b
      left [ b ] = [ (Seq→Delay (Delay→Seq b)) ] ≡⟨ cong [_] (Delay-Seq b) ⟩ [ b ] ∎
      left (eq/ a b r i) = (λ j → eq/ (Delay-Seq a j) (Delay-Seq b j) (akka' A-set r j) i) ∙ refl
      left (squash/ a b p q i j) k = (squash/ (left a k) (left b k) (λ h → left (p h) k) (λ h → left (q h) k) i j)

-- ------------------------
-- -- Helper definitions --
-- ------------------------

-- open import Cubical.Data.Nat.Order

-- _↓′_ : ∀ {A} → Seq A → A → Set _
-- (f , _) ↓′ y = Σ[ m ∈ ℕ ] ((f m ≡ inl y) × (∀ n → (f n ≡ inr tt → ⊥) → m ≤ n))
--   where open import Cubical.Data.Nat.Order

-- postulate
--   ⇓′-propositional : ∀ {A} → isSet A → ∀ x {y : A} → isProp (x ↓′ y)

-- Other-singleton : {a : Level} {A : Set a} → A → Set a
-- Other-singleton {A = A} x = Σ-syntax A λ y → x ≡ y

-- inspect : ∀ {A : Set} -> (x : A ⊎ Unit) → Other-singleton x
-- inspect (inl r) = (inl r) , refl
-- inspect (inr tt) = (inr tt) , refl

-- ⇓′→⇓ : ∀ {A} x {y : A} → x ↓′ y → x ↓seq y
-- ⇓′→⇓ = λ x x₁ → fst x₁ , proj₁ (snd x₁)

-- ----------------------
-- -- Partiality monad --
-- ----------------------

-- -- Partiality monad (QIIT)
-- -- Paper: Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type (https://arxiv.org/abs/1610.09254)
-- -- Authors: Thorsten Altenkirch, Nils Anders Danielsson, Nicolai Kraus
-- -- Formalization: http://www.cse.chalmers.se/~nad/listings/partiality-monad/Partiality-monad.Inductive.html
-- mutual
--   infix 10 <_>⊥
--   infix 4  _⊑_

--   -- The partiality monad.

--   data <_>⊥ {ℓ} (A : Type ℓ) : Type ℓ where
--     never  : < A >⊥
--     η      : A → < A >⊥
--     ⊔      : Increasing-sequence A → < A >⊥
--     α      : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
--     ⊥-isSet : isSet (< A >⊥)

--   -- Increasing sequences.

--   Increasing-sequence : ∀ {ℓ} → Type ℓ → Type ℓ
--   Increasing-sequence A = Σ[ f ∈ (ℕ → < A >⊥) ] ((n : ℕ) → f n ⊑ f (suc n))

--   -- Upper bounds.

--   Is-upper-bound : ∀ {ℓ} → {A : Type ℓ} → Increasing-sequence A → < A >⊥ → Set ℓ
--   Is-upper-bound s x = ∀ n → (fst s n) ⊑ x

--   -- A projection function for Increasing-sequence.

--   -- An ordering relation.

--   data _⊑_ {ℓ} {A : Set ℓ} : < A >⊥ → < A >⊥ → Set ℓ where
--     ⊑-refl            : ∀ x → x ⊑ x
--     ⊑-trans           : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
--     never⊑            : ∀ x → never ⊑ x
--     upper-bound       : ∀ s → Is-upper-bound s (⊔ s)
--     least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⊔ s ⊑ ub
--     ⊑-propositional   : ∀ {x y} → isProp (x ⊑ y)

-- -------------------------------------------------------------
-- -- Equivalence to Sequence quotiented by weak bisimularity --
-- -------------------------------------------------------------

-- Maybe→⊥ : ∀ {A : Type₀} → A ⊎ Unit → < A >⊥
-- Maybe→⊥ (inr tt)  = never
-- Maybe→⊥ (inl y) = η y

-- Increasing-at : ∀ {A : Set} → ℕ → (ℕ → A ⊎ Unit) → Set
-- Increasing-at n f = LE (f n) (f (suc n))

-- Increasing : ∀ {A : Set} → (ℕ → A ⊎ Unit) → Set
-- Increasing f = ∀ n → Increasing-at n f

-- ≰→> : ∀ {m n} → (m ≤ n → ⊥) → n < m
-- ≰→> {zero} {n} p = Cubical.Data.Empty.elim (p (zero-≤))
-- ≰→> {suc m} {zero}  p = suc-≤-suc (zero-≤)
-- ≰→> {suc m} {suc n} p = suc-≤-suc (≰→> (p ∘ suc-≤-suc))

-- Dec : ∀ {p} → Set p → Set p
-- Dec P = P ⊎ (P → ⊥)

-- Decidable :
--   ∀ {a b ℓ} {A : Set a} {B : Set b}
--   → (A → B → Set ℓ)
--   → Set (ℓ-max (ℓ-max a b) ℓ)
-- Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- _≤?_ : Decidable _≤_
-- zero  ≤? n     = inl (zero-≤)
-- suc m ≤? zero  = inr λ { x → ¬-<-zero x }
-- suc m ≤? suc n = Cubical.Data.Sum.map suc-≤-suc (λ m≰n → m≰n ∘ pred-≤-pred) (m ≤? n)

-- ≤⊎> : ∀ m n → (m ≤ n) ⊎ (n < m)
-- ≤⊎> m n = Cubical.Data.Sum.map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→> (m ≤? n)

-- postulate
--   ↑-downwards-closed :
--     ∀ {A} {f : ℕ → A ⊎ Unit} {m n}
--     → Increasing f
--     → m ≤ n
--     → f n ↑ → f m ↑
-- -- ↑-downwards-closed = {!!}

-- ↑<↓ :
--   ∀ {A} {f : ℕ → A ⊎ Unit} {x m n}
--     → Increasing f
--     → (f m) ↑ → (f n) ↓ x
--     → m < n
-- ↑<↓ {A} {f} {x} {m} {n} inc fm↑ fn↓x with (≤⊎> n m)
-- ... | inr m<n = m<n
-- ... | inl n≤m = Cubical.Data.Empty.rec (inl≢inr (inl x ≡⟨ sym fn↓x ⟩ f n ≡⟨ ↑-downwards-closed inc n≤m fm↑ ⟩ inr tt ∎))

-- ≰→≥ : ∀ {m n} → (m ≤ n → ⊥) → n ≤ m
-- ≰→≥ p = ≤-trans (≤-suc ≤-refl) (≰→> p)

-- total : ∀ m n → (m ≤ n) ⊎ (n ≤ m)
-- total m n = Cubical.Data.Sum.map (idfun (Σ ℕ (λ z → z + m ≡ n))) ≰→≥ (m ≤? n)

-- cancel-inl : {A : Set} {B : Set} {x y : A} → _≡_ {A = A ⊎ B} (inl x) (inl y) → x ≡ y
-- cancel-inl {A} {B} {x = x} = λ p i → case p i of λ {(inl y) → const y x ; (inr y) → idfun A x}

-- cancel-inr : {A : Set} {B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inr x) (inr y) → x ≡ y
-- cancel-inr {A} {B} {x = x} = λ p i → case p i of λ { (inr y) → const y x ; (inl y) → idfun B x }

-- ↓-step :
--   ∀ {A : Set} {f} {x : A} {n}
--   → Increasing f
--   → f n ↓ x → f (suc n) ↓ x
-- ↓-step {f = f} {x} {n} inc fn↓x = step'' (inc n)
--   module ↓ where
--     step'' : LE (f n) (f (suc n)) → f (suc n) ↓ x
--     step'' (inl fn≡f1+n) =
--       f (suc n)  ≡⟨ sym fn≡f1+n ⟩
--       f n        ≡⟨ fn↓x ⟩
--       inl x     ∎
--     step'' (inr (fn↑ , _)) =
--       Cubical.Data.Empty.rec (inl≢inr (inl x ≡⟨ sym fn↓x ⟩ f n ≡⟨ fn↑ ⟩ inr tt ∎))

-- ↓-upwards-closed :
--   ∀ {A} {f : ℕ → A ⊎ Unit} {m n x} →
--   Increasing f → m ≤ n → f m ↓ x → f n ↓ x
-- ↓-upwards-closed {A} {f} {x = x} inc (k , p) = ↓-upwards-closed-helper inc k p
--   where
--     ↓-upwards-closed-helper :
--       ∀ {A} {f : ℕ → A ⊎ Unit} {m n x} →
--       Increasing f → (k : ℕ) → (p : k + m ≡ n) → f m ↓ x → f n ↓ x
--     ↓-upwards-closed-helper {A} {f} {x = x} _ 0 p = subst (λ a → f a ↓ x) p
--     ↓-upwards-closed-helper {A} {f} {x = x} inc (suc n) p = subst (λ a → f a ↓ x) p ∘ ↓-step inc ∘ ↓-upwards-closed-helper inc n refl

-- termination-value-unique :
--   ∀ {A : Set} (x : Seq A) {y z} → x ↓seq y → x ↓seq z → y ≡ z
-- termination-value-unique (f , inc) {y} {z} (m , fm↓y) (n , fn↓z)
--   with total m n
-- ... | inl m≤n = cancel-inl (inl y ≡⟨ sym (↓-upwards-closed inc m≤n fm↓y) ⟩  f n ≡⟨ fn↓z ⟩ inl z ∎)
-- ... | inr n≤m = cancel-inl (inl y ≡⟨ sym fm↓y ⟩ f m ≡⟨ ↓-upwards-closed inc n≤m fn↓z ⟩ inl z ∎)

-- ⇓→⇓′ : ∀ {A} x {y : A} → x ↓seq y → x ↓′ y
-- ⇓→⇓′ x@(f , inc) = uncurry find-min
--     where
--       open import Cubical.Data.Nat.Order
--       find-min : ∀ {y} m → f m ≡ inl y → x ↓′ y
--       find-min 0 f0↓y = 0 , (f0↓y , (λ _ _ → zero-≤))
--       find-min {y} (suc m) f-1+m↓y with inspect (f m)
--       ... | (inr tt , fm↑) = (suc m) , (f-1+m↓y , 1+m-is-min)
--         where
--           1+m-is-min : ∀ n → (f n ≡ inr tt → ⊥) → m < n
--           1+m-is-min n ¬fn↑ with inspect (f n)
--           ... | (inr tt , fn↑) = Cubical.Data.Empty.elim (¬fn↑ fn↑)
--           ... | (inl _ , fn↓) = ↑<↓ inc fm↑ fn↓
--       ... | (inl y' , fm↓y') =
--         let temp = find-min m fm↓y' in
--         temp .fst , with-other-value (proj₁ (temp .snd)) , proj₂ (temp .snd)
--         where
--           with-other-value : ∀ {n} → f n ↓ y' → f n ↓ y
--           with-other-value = subst (_ ↓_) (termination-value-unique x (_ , fm↓y') (_ , f-1+m↓y))

-- ↓⇔∥↓∥ : ∀ {A} → isSet A → ∀ x {y : A} → (x ↓seq y → ∥ x ↓seq y ∥) × (∥ x ↓seq y ∥ → x ↓seq y)
-- ↓⇔∥↓∥ A-set x {y} =
--     (∣_∣) ,
--     ⇓′→⇓ x ∘ Cubical.HITs.PropositionalTruncation.rec (⇓′-propositional A-set x {y = y}) (⇓→⇓′ x)

-- Maybe→⊥-mono : ∀ {A : Type₀} {x y : A ⊎ Unit} → LE x y → (Maybe→⊥ x) ⊑ (Maybe→⊥ y)
-- Maybe→⊥-mono {x = x} {y} (inl p) = subst (λ a → Maybe→⊥ x ⊑ Maybe→⊥ a) p (⊑-refl (Maybe→⊥ x))
-- Maybe→⊥-mono {x = x} {y} (inr p) = subst (λ a → Maybe→⊥ a ⊑ Maybe→⊥ y) (sym (proj₁ p)) (never⊑ (Maybe→⊥ y))

-- Seq→Inc-seq : ∀ {A} → Seq A → Increasing-sequence A
-- Seq→Inc-seq (f , inc) = Maybe→⊥ ∘ f , Maybe→⊥-mono ∘ inc

-- -- Turns increasing sequences of potential values into partial values.

-- Seq→⊥ : ∀ {A} → Seq A → < A >⊥
-- Seq→⊥ = ⊔ ∘ Seq→Inc-seq

-- -- If every element in one increasing sequence is bounded by some
-- -- element in another, then the least upper bound of the first
-- -- sequence is bounded by the least upper bound of the second one.
-- private
--   ⊑→⨆⊑⨆ : ∀ {A : Set} {s₁ s₂ : Increasing-sequence A} {f : ℕ → ℕ} →
--           (∀ n → fst s₁ n ⊑ fst s₂ (f n)) → ⊔ s₁ ⊑ ⊔ s₂
--   ⊑→⨆⊑⨆ {s₁} {s₂} {f} s₁⊑s₂ =
--       least-upper-bound _ _ λ n → ⊑-trans (s₁⊑s₂ n) (upper-bound _ _)

--   -- A variant of the previous lemma.

-- private
--   ∃⊑→⨆⊑⨆ : ∀ {A : Set} {s₁ s₂ : Increasing-sequence A} →
--            (∀ m → Σ[ n ∈ ℕ ] (fst s₁  m ⊑ fst s₂ n)) → ⊔ s₁ ⊑ ⊔ s₂
--   ∃⊑→⨆⊑⨆ s₁⊑s₂ = ⊑→⨆⊑⨆ (snd ∘ s₁⊑s₂)

-- Seq→⊥-mono : ∀ {A : Set} → isSet A → ∀ (x y : Seq A) → x ⊑seq y → Seq→⊥ x ⊑ Seq→⊥ y
-- Seq→⊥-mono A-set x@(f , _) y@(g , _) x⊑y =
--   ∃⊑→⨆⊑⨆ inc
--   where
--     inc : ∀ m → Σ[ n ∈ ℕ ] (Maybe→⊥ (f m) ⊑ Maybe→⊥ (g n))
--     inc m with inspect (f m)
--     ... | (inr tt , p) = 0 , subst (λ x₁ → Maybe→⊥ x₁ ⊑ Maybe→⊥ (g 0)) (sym p) (never⊑ (Maybe→⊥ (g 0))) -- never⊑ (Maybe→⊥ (g 0))
--     ... | (inl r , p) =
--       fst y↓z ,
--       subst (λ a → Maybe→⊥ (f m) ⊑ Maybe→⊥ a) (sym (snd y↓z))
--       (subst (λ a → Maybe→⊥ a ⊑ η r) (sym p) (⊑-refl (η r)))
--       where
--         y↓z : y ↓seq r
--         y↓z = let temp = x⊑y r in let temp' = proj₂ (↓⇔∥↓∥ A-set y) ∘ temp in temp' ∣ m , p ∣

-- Seq→⊥-≈→≡ : ∀ {A} → isSet A → ∀ (x y : Seq A) → x ∼seq y → Seq→⊥ x ≡ Seq→⊥ y
-- Seq→⊥-≈→≡ A-set x y (p , q) = α (Seq→⊥-mono A-set x y p) (Seq→⊥-mono A-set y x q)

-- -- recc :
-- --   ∀ {A B : Set} {R : A → A → Set}
-- --   → (f : A → B)
-- --   → (∀ x y → R x y → f x ≡ f y)
-- --   → isSet B
-- --   → A / R → B
-- -- recc {A} {B} {R} f feq B-set ar =
-- --     Cubical.HITs.SetQuotients.elim {B = λ _ → B} (λ _ → B-set) f feq ar
-- -- recc = rec/

-- Seq/∼→⊥ : ∀ {A} → isSet A → (Seq A / _∼seq_) → < A >⊥
-- Seq/∼→⊥ {A} A-set = rec/ Seq→⊥ (Seq→⊥-≈→≡ A-set) ⊥-isSet

-- private -- useful property
--   postulate -- TODO
--     η⊑⊔ : ∀ {A : Set} s q (r : A) → η r ⊑ ⊔ (s , q) → ∥ Σ[ n ∈ ℕ ] η r ⊑ s n ∥

-- ⊑-refl-constr : ∀ {A : Set} {x y : < A >⊥} → x ≡ y → x ⊑ y
-- ⊑-refl-constr {x = x} p = transport (λ i → x ⊑ p i) (⊑-refl x)

-- -- weakly effective?
-- Seq→⊥-isInjective : ∀ {A} → (A-set : isSet A) → (s t : Seq A) → Seq→⊥ s ≡ Seq→⊥ t → s ∼seq t
-- Seq→⊥-isInjective {A} A-set s t x =
--   lemma s t x ,
--   lemma t s (sym x)
--   where
--     postulate
--       ⇓≃now⊑ : (x : Seq A) {y : A} → Iso (x ↓seq y) (η y ⊑ Seq→⊥ x)
    
--     lemma : (x y : Seq A) → Seq→⊥ x ≡ Seq→⊥ y → (∀ a → ∥ x ↓seq a ∥ → ∥ y ↓seq a ∥)
--     lemma x y p a q = ∥map∥ (λ x₁ → Iso.inv (⇓≃now⊑ y) (subst (λ k → η a ⊑ k) p (Iso.fun (⇓≃now⊑ x) x₁))) q

-- Seq/∼→⊥-isInjective : ∀ {A} → (A-set : isSet A) → isInjective (Seq/∼→⊥ A-set)
-- Seq/∼→⊥-isInjective {A} A-set {x} {y} =
--   elimProp
--     {A = Seq A}
--     {R = _∼seq_}
--     {B = λ x → Seq/∼→⊥ A-set x ≡ Seq/∼→⊥ A-set y → x ≡ y}
--     (λ x → isPropΠ λ _ → squash/ x y)
--     (λ a →
--        elimProp
--          {A = Seq A}
--          {R = _∼seq_}
--          {B = λ y → Seq→⊥ a ≡ Seq/∼→⊥ A-set y → [ a ] ≡ y}
--          (λ y → isPropΠ λ _ → squash/ [ a ] y)
--          (λ b → eq/ a b ∘ (Seq→⊥-isInjective A-set a b))
--          y)
--     x

-- Seq/∼→⊥-isEmbedding : ∀ {A} → (A-set : isSet A) → isEmbedding (Seq/∼→⊥ A-set)
-- Seq/∼→⊥-isEmbedding {A} A-set = injEmbedding squash/ ⊥-isSet (Seq/∼→⊥-isInjective A-set)

-- -- The axiom of countable choice, stated in a corresponding way.

-- Axiom-of-countable-choice : (ℓ : Level) → Set (ℓ-suc ℓ)
-- Axiom-of-countable-choice ℓ = {B : ℕ → Set ℓ} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥
  
-- private
--   postulate
--     -- the least upper bound of a constant sequence, is the constant
--     sldfkja : ∀ {A : Set} (s : < A >⊥) → ⊔ ((λ _ → s) , (λ _ → ⊑-refl s)) ≡ s

-- const-seq : ∀ {A : Set} → (s : A ⊎ Unit) → Seq→⊥ ((λ _ → s) , (λ _ → inl refl)) ≡ Maybe→⊥ s
-- const-seq s =
--   Seq→⊥ ((λ _ → s) , (λ _ → inl refl))
--     ≡⟨ refl ⟩
--   ⊔ ((λ _ → Maybe→⊥ s) , (λ _ → subst (λ a → Maybe→⊥ s ⊑ Maybe→⊥ a) refl (⊑-refl (Maybe→⊥ s))))
--     ≡⟨ cong (λ a → ⊔ ((λ _ → Maybe→⊥ s) , λ _ → a)) (substRefl {B = λ a → Maybe→⊥ s ⊑ Maybe→⊥ a} (⊑-refl (Maybe→⊥ s))) ⟩
--   ⊔ ((λ _ → Maybe→⊥ s) , (λ _ → ⊑-refl (Maybe→⊥ s)))
--     ≡⟨ sldfkja (Maybe→⊥ s) ⟩
--   Maybe→⊥ s ∎

-- elimProp⊥ :
--   ∀ {A : Set} (P : < A >⊥ → Set)
--   → (∀ a → isProp (P a))
--   → P never
--   → ((a : A) → P (η a))
--   → ((s : Σ[ s ∈ (ℕ → < A >⊥) ] ((n : ℕ) → s n ⊑ s (suc n)))
--         → ((n : ℕ) → P (fst s n)) → P (⊔ s))
--   → (x : < A >⊥) → P x
-- elimProp⊥ {A = A} P Pprop pn pη p⊔ x = temp x
--   where
--     temp : (x : < A >⊥) → P x
--     temp never = pn
--     temp (η a) = pη a
--     temp (⊔ (s , q)) = p⊔ (s , q) (temp ∘ s)
--     temp (α {x} {y} a b i) =
--       isOfHLevel→isOfHLevelDep 1 Pprop
--         (temp x) (temp y)
--         (α a b) i
--     temp (⊥-isSet a b p q i j) =
--       isOfHLevel→isOfHLevelDep 2 (isProp→isSet ∘ Pprop)
--         (temp a) (temp b)
--         (cong temp p) (cong temp q)
--         (⊥-isSet a b p q) i j

-- private
--   postulate
--     pointwise-equivalence→upper-bound-equivalence :
--       ∀ {A} (s : Increasing-sequence A)
--       → (f : ℕ → Seq A)
--       → (∀ n → Seq→⊥ (f n) ≡ fst s n)
--       -------------------------
--       → Σ[ x ∈ Seq A ] (Seq→⊥ x ≡ ⊔ s)

-- Seq→⊥-isSurjection : ∀ {A : Set} → (A-set : isSet A) → Axiom-of-countable-choice ℓ-zero → isSurjection (Seq→⊥ {A})
-- Seq→⊥-isSurjection {A} A-set cc =
--   elimProp⊥
--     (λ y → ∥ (Σ[ x ∈ Seq A ] (Seq→⊥ x ≡ y)) ∥)
--     (λ _ → propTruncIsProp)
--     ∣ ((λ _ → inr tt) , (λ _ → inl refl)) , const-seq (inr tt) ∣
--     (λ a → ∣ ((λ _ → inl a) , (λ _ → inl refl)) , const-seq (inl a) ∣)
--     λ s p →
--       let temp'3 : ∥ (Σ[ f ∈ (ℕ → Seq A) ] (∀ n → Seq→⊥ (f n) ≡ fst s n)) ∥
--           temp'3 = ∥map∥ (λ x → (λ n → x n .fst) , (λ n → x n .snd)) (cc p) in
--       let temp'4 : ∥ (Σ[ x ∈ Seq A ] (Seq→⊥ x ≡ ⊔ s)) ∥
--           temp'4 = ∥map∥ (uncurry (pointwise-equivalence→upper-bound-equivalence s)) temp'3 in
--       temp'4

-- Seq/∼→⊥-isSurjection : ∀ {A} → (A-set : isSet A) → Axiom-of-countable-choice ℓ-zero → isSurjection (Seq/∼→⊥ A-set)
-- Seq/∼→⊥-isSurjection A-set cc b =
--   ∥map∥ (λ {(x , y) → [ x ] , y}) (Seq→⊥-isSurjection A-set cc b)

-- seq/∼→⊥-isEquiv : ∀ {A} → (A-set : isSet A) → Axiom-of-countable-choice ℓ-zero → isEquiv (Seq/∼→⊥ A-set)
-- seq/∼→⊥-isEquiv A-set cc = isEmbedding×isSurjection→isEquiv ((Seq/∼→⊥-isEmbedding A-set) , (Seq/∼→⊥-isSurjection A-set cc)) 

-- seq/∼≃⊥ : ∀ {A} → isSet A → Axiom-of-countable-choice ℓ-zero → (Seq A / _∼seq_) ≃ < A >⊥
-- seq/∼≃⊥ A-set cc = Seq/∼→⊥ A-set , seq/∼→⊥-isEquiv A-set cc
