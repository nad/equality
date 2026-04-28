------------------------------------------------------------------------
-- The list container
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Container.List
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_; module _⇔_)
open import Prelude as P hiding (List; []; _∷_; id; _∘_)

import Bag-equivalence eq as BE
open import Bijection eq using (_↔_; module _↔_; Σ-≡,≡↔≡)
open import Container eq as C
  hiding (decidable-equality; decidable-erased-equality)
open import Equivalence eq as Eq using (_≃_)
open import Erased.Level-1 eq using (Decidable-erased-equality)
open import Extensionality eq
open import Fin eq
open import Function-universe eq
open import H-level eq
open import H-level.Closure eq
import Nat eq as Nat
import List eq as L
open import Surjection eq using (_↠_)
import Vec.Dependent eq as Vec

open BE.Kind

private variable
  a p              : Level
  A B              : Type a
  k lkup n x xs ys : A

------------------------------------------------------------------------
-- The type

-- Lists.

List : Container lzero
List = ℕ ▷ Fin

-- The length of a list.

length : ⟦ List ⟧ A → ℕ
length = proj₁

------------------------------------------------------------------------
-- The definitions of lists and bag equivalence for lists given in
-- Container/Container.List and in Prelude/Bag-equivalence are closely
-- related

-- There is a split surjection from ⟦ List ⟧ A to P.List A.

List↠List : ⟦ List ⟧ A ↠ P.List A
List↠List {A} = record
  { logical-equivalence = record
    { to   = uncurry to
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  to : (n : ℕ) → (Fin n → A) → P.List A
  to zero    f = P.[]
  to (suc n) f = P._∷_ (f fzero) (to n (f ∘ fsuc))

  from = λ xs → (L.length xs , L.index xs)

  to∘from : ∀ xs → uncurry to (from xs) ≡ xs
  to∘from P.[]         = refl _
  to∘from (P._∷_ x xs) = cong (P._∷_ x) (to∘from xs)

-- The surjection preserves lengths.

_ : length (_↠_.from List↠List xs) ≡ L.length xs
_ = refl _

length-List↠List : L.length (_↠_.to List↠List xs) ≡ length xs
length-List↠List {xs} =
  L.length (_↠_.to List↠List xs)                     ≡⟨⟩
  length (_↠_.from List↠List (_↠_.to List↠List xs))  ≡⟨ uncurry lemma xs ⟩∎
  length xs                                          ∎
  where
  lemma :
    ∀ n f → proj₁ (_↠_.from List↠List (_↠_.to List↠List (n , f))) ≡ n
  lemma zero    _ = refl _
  lemma (suc n) _ = cong suc $ lemma n _

-- If we assume that equality of functions is extensional, then we can
-- also prove that the two definitions are isomorphic.

List↔List :
  Extensionality lzero a →
  {A : Type a} → ⟦ List ⟧ A ↔ P.List A
List↔List ext {A} = record
  { surjection      = List↠List
  ; left-inverse-of = uncurry from∘to
  }
  where
  open _↠_ List↠List

  from∘to : ∀ n f → from (to (n , f)) ≡ (n , f)
  from∘to zero    f = cong (_,_ _) (apply-ext ext λ ())
  from∘to (suc n) f =
    let x  = f (inj₁ tt)
        xs = (n , f ∘ inj₂)
    in
    (suc (L.length (to xs)) , L.index (P._∷_ x (to xs)))  ≡⟨ elim¹ (λ {ys} _ → _≡_ {A = ⟦ List ⟧ A}
                                                                                   (suc (L.length (to xs)) , L.index (P._∷_ x (to xs)))
                                                                                   (suc (proj₁ ys) , [ (λ _ → x) , proj₂ ys ]))
                                                                   (cong (suc (L.length (to xs)) ,_) $ apply-ext ext
                                                                      [ (λ _ → refl _) , (λ _ → refl _) ])
                                                                   (from∘to n (f ∘ inj₂)) ⟩
    (suc n                  , [ (λ _ → x) , f ∘ inj₂ ])   ≡⟨ cong (_,_ _) (apply-ext ext [ (λ _ → refl _) , (λ _ → refl _) ]) ⟩∎
    (suc n                  , f)                          ∎

-- The two definitions of Any are isomorphic (both via "to" and
-- "from").

Any↔Any-to :
  (P : A → Type p) (xs : ⟦ List ⟧ A) →
  Any P xs ↔ BE.Any P (_↠_.to List↠List xs)
Any↔Any-to {A} P = uncurry Any↔Any-to′
  where
  Any↔Any-to′ : (n : ℕ) (lkup : Fin n → A) →
                Any {C = List} P (n , lkup) ↔
                BE.Any P (_↠_.to List↠List (n , lkup))
  Any↔Any-to′ zero lkup =
    (∃ λ (p : Fin zero) → P (lkup p))  ↔⟨ ∃-Fin-zero _ ⟩
    ⊥                                  □
  Any↔Any-to′ (suc n) lkup =
    (∃ λ (p : Fin (suc n)) → P (lkup p))                            ↔⟨ ∃-Fin-suc _ ⟩
    P (lkup fzero) ⊎ Any {C = List} P (n , lkup ∘ fsuc)             ↔⟨ id ⊎-cong Any↔Any-to′ n (lkup ∘ fsuc) ⟩
    P (lkup fzero) ⊎ BE.Any P (_↠_.to List↠List (n , lkup ∘ fsuc))  □

Any-from↔Any :
  (P : A → Type p) (xs : P.List A) →
  Any P (_↠_.from List↠List xs) ↔ BE.Any P xs
Any-from↔Any P P.[] =
  (∃ λ (p : Fin zero) → P (L.index P.[] p))  ↔⟨ ∃-Fin-zero _ ⟩
  ⊥                                          □
Any-from↔Any P (P._∷_ x xs) =
  (∃ λ (p : Fin (suc (L.length xs))) → P (L.index (P._∷_ x xs) p))  ↔⟨ ∃-Fin-suc _ ⟩
  P x ⊎ Any {C = List} P (_↠_.from List↠List xs)                    ↔⟨ id ⊎-cong Any-from↔Any P xs ⟩
  P x ⊎ BE.Any P xs                                                 □

-- Some lemmas relating different definitions of bag equivalence for
-- different definitions of lists.

≈-⇔-to-≈-to :
  xs ∼[ ⌊ k ⌋-iso ] ys ⇔
  _↠_.to List↠List xs BE.∼[ ⌊ k ⌋-iso ] _↠_.to List↠List ys
≈-⇔-to-≈-to {xs} {ys} = record
  { to   = λ xs≈ys z →
             z BE.∈ (_↠_.to List↠List xs)  ↔⟨ inverse $ Any↔Any-to _ xs ⟩
             z ∈ xs                        ↔⟨ xs≈ys z ⟩
             z ∈ ys                        ↔⟨ Any↔Any-to _ ys ⟩
             z BE.∈ (_↠_.to List↠List ys)  □
  ; from = λ xs≈ys z →
             z ∈ xs                        ↔⟨ Any↔Any-to _ xs ⟩
             z BE.∈ (_↠_.to List↠List xs)  ↔⟨ xs≈ys z ⟩
             z BE.∈ (_↠_.to List↠List ys)  ↔⟨ inverse $ Any↔Any-to _ ys ⟩
             z ∈ ys                        □
  }

≈-⇔-from-≈-from :
  xs BE.∼[ ⌊ k ⌋-iso ] ys ⇔
  _↠_.from List↠List xs ∼[ ⌊ k ⌋-iso ] _↠_.from List↠List ys
≈-⇔-from-≈-from {xs} {ys} = record
  { to   = λ xs≈ys z →
             z ∈ (_↠_.from List↠List xs)  ↔⟨ Any-from↔Any _ xs ⟩
             z BE.∈ xs                    ↔⟨ xs≈ys z ⟩
             z BE.∈ ys                    ↔⟨ inverse $ Any-from↔Any _ ys ⟩
             z ∈ (_↠_.from List↠List ys)  □
  ; from = λ xs≈ys z →
             z BE.∈ xs                    ↔⟨ inverse $ Any-from↔Any _ xs ⟩
             z ∈ (_↠_.from List↠List xs)  ↔⟨ xs≈ys z ⟩
             z ∈ (_↠_.from List↠List ys)  ↔⟨ Any-from↔Any _ ys ⟩
             z BE.∈ ys                    □
  }

≈-≃-from-≈-from :
  {A : Type a} {xs ys : P.List A} →
  xs BE.≈-bag ys ↝[ a ∣ a ]
  _↠_.from List↠List xs ≈-bag _↠_.from List↠List ys
≈-≃-from-≈-from {xs} {ys} =
  generalise-ext? ≈-⇔-from-≈-from λ ext →
      (λ xs≈ys → apply-ext ext λ z →
         Eq.lift-equality ext $ apply-ext ext λ z∈xs →
         _↔_.from (Any-from↔Any (z ≡_) ys)
           (_↔_.to (Any-from↔Any (z ≡_) ys)
              (_≃_.to (xs≈ys z)
                 (_↔_.from (Any-from↔Any (z ≡_) xs)
                    (_↔_.to (Any-from↔Any (z ≡_) xs) z∈xs))))  ≡⟨ _↔_.left-inverse-of (Any-from↔Any (z ≡_) ys) _ ⟩

          _≃_.to (xs≈ys z)
            (_↔_.from (Any-from↔Any (z ≡_) xs)
               (_↔_.to (Any-from↔Any (z ≡_) xs) z∈xs))         ≡⟨ cong (_≃_.to (xs≈ys z)) $
                                                                  _↔_.left-inverse-of (Any-from↔Any (z ≡_) xs) _ ⟩∎
          _≃_.to (xs≈ys z) z∈xs                                ∎)
    , (λ xs≈ys → apply-ext ext λ z →
         Eq.lift-equality ext $ apply-ext ext λ z∈xs →
         _↔_.to (Any-from↔Any (z ≡_) ys)
           (_↔_.from (Any-from↔Any (z ≡_) ys)
              (_≃_.to (xs≈ys z)
                 (_↔_.to (Any-from↔Any (z ≡_) xs)
                    (_↔_.from (Any-from↔Any (z ≡_) xs) z∈xs))))  ≡⟨ _↔_.right-inverse-of (Any-from↔Any (z ≡_) ys) _ ⟩

          _≃_.to (xs≈ys z)
            (_↔_.to (Any-from↔Any (z ≡_) xs)
               (_↔_.from (Any-from↔Any (z ≡_) xs) z∈xs))         ≡⟨ cong (_≃_.to (xs≈ys z)) $
                                                                    _↔_.right-inverse-of (Any-from↔Any (z ≡_) xs) _ ⟩∎
          _≃_.to (xs≈ys z) z∈xs                                  ∎)

------------------------------------------------------------------------
-- Constructors

[] : ⟦ List ⟧ A
[] = (zero , λ ())

infixr 5 _∷_

_∷_ : A → ⟦ List ⟧ A → ⟦ List ⟧ A
x ∷ (n , lkup) = (suc n , [ (λ _ → x) , lkup ])

-- Even if we don't assume extensionality we can prove that
-- intensionally distinct implementations of the constructors are bag
-- equivalent.

[]≈ : _≈-bag_ {C₂ = List} [] (zero , lkup)
[]≈ _ = Eq.↔→≃
  (λ { (() , _) })
  (λ { (() , _) })
  (λ { (() , _) })
  (λ { (() , _) })

∷≈ :
  _≈-bag_ {C₂ = List}
          (lkup (inj₁ tt) ∷ (n , lkup ∘ inj₂))
          (suc n , lkup)
∷≈ _ = Eq.↔→≃
  (λ { (inj₁ tt , eq) → (inj₁ tt , eq)
     ; (inj₂ s  , eq) → (inj₂ s  , eq)
     })
  (λ { (inj₁ tt , eq) → (inj₁ tt , eq)
     ; (inj₂ s  , eq) → (inj₂ s  , eq)
     })
  (λ { (inj₁ tt , eq) → refl _
     ; (inj₂ s  , eq) → refl _
     })
  (λ { (inj₁ tt , eq) → refl _
     ; (inj₂ s  , eq) → refl _
     })

-- Any lemmas for the constructors.

Any-[] : (P : A → Type p) → Any P [] ↔ ⊥₀
Any-[] _ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (() , _) }
      ; from = λ ()
      }
    ; right-inverse-of = λ ()
    }
  ; left-inverse-of = λ { (() , _) }
  }

Any-∷ : (P : A → Type p) → Any P (x ∷ xs) ↔ P x ⊎ Any P xs
Any-∷ _ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (inj₁ tt , eq) → inj₁ eq
                 ; (inj₂ s  , eq) → inj₂ (s , eq)
                 }
      ; from = λ { (inj₁ eq)       → (inj₁ tt , eq)
                 ; (inj₂ (s , eq)) → (inj₂ s  , eq)
                 }
      }
    ; right-inverse-of = λ { (inj₁ eq)       → refl _
                           ; (inj₂ (s , eq)) → refl _
                           }
    }
  ; left-inverse-of = λ { (inj₁ tt , eq) → refl _
                        ; (inj₂ s  , eq) → refl _
                        }
  }

------------------------------------------------------------------------
-- More functions

-- A fold for lists. (Well, this is not a catamorphism, it is a
-- paramorphism.)

fold : B → (A → ⟦ List ⟧ A → B → B) → ⟦ List ⟧ A → B
fold {B} {A} nl cns = uncurry fold′
  where
  fold′ : (n : ℕ) → (Fin n → A) → B
  fold′ zero    lkup = nl
  fold′ (suc n) lkup =
    cns (lkup fzero) (n , lkup ∘ fsuc) (fold′ n (lkup ∘ fsuc))

-- A lemma which can be used to prove properties about fold.
--
-- The "respects bag equivalence" argument could be omitted if
-- equality of functions were extensional.

fold-lemma :
  {nl : B} {cns : A → ⟦ List ⟧ A → B → B}
  (P : ⟦ List ⟧ A → B → Type p) →
  (∀ xs ys → xs ≈-bag ys → ∀ b → P xs b → P ys b) →
  P [] nl →
  (∀ x xs b → P xs b → P (x ∷ xs) (cns x xs b)) →
  ∀ xs → P xs (fold nl cns xs)
fold-lemma {A} {nl} {cns} P resp P-nl P-cns =
  uncurry fold′-lemma
  where
  fold′-lemma : ∀ n (lkup : Fin n → A) →
                P (n , lkup) (fold nl cns (n , lkup))
  fold′-lemma zero    lkup = resp _ _ []≈ _ P-nl
  fold′-lemma (suc n) lkup = resp _ _ ∷≈ _ $
    P-cns _ _ _ $ fold′-lemma n (lkup ∘ fsuc)

-- Why have I included both fold and fold-lemma rather than simply a
-- dependent eliminator? I tried this, and could easily define the
-- functions I wanted to define. However, the functions were defined
-- together with (partial) correctness proofs, and were unnecessarily
-- hard to read. I wanted to be able to define functions which were
-- easy to read, like the _++_ function below, and then have the
-- option to prove properties about them, like Any-++.
--
-- Unfortunately this turned out to be harder than expected. When
-- proving the Any-++ lemma it seemed as if I had to prove that _++_
-- preserves bag equivalence in its first argument in order to
-- instantiate the "respects bag equivalence" argument. However, my
-- preferred proof of this property uses Any-++…
--
-- An alternative could be to assume that equality of functions is
-- extensional, in which case the "respects bag equivalence" argument
-- could be removed. Another option would be to listen to Conor
-- McBride and avoid higher-order representations of first-order data.

-- Append.

infixr 5 _++_

_++_ : ⟦ List ⟧ A → ⟦ List ⟧ A → ⟦ List ⟧ A
xs ++ ys = fold ys (λ z _ zs → z ∷ zs) xs

-- An Any lemma for append.

Any-++ :
  ∀ (P : A → Type p) xs ys →
  Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P xs ys = fold-lemma
  (λ xs xs++ys → Any P xs++ys ↔ Any P xs ⊎ Any P ys)

  (λ us vs us≈vs us++ys hyp →
     Any P us++ys         ↔⟨ hyp ⟩
     Any P us ⊎ Any P ys  ↔⟨ Any-cong P P us vs (λ _ → id) us≈vs ⊎-cong id ⟩□
     Any P vs ⊎ Any P ys  □)

  (Any P ys             ↔⟨ inverse ⊎-left-identity ⟩
   ⊥ ⊎ Any P ys         ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩□
   Any P [] ⊎ Any P ys  □)

  (λ x xs xs++ys ih →
     Any P (x ∷ xs++ys)           ↔⟨ Any-∷ P ⟩
     P x ⊎ Any P xs++ys           ↔⟨ id ⊎-cong ih ⟩
     P x ⊎ Any P xs ⊎ Any P ys    ↔⟨ ⊎-assoc ⟩
     (P x ⊎ Any P xs) ⊎ Any P ys  ↔⟨ inverse (Any-∷ P) ⊎-cong id ⟩□
     Any P (x ∷ xs) ⊎ Any P ys    □)

  xs

------------------------------------------------------------------------
-- More results related to bag equivalence

-- Two notions of bag equivalence are pointwise equivalent (assuming
-- function extensionality).

≈≃≈′ :
  {A : Type a} {xs ys : P.List A} →
  xs BE.≈-bag ys ↝[ a ∣ a ] xs BE.≈-bag′ ys
≈≃≈′ {xs} {ys} {k} ext =
  xs BE.≈-bag ys                                         ↝⟨ ≈-≃-from-≈-from ext ⟩

  _↠_.from List↠List xs ≈-bag _↠_.from List↠List ys      ↝⟨ ≈↔≈′ (_↠_.from List↠List xs) (_↠_.from List↠List ys) ext ⟩

  _↠_.from List↠List xs ≈[ bag ]′ _↠_.from List↠List ys  ↔⟨⟩

  (∃ λ (eq : Fin (L.length xs) ≃ Fin (L.length ys)) →
   ∀ i → L.index xs i ≡ L.index ys (_≃_.to eq i))        ↔⟨ Eq.↔→≃
                                                              (λ (eq , r) → record { equivalence = eq; related = r })
                                                              _
                                                              refl
                                                              refl ⟩□
  xs BE.≈-bag′ ys                                        □

-- The type of lists that are bag equivalent to a list xs is
-- equivalent to Fin (length xs !), if a certain variant of bag
-- equivalence is used (and assuming function extensionality).

∃≈≃Fin! :
  {A : Type a} {xs : ⟦ List ⟧ A} →
  Extensionality a a →
  (∃ λ (ys : ⟦ List ⟧ A) → xs ≈-bag ys) ≃ Fin (length xs !)
∃≈≃Fin! {A} {xs = xs@(m , f)} ext =
  (∃ λ ys → xs ≈-bag ys)                      ↝⟨ ∃≈≃∃≃ ext List ⟩

  (∃ λ (n : ℕ) → Fin m ≃ Fin n)               ↔⟨ (∃-cong λ _ → inverse $ drop-⊤-right λ hyp →
                                                  _⇔_.to contractible⇔↔⊤ $
                                                  propositional⇒inhabited⇒contractible ℕ-set
                                                    (_⇔_.to isomorphic-same-size (from-equivalence hyp))) ⟩

  (∃ λ (n : ℕ) → Fin m ≃ Fin n × m ≡ n)       ↝⟨ inverse $ other-∃-intro _ _ ⟩

  Fin m ≃ Fin m                               ↝⟨ [Fin≃Fin]≃Fin! m ext₀ ⟩□

  Fin (m !)                                   □
  where
  ext₀ = lower-extensionality _ _ ext

-- The type of lists that are bag equivalent to a list xs is
-- equivalent to Fin (L.length xs !), if a certain variant of bag
-- equivalence is used (and assuming function extensionality).

∃-List-≈≃Fin! :
  {A : Type a} {xs : P.List A} →
  Extensionality a a →
  (∃ λ (ys : P.List A) → xs BE.≈-bag ys) ≃ Fin (L.length xs !)
∃-List-≈≃Fin! {A} {xs} ext =
  (∃ λ (ys : P.List A) → xs BE.≈-bag ys)                    ↝⟨ Σ-cong (inverse $ List↔List ext′) (λ _ → ≈-≃-from-≈-from ext) ⟩
  (∃ λ (ys : ⟦ List ⟧ A) → _↠_.from List↠List xs ≈-bag ys)  ↝⟨ ∃≈≃Fin! ext ⟩□
  Fin (L.length xs !)                                       □
  where
  ext′ = lower-extensionality _ lzero ext

------------------------------------------------------------------------
-- Decidable equality

-- Decidable equality for lists.

decidable-equality :
  {A : Type a} →
  Extensionality lzero a →
  Decidable-equality A →
  Decidable-equality (⟦ List ⟧ A)
decidable-equality ext dec =
  C.decidable-equality Nat._≟_
    (Vec.decidable-equality-Π-Fin ext (λ _ → dec))

-- Decidable erased equality for lists.

decidable-erased-equality :
  {A : Type a} →
  @0 Extensionality lzero a →
  Decidable-erased-equality A →
  Decidable-erased-equality (⟦ List ⟧ A)
decidable-erased-equality ext dec =
  C.decidable-erased-equality Nat._≟_
    (Vec.decidable-erased-equality-Π-Fin ext (λ _ → dec))
