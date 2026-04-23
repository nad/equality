------------------------------------------------------------------------
-- Vectors, defined using an inductive family
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Data
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (Fin)

open import Bijection eq using (_↔_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased hiding (map)
open import Erased.Stability eq
open import Fin.Data eq
open import Function-universe eq as F hiding (_∘_)
open import H-level.Closure eq
open import List eq using (length)
open import Nat eq as Nat using (pred)
open import Surjection eq using (_↠_; ↠-≡)

private variable
  a      : Level
  A B    : Type _
  x y    : A
  @0 m n : ℕ

------------------------------------------------------------------------
-- The type

-- Vectors.

infixr 5 _∷_

data Vec (A : Type a) : @0 ℕ → Type a where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

private variable
  xs ys : Vec _ _

------------------------------------------------------------------------
-- Some simple functions

-- Finds the element at the given position.

index : Vec A n → Fin n → A
index (x ∷ _)  zero    = x
index (_ ∷ xs) (suc i) = index xs i

-- Updates the element at the given position.

infix 3 _[_≔_]

_[_≔_] : Vec A n → Fin n → A → Vec A n
_[_≔_] []       ()      _
_[_≔_] (x ∷ xs) zero    y = y ∷ xs
_[_≔_] (x ∷ xs) (suc i) y = x ∷ (xs [ i ≔ y ])

-- Applies the function to every element in the vector.

map : (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Constructs a vector containing a certain number of copies of the
-- given element.

replicate : ∀ {n} → A → Vec A n
replicate {n = zero}  _ = []
replicate {n = suc _} x = x ∷ replicate x

-- The head of the vector.

head : Vec A (suc n) → A
head (x ∷ _) = x

-- The tail of the vector.

tail : Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

------------------------------------------------------------------------
-- Conversions to and from lists

-- Vectors can be converted to lists.

to-list : Vec A n → List A
to-list  []        = []
to-list (x ∷ xs) = x ∷ to-list xs

-- Lists can be converted to vectors.

from-list : (xs : List A) → Vec A (length xs)
from-list []       = []
from-list (x ∷ xs) = x ∷ from-list xs

-- ∃ (Vec A) is isomorphic to List A.

∃Vec↔List : ∃ (λ n → Vec A n) ↔ List A
∃Vec↔List {A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = to-list ∘ proj₂
      ; from = λ xs → length xs , from-list xs
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = uncurry from∘to
  }
  where
  to∘from : (xs : List A) → to-list (from-list xs) ≡ xs
  to∘from []       = refl _
  to∘from (x ∷ xs) = cong (x ∷_) (to∘from xs)

  tail′ : A → ∃ (λ n → Vec A n) ↠ ∃ (λ n → Vec A n)
  tail′ y = record
    { logical-equivalence = record
      { to   = λ where
                 (suc n , _ ∷ xs) → n , xs
                 xs@(zero , _)    → xs
      ; from = Σ-map suc (y ∷_)
      }
    ; right-inverse-of = refl
    }

  from∘to :
    ∀ n (xs : Vec A n) →
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)
  from∘to zero    []       = refl _
  from∘to (suc n) (x ∷ xs) =                                    $⟨ from∘to n xs ⟩
    (length (to-list xs) , from-list (to-list xs)) ≡ (n , xs)   ↝⟨ _↠_.from $ ↠-≡ (tail′ x) ⟩□

    (length (to-list (x ∷ xs)) , from-list (to-list (x ∷ xs)))
      ≡
    (suc n , x ∷ xs)                                            □

opaque

  -- The function to-list preserves the length.

  length-to-list : ∀ {n} (xs : Vec A n) → length (to-list xs) ≡ n
  length-to-list xs =
    cong proj₁ (_↔_.left-inverse-of ∃Vec↔List (_ , xs))

-- ∃ (λ (([ n ]) : Erased ℕ) → Vec A n) is equivalent to List A.

∃Erased-Vec≃List : ∃ (λ (([ n ]) : Erased ℕ) → Vec A n) ≃ List A
∃Erased-Vec≃List {A} =
  Eq.↔→≃ (to-list ∘ proj₂) (λ xs → [ _ ] , from-list xs)
    (_↔_.right-inverse-of ∃Vec↔List) from-to
  where
  opaque
    from-to :
      ((n , xs) : ∃ (λ (([ n ]) : Erased ℕ) → Vec A n)) →
      _≡_ {A = ∃ (λ (([ n ]) : Erased ℕ) → Vec A n)}
        ([ length (to-list xs) ] , from-list (to-list xs)) (n , xs)
    from-to ([ _ ] , [])     = refl _
    from-to ([ _ ] , x ∷ xs) =
      cong (Σ-map (Erased.map suc) (x ∷_)) (from-to ([ _ ] , xs))

-- Vec A n is equivalent to ∃ λ (xs : List A) → Erased (length xs ≡ n)
-- (in the presence of []-cong).

Vec≃∃List-Erased :
  {A : Type a} →
  []-cong-axiomatisation lzero →
  Vec A n ≃ ∃ λ (xs : List A) → Erased (length xs ≡ n)
Vec≃∃List-Erased {n} {A} ax =
  Vec A n                                                           ↔⟨ inverse $ drop-⊤-left-Σ $
                                                                       Erased-⊤↔⊤ F.∘
                                                                       Erased-cong.Erased-cong-↔ ax ax
                                                                         (_⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩

  (∃ λ (([ m , _ ]) : Erased (∃ λ (m : ℕ) → m ≡ n)) → Vec A m)      ↝⟨ (Σ-cong Erased-Σ↔Σ λ { [ _ ] → F.id }) ⟩

  (∃ λ (([ m ] , _) : ∃ λ (([ m ]) : Erased ℕ) → Erased (m ≡ n)) →
   Vec A m)                                                         ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (([ m ]) : Erased ℕ) → Erased (m ≡ n) × Vec A m)             ↔⟨ (∃-cong λ _ → ×-comm) ⟩

  (∃ λ (([ m ]) : Erased ℕ) → Vec A m × Erased (m ≡ n))             ↔⟨ Σ-assoc ⟩

  (∃ λ (([ m ] , _) : ∃ (λ (([ m ]) : Erased ℕ) → Vec A m)) →
   Erased (m ≡ n))                                                  ↝⟨ (Σ-cong-contra (inverse ∃Erased-Vec≃List) λ _ → F.id) ⟩

  (∃ λ (xs : List A) → Erased (length xs ≡ n))                      □

-- If n is not erased, then Vec A n is equivalent, with erased proofs,
-- to ∃ λ (xs : List A) → Erased (length xs ≡ n).

Vec≃ᴱ∃List-Erased :
  ∀ {A : Type a} {n} →
  Vec A n ≃ᴱ ∃ λ (xs : List A) → Erased (length xs ≡ n)
Vec≃ᴱ∃List-Erased {A} {n} = EEq.↔→≃ᴱ
  (λ xs → to-list xs , [ length-to-list xs ])
  (λ (xs , eq) →
     subst (λ n → Vec A n) (Dec→Stable (length xs Nat.≟ n) eq)
       (from-list xs))
  (λ (xs , eq) →
     _↔_.to
       (ignore-propositional-component $
        Erased.[]-cong₁.H-level-Erased
          erased-instance-of-[]-cong-axiomatisation 1 ℕ-set)
       (elim¹
          (λ eq →
             to-list (subst (λ n → Vec A n) eq (from-list xs)) ≡ xs)
          (to-list
             (subst (λ n → Vec A n) (refl (length xs)) (from-list xs))  ≡⟨ cong to-list (subst-refl _ _) ⟩

           to-list (from-list xs)                                       ≡⟨ _↔_.right-inverse-of ∃Vec↔List _ ⟩∎

           xs                                                           ∎)
          (Dec→Stable (length xs Nat.≟ n) eq)))
  (λ xs →
     let eq = _↔_.left-inverse-of ∃Vec↔List _ in

     subst (λ n → Vec A n)
       (Dec→Stable (length (to-list xs) Nat.≟ n) [ length-to-list xs ])
       (from-list (to-list xs))                                          ≡⟨ cong (λ eq → subst (λ n → Vec A n) eq (from-list (to-list xs))) $
                                                                                 ℕ-set _ _ ⟩

     subst (λ n → Vec A n) (cong proj₁ eq) (from-list (to-list xs))      ≡⟨ sym (subst-∘ _ _ _) ⟩

     subst (λ (n , _) → Vec A n) eq (from-list (to-list xs))             ≡⟨ elim₁ (λ {p} eq → subst (λ (n , _) → Vec A n) eq (proj₂ p) ≡ xs)
                                                                                   (subst-refl _ _)
                                                                                   _ ⟩∎
     xs                                                                  ∎)

------------------------------------------------------------------------
-- Some rearrangement lemmas

-- A rearrangement lemma for subst and _∷_.

push-subst-∷ :
  ∀ {m n} {xs} {eq : m ≡ n} →
  subst (λ n → Vec A (suc n)) eq (x ∷ xs) ≡
  x ∷ subst (λ n → Vec A n) eq xs
push-subst-∷ {A} {x} {m} {xs} {eq} =
  elim¹
    (λ eq →
       ∀ xs →
       subst (λ n → Vec A (suc n)) eq (x ∷ xs) ≡
       x ∷ subst (λ n → Vec A n) eq xs)
    (λ xs →
       subst (λ n → Vec A (suc n)) (refl m) (x ∷ xs)  ≡⟨ subst-refl _ _ ⟩
       x ∷ xs                                         ≡⟨ sym (cong (_ ∷_) (subst-refl (λ _ → Vec _ _) _)) ⟩∎
       x ∷ subst (λ n → Vec A n) (refl m) xs          ∎)
    eq _

-- A variant of push-subst-∷.

push-subst-∷′ :
  ∀ {m n} {xs} {eq₁ : suc m ≡ suc n} {eq₂ : m ≡ n} →
  subst (λ n → Vec A n) eq₁ (x ∷ xs) ≡
  x ∷ subst (λ n → Vec A n) eq₂ xs
push-subst-∷′ {A} {x} {xs} {eq₁} {eq₂} =
  subst (λ n → Vec A n) eq₁ (x ∷ xs)             ≡⟨ cong (λ eq → subst (λ n → Vec A n) eq _) (ℕ-set _ _) ⟩
  subst (λ n → Vec A n) (cong suc eq₂) (x ∷ xs)  ≡⟨ sym (subst-∘ _ _ _) ⟩
  subst (λ n → Vec A (suc n)) eq₂ (x ∷ xs)       ≡⟨ push-subst-∷ ⟩∎
  x ∷ subst (λ n → Vec A n) eq₂ xs               ∎

-- A rearrangement lemma for substᴱ and _∷_.

push-substᴱ-∷ :
  {@0 eq : m ≡ n}
  (ax : []-cong-axiomatisation lzero) →
  let open Erased.[]-cong₁ ax in
  substᴱ (λ n → Vec A (suc n)) eq (x ∷ xs) ≡
  x ∷ substᴱ (Vec A) eq xs
push-substᴱ-∷ {m} {A} {x} {xs} {eq} ax =
  elim¹ᴱ
    (λ eq →
       ∀ xs →
       substᴱ (λ n → Vec A (suc n)) eq (x ∷ xs) ≡
       x ∷ substᴱ (Vec A) eq xs)
    (λ xs →
       substᴱ (λ n → Vec A (suc n)) (refl m) (x ∷ xs)  ≡⟨ substᴱ-refl ⟩
       x ∷ xs                                          ≡⟨ sym (cong (_ ∷_) (substᴱ-refl {P = Vec _})) ⟩∎
       x ∷ substᴱ (Vec A) (refl m) xs                  ∎)
    eq _
  where
  open Erased.[]-cong₁ ax

-- A variant of push-substᴱ-∷.

push-substᴱ-∷′ :
  {@0 eq₁ : suc m ≡ suc n} {@0 eq₂ : m ≡ n}
  (ax : []-cong-axiomatisation lzero) →
  let open Erased.[]-cong₁ ax in
  substᴱ (Vec A) eq₁ (x ∷ xs) ≡
  x ∷ substᴱ (Vec A) eq₂ xs
push-substᴱ-∷′ {A} {x} {xs} {eq₁} {eq₂} ax =
  substᴱ (Vec A) eq₁ (x ∷ xs)                ≡⟨ congᴱ (λ eq → substᴱ (Vec A) eq (x ∷ xs)) (ℕ-set _ _) ⟩
  substᴱ (Vec A) (cong suc eq₂) (x ∷ xs)     ≡⟨ sym (substᴱ-∘ (Vec _)) ⟩
  substᴱ (λ n → Vec A (suc n)) eq₂ (x ∷ xs)  ≡⟨ push-substᴱ-∷ ax ⟩∎
  x ∷ substᴱ (Vec A) eq₂ xs                  ∎
  where
  open Erased.[]-cong₁ ax
  open Erased.[]-cong₂ ax ax

------------------------------------------------------------------------
-- Some equality tests

-- An equality test for vectors of equal length.
--
-- Note that the length is erased.

decidable-erased-equality₁ :
  Decidable-erased-equality A →
  Decidable-erased-equality (Vec A n)
decidable-erased-equality₁ _ [] [] =
  yes [ refl _ ]
decidable-erased-equality₁ dec (x ∷ xs) (y ∷ ys) with dec x y
… | no [ x≢y ]  = no [ x≢y ∘ cong head ]
… | yes [ x≡y ] with decidable-erased-equality₁ dec xs ys
…   | yes [ xs≡ys ] = yes [ cong₂ _∷_ x≡y xs≡ys ]
…   | no [ xs≢ys ]  = no [ xs≢ys ∘ cong tail ]

private

  -- A lemma used below.

  @0 decidable-erased-equality-lemma :
    (eq : suc m ≡ suc n) →
    subst (λ n → Vec A n) eq (x ∷ xs) ≡ y ∷ ys →
    x ∷ subst (λ n → Vec A n) (cong pred eq) xs ≡ y ∷ ys
  decidable-erased-equality-lemma {A} {x} {xs} {y} {ys} eq₁ eq₂ =
    x ∷ subst (λ n → Vec A n) (cong pred eq₁) xs  ≡⟨ sym push-subst-∷′ ⟩
    subst (λ n → Vec A n) eq₁ (x ∷ xs)            ≡⟨ eq₂ ⟩∎
    y ∷ ys                                        ∎

-- An equality test for vectors of possibly different, erased lengths.
--
-- Note that the lengths are erased.

decidable-erased-equality :
  Decidable-erased-equality A →
  (xs : Vec A m) (ys : Vec A n) →
  Dec-Erased (∃ λ (eq : m ≡ n) → subst (λ n → Vec A n) eq xs ≡ ys)
decidable-erased-equality _ [] [] =
  yes [ (refl _ , subst-refl _ _) ]
decidable-erased-equality _ [] (_ ∷ _) =
  no [ Nat.0≢+ ∘ proj₁ ]
decidable-erased-equality _ (_ ∷ _) [] =
  no [ Nat.0≢+ ∘ sym ∘ proj₁ ]
decidable-erased-equality {A} dec (x ∷ xs) (y ∷ ys) with dec x y
… | no [ x≢y ] =
  no [ (λ (eq₁ , eq₂) →
          x≢y $ cong head (decidable-erased-equality-lemma eq₁ eq₂))
     ]
… | yes [ x≡y ] with decidable-erased-equality dec xs ys
…   | yes [ (m≡n , xs≡ys) ] =
      yes [ ( cong suc m≡n
            , (subst (λ n → Vec A n) (cong suc m≡n) (x ∷ xs)  ≡⟨ push-subst-∷′ ⟩
               x ∷ subst (λ n → Vec A n) m≡n xs               ≡⟨ cong₂ _∷_ x≡y xs≡ys ⟩∎
               y ∷ ys                                         ∎)
            )
          ]
…   | no [ xs≢ys ] =
      no [ (λ (eq₁ , eq₂) →
              xs≢ys
                (cong pred eq₁ ,
                 cong tail (decidable-erased-equality-lemma eq₁ eq₂)))
         ]

-- An equality test for vectors of equal length.
--
-- Note that the length is erased.

decidable-equality₁ :
  Decidable-equality A →
  Decidable-equality (Vec A n)
decidable-equality₁ _ [] [] =
  yes (refl _)
decidable-equality₁ dec (x ∷ xs) (y ∷ ys) with dec x y
… | no x≢y  = no (x≢y ∘ cong head)
… | yes x≡y with decidable-equality₁ dec xs ys
…   | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
…   | no xs≢ys  = no (xs≢ys ∘ cong tail)

private

  -- A lemma used below.

  decidable-equality-lemma :
    ∀ {A : Type a} {x xs y ys}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    (@0 eq : suc m ≡ suc n) →
    substᴱ (Vec A) eq (x ∷ xs) ≡ y ∷ ys →
    x ∷ substᴱ (Vec A) (cong pred eq) xs ≡ y ∷ ys
  decidable-equality-lemma {A} {x} {xs} {y} {ys} ax eq₁ eq₂ =
    x ∷ substᴱ (Vec A) (cong pred eq₁) xs  ≡⟨ sym (push-substᴱ-∷′ ax) ⟩
    substᴱ (Vec A) eq₁ (x ∷ xs)            ≡⟨ eq₂ ⟩∎
    y ∷ ys                                 ∎
    where
    open Erased.[]-cong₁ ax

-- An equality test for vectors of possibly different lengths.
--
-- Note that the lengths are erased.

decidable-equality :
  (ax : []-cong-axiomatisation lzero) →
  let open Erased.[]-cong₁ ax in
  Decidable-equality A →
  (xs : Vec A m) (ys : Vec A n) →
  Dec (∃ λ (([ eq ]) : Erased (m ≡ n)) → substᴱ (Vec A) eq xs ≡ ys)
decidable-equality ax _ [] [] =
  yes ([ refl _ ] , []-cong₁.substᴱ-refl ax {P = Vec _})
decidable-equality _ _ [] (_ ∷ _) =
  no (λ { ([ eq ] , _) → ⊥-elim₀ (Nat.0≢+ eq) })
decidable-equality _ _ (_ ∷ _) [] =
  no (λ { ([ eq ] , _) → ⊥-elim₀ (Nat.0≢+ (sym eq)) })
decidable-equality {A} ax dec (x ∷ xs) (y ∷ ys) with dec x y
… | no x≢y =
  no (λ ([ eq₁ ] , eq₂) →
        x≢y (cong head (decidable-equality-lemma ax eq₁ eq₂)))
… | yes x≡y with decidable-equality ax dec xs ys
…   | yes ([ m≡n ] , xs≡ys) =
      yes ( [ cong suc m≡n ]
          , (let open Erased.[]-cong₁ ax in
             substᴱ (Vec A) (cong suc m≡n) (x ∷ xs)  ≡⟨ push-substᴱ-∷′ ax ⟩
             x ∷ substᴱ (Vec A) m≡n xs               ≡⟨ cong₂ _∷_ x≡y xs≡ys ⟩∎
             y ∷ ys                                  ∎)
          )
…   | no xs≢ys =
      no (λ ([ eq₁ ] , eq₂) →
            xs≢ys
              ([ cong pred eq₁ ] ,
               cong tail (decidable-equality-lemma ax eq₁ eq₂)))
