------------------------------------------------------------------------
-- A forded variant of the vectors in Vec.Data
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Data.Forded
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (Fin)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased hiding (map)
open import Erased.Stability eq as ES
open import Fin.Data.Forded eq hiding (cast; elim)
open import Function-universe eq hiding (_∘_)
open import H-level eq
open import H-level.Closure eq
open import Nat eq as Nat using (pred)
import Vec.Data eq as D
import Vec.Data.Forded.Non-erased-lengths eq as L

private variable
  a b p    : Level
  @0 A B   : Type _
  x y      : A
  @0 m n o : ℕ

------------------------------------------------------------------------
-- The type

-- Vectors.

data Vec (A : Type a) (@0 n : ℕ) : Type a where
  nil⁼  : (@0 eq : zero ≡ n) → Vec A n
  cons⁼ : A → Vec A m → (@0 eq : suc m ≡ n) → Vec A n

private variable
  xs ys : Vec _ _

opaque

  -- An eliminator for Vec.

  elim⁼ :
    (@0 P : ∀ {n} → Vec A n → Type p) →
    (∀ {@0 n} (@0 eq : zero ≡ n) → P (nil⁼ eq)) →
    (∀ {@0 m n} (x : A) (xs : Vec A m) (@0 eq : suc m ≡ n) → P xs →
     P (cons⁼ x xs eq)) →
    (xs : Vec A n) → P xs
  elim⁼ P n c (nil⁼ eq)       = n eq
  elim⁼ P n c (cons⁼ x xs eq) = c x xs eq (elim⁼ P n c xs)

------------------------------------------------------------------------
-- A non-forded interface to Vec

opaque

  -- A variant of nil⁼.

  nil : Vec A 0
  nil = nil⁼ (refl _)

opaque

  -- A variant of cons⁼.

  cons : A → Vec A n → Vec A (suc n)
  cons x xs = cons⁼ x xs (refl _)

opaque
  unfolding nil cons

  -- An eliminator for Vec.

  elim :
    []-cong-axiomatisation lzero →
    (P : ∀ {@0 n} → Vec A n → Type p) →
    P nil →
    (∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    (xs : Vec A n) → P xs
  elim ax P n c =
    elim⁼ P (λ eq → elim¹ᴱ (λ eq → P (nil⁼ eq)) n eq)
      (λ x xs eq p → elim¹ᴱ (λ eq → P (cons⁼ x xs eq)) (c x xs p) eq)
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding elim elim⁼ nil

  -- A "computation" rule.

  elim-nil :
    {ax : []-cong-axiomatisation lzero}
    {P : ∀ {@0 n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elim ax P pⁿ pᶜ nil ≡ pⁿ
  elim-nil {ax} {P} {pⁿ} {pᶜ} =
    elim ax P pⁿ pᶜ nil                         ≡⟨⟩
    elim¹ᴱ (λ eq → P (nil⁼ eq)) pⁿ (refl zero)  ≡⟨ elim¹ᴱ-refl (λ eq → P (nil⁼ eq)) ⟩∎
    pⁿ                                          ∎
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding elim elim⁼ cons

  -- A "computation" rule.

  elim-cons :
    {ax : []-cong-axiomatisation lzero}
    {P : ∀ {@0 n} → Vec A n → Type p} {pⁿ : P nil}
    {x : A} {xs : Vec A n}
    {pᶜ : ∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elim ax P pⁿ pᶜ (cons x xs) ≡ pᶜ x xs (elim ax P pⁿ pᶜ xs)
  elim-cons {n} {ax} {P} {pⁿ} {x} {xs} {pᶜ} =
    elim ax P pⁿ pᶜ (cons x xs)                                       ≡⟨⟩

    elim¹ᴱ (λ eq → P (cons⁼ x xs eq)) (pᶜ x xs (elim ax P pⁿ pᶜ xs))
      (refl (suc n))                                                  ≡⟨ elim¹ᴱ-refl (λ eq → P (cons⁼ x xs eq)) ⟩∎

    pᶜ x xs (elim ax P pⁿ pᶜ xs)                                      ∎
    where
    open Erased.[]-cong₁ ax

-- A non-dependent eliminator for Vec.

rec : B → (∀ {@0 n} → A → Vec A n → B → B) → Vec A n → B
rec {B} n c = elim⁼ (λ _ → B) (λ _ → n) (λ x xs _ → c x xs)

opaque
  unfolding elim⁼ nil

  -- A computation rule.

  _ :
    {B : Type b} {bⁿ : B}
    {bᶜ : ∀ {@0 n} → A → Vec A n → B → B} →
    rec bⁿ bᶜ nil ≡ bⁿ
  _ = refl _

opaque
  unfolding elim⁼ cons

  -- A computation rule.

  _ :
    {B : Type b} {bⁿ : B} {xs : Vec A n}
    {bᶜ : ∀ {@0 n} → A → Vec A n → B → B} →
    rec bⁿ bᶜ (cons x xs) ≡ bᶜ x xs (rec bⁿ bᶜ xs)
  _ = refl _

opaque
  unfolding nil cons

  -- A variant of elim, defined under the assumption that unlimited
  -- erased matches are allowed for identity types.

  elimᵁ :
    Unlimited-erased-matches lzero p →
    (@0 P : ∀ {n} → Vec A n → Type p) →
    P nil →
    (∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    (xs : Vec A n) → P xs
  elimᵁ (Jᴱ , _) P n c =
    elim⁼ P (λ eq → Jᴱ (λ eq → P (nil⁼ eq)) n eq)
      (λ x xs eq p → Jᴱ (λ eq → P (cons⁼ x xs eq)) (c x xs p) eq)

opaque
  unfolding elim⁼ elimᵁ nil

  -- A "computation" rule.

  elimᵁ-nil :
    {ax : Unlimited-erased-matches lzero p}
    {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elimᵁ ax P pⁿ pᶜ nil ≡ pⁿ
  elimᵁ-nil {ax = ax@(Jᴱ , Jᴱ-refl)} {P} {pⁿ} {pᶜ} =
    elimᵁ ax P pⁿ (λ {n = n} → pᶜ {n = n}) nil  ≡⟨⟩
    Jᴱ (λ eq → P (nil⁼ eq)) pⁿ (refl zero)      ≡⟨ Jᴱ-refl (λ eq → P (nil⁼ eq)) ⟩∎
    pⁿ                                          ∎

opaque
  unfolding elim⁼ elimᵁ cons

  -- A "computation" rule.

  elimᵁ-cons :
    {ax : Unlimited-erased-matches lzero p}
    {P : ∀ {@0 n} → Vec A n → Type p} {pⁿ : P nil}
    {x : A} {xs : Vec A n}
    {pᶜ : ∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elimᵁ ax P pⁿ pᶜ (cons x xs) ≡ pᶜ x xs (elimᵁ ax P pⁿ pᶜ xs)
  elimᵁ-cons {n} {ax = ax@(Jᴱ , Jᴱ-refl)} {P} {pⁿ} {x} {xs} {pᶜ} =
    elimᵁ ax P pⁿ pᶜ (cons x xs)                                   ≡⟨⟩

    Jᴱ (λ eq → P (cons⁼ x xs eq)) (pᶜ x xs (elimᵁ ax P pⁿ pᶜ xs))
      (refl (suc n))                                               ≡⟨ Jᴱ-refl (λ eq → P (cons⁼ x xs eq)) ⟩∎

    pᶜ x xs (elimᵁ ax P pⁿ pᶜ xs)                                  ∎

------------------------------------------------------------------------
-- A cast lemma

opaque

  -- A cast function for vectors.

  cast : @0 m ≡ n → Vec A m → Vec A n
  cast eq₁ (nil⁼ eq₂)       = nil⁼ (trans eq₂ eq₁)
  cast eq₁ (cons⁼ x xs eq₂) = cons⁼ x xs (trans eq₂ eq₁)

opaque
  unfolding cast

  -- A simplification lemma.

  cast-refl :
    []-cong-axiomatisation lzero →
    cast (refl n) xs ≡ xs
  cast-refl {xs = nil⁼ eq} ax =
    congᴱ nil⁼ (trans-reflʳ eq)
    where
    open Erased.[]-cong₁ ax
  cast-refl {xs = cons⁼ _ _ eq} ax =
    congᴱ (cons⁼ _ _) (trans-reflʳ eq)
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cast

  -- A simplification lemma.

  cast-cong-pred-refl :
    []-cong-axiomatisation lzero →
    cast (cong pred (refl (suc n))) xs ≡ xs
  cast-cong-pred-refl {n} {xs} ax =
    cast (cong pred (refl (suc n))) xs  ≡⟨ congᴱ (λ eq → cast eq _) (cong-refl _) ⟩
    cast (refl n) xs                    ≡⟨ cast-refl ax ⟩∎
    xs                                  ∎
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cons

  -- A simplification lemma.

  cons-cast-cong-pred :
    {A : Type a} {x : A} {xs : Vec A m} {@0 eq : suc m ≡ suc n} →
    []-cong-axiomatisation lzero →
    cons x (cast (cong pred eq) xs) ≡ cons⁼ x xs eq
  cons-cast-cong-pred {m} {x} {xs} {eq} ax =
    cons x (cast (cong pred eq) xs)                     ≡⟨ elim¹ᴱ
                                                             (λ eq → cons x (cast (cong pred eq) xs) ≡ cons⁼ x xs (cong suc (cong pred eq)))
                                                             (
      cons x (cast (cong pred (refl (suc m))) xs)             ≡⟨ cong (cons _) (cast-cong-pred-refl ax) ⟩
      cons x xs                                               ≡⟨ congᴱ (cons⁼ _ _) (sym (trans (cong (cong _) (cong-refl _)) (cong-refl _))) ⟩∎
      cons⁼ x xs (cong suc (cong pred (refl (suc m))))        ∎)
                                                             eq ⟩
    cons⁼ x xs (cong suc (cong pred eq))                ≡⟨ congᴱ (cons⁼ _ _) (_↔_.left-inverse-of suc≡suc↔ _) ⟩∎
    cons⁼ x xs eq                                       ∎
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cons

  -- A definition used to state the type of cons-cast-cong-pred-refl.

  Cons-cast-cong-pred-refl :
    []-cong-axiomatisation lzero →
    {A : Type a} (x : A) (xs : Vec A n) →
    Type a
  Cons-cast-cong-pred-refl {n} ax x xs =
    cons-cast-cong-pred {x = x} {xs = xs} {eq = refl (suc n)} ax ≡
    cong (cons x) (cast-cong-pred-refl ax)

opaque
  unfolding Cons-cast-cong-pred-refl cons-cast-cong-pred

  -- A simplification lemma.

  cons-cast-cong-pred-refl :
    {ax : []-cong-axiomatisation lzero}
    {A : Type a} {x : A} {xs : Vec A n} →
    Cons-cast-cong-pred-refl ax x xs
  cons-cast-cong-pred-refl {ax} {x} {xs} =
    trans
      (elim¹ᴱ
         (λ eq →
            cons x (cast (cong pred eq) xs) ≡
            cons⁼ x xs (cong suc (cong pred eq)))
         (trans (cong (cons _) (cast-cong-pred-refl ax)) $
          congᴱ (cons⁼ _ _)
            (sym (trans (cong (cong _) (cong-refl _)) (cong-refl _))))
         (refl _))
      (congᴱ (cons⁼ _ _) (_↔_.left-inverse-of suc≡suc↔ _))              ≡⟨ cong (flip trans _) $
                                                                           elim¹ᴱ-refl
                                                                             (λ eq →
                                                                                cons _ (cast (cong _ eq) _) ≡
                                                                                cons⁼ _ _ (cong _ (cong pred eq))) ⟩
    trans
      (trans (cong (cons _) (cast-cong-pred-refl ax)) $
       congᴱ (cons⁼ _ _)
         (sym (trans (cong (cong _) (cong-refl _)) (cong-refl _))))
      (congᴱ (cons⁼ _ _) (_↔_.left-inverse-of suc≡suc↔ _))              ≡⟨ trans (trans-assoc _ _ _) $
                                                                           cong (trans _) $
                                                                           sym (congᴱ-trans {f = cons⁼ _ _}) ⟩
    trans (cong (cons _) (cast-cong-pred-refl ax))
      (congᴱ (cons⁼ _ _)
         (trans
            (sym (trans (cong (cong _) (cong-refl _)) (cong-refl _)))
            (_↔_.left-inverse-of suc≡suc↔ _)))                          ≡⟨ congᴱ
                                                                             (λ eq →
                                                                                trans (cong (cons _) (cast-cong-pred-refl _))
                                                                                  (congᴱ (cons⁼ _ _) eq))
                                                                             (mono₁ 2 ℕ-set _ _) ⟩
    trans (cong (cons _) (cast-cong-pred-refl ax))
      (congᴱ (cons⁼ _ _) (refl _))                                      ≡⟨ cong (trans _) (congᴱ-refl {f = cons⁼ _ _}) ⟩

    trans (cong (cons _) (cast-cong-pred-refl ax)) (refl _)             ≡⟨ trans-reflʳ _ ⟩∎

    cong (cons _) (cast-cong-pred-refl ax)                              ∎
    where
    open Erased.[]-cong₁ ax

------------------------------------------------------------------------
-- Some simple functions

opaque

  -- Finds the element at the given position.

  index : Vec A n → Fin n → A
  index (nil⁼ p)      (zero q)   = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  index (nil⁼ p)      (suc _ q)  = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  index (cons⁼ x _ _) (zero _)   = x
  index (cons⁼ _ xs p) (suc i q) =
    index (cast (Nat.cancel-suc (trans p (sym q))) xs) i

opaque

  -- Updates the element at the given position.

  infix 3 _[_≔_]

  _[_≔_] : Vec A n → Fin n → A → Vec A n
  nil⁼ p       [ zero q  ≔ _ ] = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  nil⁼ p       [ suc _ q ≔ _ ] = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  cons⁼ _ xs p [ zero _  ≔ y ] = cons⁼ y xs p
  cons⁼ x xs p [ suc i q ≔ y ] =
    cons⁼ x (cast (Nat.cancel-suc (trans p (sym q))) xs [ i ≔ y ]) q

opaque

  -- Applies the function to every element in the vector.

  map : (A → B) → Vec A n → Vec B n
  map _ (nil⁼ eq)       = nil⁼ eq
  map f (cons⁼ x xs eq) = cons⁼ (f x) (map f xs) eq

opaque

  -- Constructs a vector containing a certain number of copies of the
  -- given element.

  replicate : ∀ {n} → A → Vec A n
  replicate {n = zero}  _ = nil
  replicate {n = suc _} x = cons x (replicate x)

opaque

  -- The head of the vector.

  head : Vec A (suc n) → A
  head (nil⁼ eq)     = ⊥-elim₀ (Nat.0≢+ eq)
  head (cons⁼ x _ _) = x

opaque

  -- The tail of the vector.

  tail : Vec A (suc n) → Vec A n
  tail (nil⁼ eq)       = ⊥-elim₀ (Nat.0≢+ eq)
  tail (cons⁼ _ xs eq) = cast (Nat.cancel-suc eq) xs

opaque
  unfolding cons head tail

  -- Vec A (suc n) is equivalent to A × Vec A n (in the presence of
  -- []-cong).

  Vec-suc≃ :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    Vec A (suc n) ≃ (A × Vec A n)
  Vec-suc≃ {n} {A} ax = Eq.↔→≃
    (λ xs → head xs , tail xs)
    (uncurry cons)
    (λ (x , xs) →
       x , cast (Nat.cancel-suc (refl (suc n))) xs  ≡⟨ cong (_,_ _) (congᴱ (λ eq → cast eq xs) (cong-refl _)) ⟩
       x , cast (refl n) xs                         ≡⟨ cong (_,_ _) (cast-refl ax) ⟩∎
       x , xs                                       ∎)
    (λ where
       (nil⁼ eq)     → ⊥-elim₀ (Nat.0≢+ eq)
       (cons⁼ _ _ _) → cons-cast-cong-pred ax)
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding Vec-suc≃

  -- Vec A (suc n) is equivalent (with erased proofs) to A × Vec A n.

  Vec-suc≃ᴱ : Vec A (suc n) ≃ᴱ (A × Vec A n)
  Vec-suc≃ᴱ =
    EEq.[≃]→≃ᴱ
      (EEq.[proofs]
         (Vec-suc≃ erased-instance-of-[]-cong-axiomatisation))

------------------------------------------------------------------------
-- An observation

opaque
  unfolding elim⁼ nil cons

  -- If a function with the type of elim (but without the first
  -- explicit argument) can be implemented, then a family of special
  -- cases of []-cong (without computation rules) can be implemented.

  elim→[]-cong-ℕ :
    (∀ {a p} {@0 A : Type a} {@0 n}
     (P : ∀ {@0 n} → Vec A n → Type p) →
     P nil →
     (∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
     (xs : Vec A n) → P xs) →
    {m : ℕ} → @0 m ≡ n → [ m ] ≡ [ n ]
  elim→[]-cong-ℕ elim {m = zero} eq =
    elim
      (elim⁼ (λ _ → Type) (λ {n} _ → [ zero ] ≡ [ n ]) (λ _ _ _ _ → ⊤))
      (refl [ zero ]) (λ _ _ _ → tt) (nil⁼ {A = ⊤} eq)
  elim→[]-cong-ℕ elim {m = suc _} eq =
    elim
      (elim⁼ (λ _ → Type) (λ _ → ⊤)
         (λ {m n} _ _ _ _ → [ suc m ] ≡ [ n ]))
      tt (λ {n} _ _ _ → refl [ suc n ]) (cons⁼ tt (replicate tt) eq)

------------------------------------------------------------------------
-- Some rearrangement lemmas

opaque
  unfolding nil

  -- A rearrangement lemma for substᴱ and nil⁼.

  push-substᴱ-nil⁼ :
    {A : Type a} {@0 eq₁ : zero ≡ m} {@0 eq₂ : m ≡ n}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Vec A) eq₂ (nil⁼ eq₁) ≡ nil⁼ (trans eq₁ eq₂)
  push-substᴱ-nil⁼ {n} {A} ax =
    elim₁ᴱ
      (λ eq₂ →
         ∀ (@0 eq₁) →
         substᴱ (Vec A) eq₂ (nil⁼ eq₁) ≡ nil⁼ (trans eq₁ eq₂))
      (λ eq →
         substᴱ (Vec A) (refl n) (nil⁼ eq)  ≡⟨ substᴱ-refl ⟩
         nil⁼ eq                            ≡⟨ congᴱ nil⁼ (sym (trans-reflʳ _)) ⟩∎
         nil⁼ (trans eq (refl n))           ∎)
      _ _
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding nil

  -- A rearrangement lemma for substᴱ and nil.

  push-substᴱ-nil :
    {A : Type a} {@0 eq : zero ≡ n}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Vec A) eq nil ≡ nil⁼ eq
  push-substᴱ-nil {A} {eq} ax =
    substᴱ (Vec A) eq nil        ≡⟨ push-substᴱ-nil⁼ ax ⟩
    nil⁼ (trans (refl zero) eq)  ≡⟨ congᴱ nil⁼ (trans-reflˡ _) ⟩∎
    nil⁼ eq                      ∎
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cons

  -- A rearrangement lemma for substᴱ and cons⁼.

  push-substᴱ-cons⁼ :
    ∀ {A : Type a} {x xs} {@0 eq₁ : suc m ≡ n} {@0 eq₂ : n ≡ o}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Vec A) eq₂ (cons⁼ x xs eq₁) ≡ cons⁼ x xs (trans eq₁ eq₂)
  push-substᴱ-cons⁼ {o} {A} {x} ax =
    elim₁ᴱ
      (λ eq₂ →
         ∀ (@0 eq₁) xs →
         substᴱ (Vec A) eq₂ (cons⁼ x xs eq₁) ≡
         cons⁼ x xs (trans eq₁ eq₂))
      (λ eq xs →
         substᴱ (Vec A) (refl o) (cons⁼ x xs eq)  ≡⟨ substᴱ-refl {P = Vec A} ⟩
         cons⁼ x xs eq                            ≡⟨ congᴱ (cons⁼ _ _) (sym (trans-reflʳ _)) ⟩∎
         cons⁼ x xs (trans eq (refl o))           ∎)
      _ _ _
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cons

  -- Another rearrangement lemma for substᴱ and cons⁼.

  push-substᴱ-cons⁼′ :
    ∀ {A : Type a} {x xs} {@0 eq₁ : suc m ≡ n} {@0 eq₂ : n ≡ suc o}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Vec A) eq₂ (cons⁼ x xs eq₁) ≡
    cons x (substᴱ (Vec A) (cong pred (trans eq₁ eq₂)) xs)
  push-substᴱ-cons⁼′ {A} {x} {xs} {eq₁} {eq₂} ax =
    substᴱ (Vec A) eq₂ (cons⁼ x xs eq₁)                     ≡⟨ push-substᴱ-cons⁼ ax ⟩
    cons⁼ x xs (trans eq₁ eq₂)                              ≡⟨ elim¹ᴱ
                                                                 (λ eq →
                                                                    cons⁼ x xs eq ≡ cons⁼ x (substᴱ (Vec A) (cong pred eq) xs) (lemma eq))
                                                                 (sym $ cong (λ xs → cons⁼ _ xs _) $
                                                                  trans (congᴱ (λ eq → substᴱ (Vec _) eq _) (cong-refl _)) substᴱ-refl)
                                                                 _ ⟩∎
    cons x (substᴱ (Vec A) (cong pred (trans eq₁ eq₂)) xs)  ∎
    where
    open Erased.[]-cong₁ ax

    lemma : {n : ℕ} → suc m ≡ n → suc (pred n) ≡ n
    lemma {n = zero}  eq = ⊥-elim₀ (Nat.0≢+ (sym eq))
    lemma {n = suc n} _  = refl _

opaque
  unfolding cons

  -- A rearrangement lemma for substᴱ and cons.

  push-substᴱ-cons :
    ∀ {A : Type a} {x xs} {@0 eq : suc m ≡ n}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Vec A) eq (cons x xs) ≡ cons⁼ x xs eq
  push-substᴱ-cons {m} {A} {x} {xs} {eq} ax =
    substᴱ (Vec A) eq (cons x xs)         ≡⟨ push-substᴱ-cons⁼ ax ⟩
    cons⁼ x xs (trans (refl (suc m)) eq)  ≡⟨ congᴱ (cons⁼ _ _) (trans-reflˡ _) ⟩∎
    cons⁼ x xs eq                         ∎
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding cons

  -- Another rearrangement lemma for substᴱ and cons.

  push-substᴱ-cons′ :
    ∀ {A : Type a} {x xs} {@0 eq : suc m ≡ suc n}
    (ax : []-cong-axiomatisation lzero) →
    let open Erased.[]-cong₁ ax in
    substᴱ (Vec A) eq (cons x xs) ≡
    cons x (substᴱ (Vec A) (cong pred eq) xs)
  push-substᴱ-cons′ {m} {A} {x} {xs} {eq} ax =
    substᴱ (Vec A) eq (cons⁼ x xs (refl (suc m)))                     ≡⟨ push-substᴱ-cons⁼′ ax ⟩
    cons x (substᴱ (Vec A) (cong pred (trans (refl (suc m)) eq)) xs)  ≡⟨ congᴱ (λ eq → cons _ (substᴱ (Vec _) (cong pred eq) _)) (trans-reflˡ _) ⟩∎
    cons x (substᴱ (Vec A) (cong pred eq) xs)                         ∎
    where
    open Erased.[]-cong₁ ax

------------------------------------------------------------------------
-- Conversion between D.Vec and Vec

opaque

  -- The types D.Vec A n and Vec A n are equivalent (if []-cong is
  -- available).

  Vec≃Vec :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    D.Vec A n ≃ Vec A n
  Vec≃Vec {A} ax = Eq.↔→≃ to from to-from from-to
    where
    to : D.Vec A n → Vec A n
    to D.[]       = nil
    to (x D.∷ xs) = cons x (to xs)

    from : Vec A n → D.Vec A n
    from = elim ax (λ {n} _ → D.Vec A n) D.[] (λ x _ xs → x D.∷ xs)

    to-from : (xs : Vec A n) → to (from xs) ≡ xs
    to-from =
      elim ax (λ xs → to (from xs) ≡ xs)
        (to (from nil)  ≡⟨ cong to elim-nil ⟩
         to D.[]        ≡⟨⟩
         nil            ∎)
        (λ x xs hyp →
           to (from (cons x xs))  ≡⟨ cong to elim-cons ⟩
           to (x D.∷ from xs)     ≡⟨⟩
           cons x (to (from xs))  ≡⟨ cong (cons _) hyp ⟩∎
           cons x xs              ∎)

    from-to : (xs : D.Vec A n) → from (to xs) ≡ xs
    from-to D.[] =
      from (to D.[]) ≡⟨⟩
      from nil       ≡⟨ elim-nil ⟩∎
      D.[]           ∎
    from-to (x D.∷ xs) =
      from (to (x D.∷ xs))   ≡⟨⟩
      from (cons x (to xs))  ≡⟨ elim-cons ⟩
      x D.∷ from (to xs)     ≡⟨ cong (D._∷_ _) (from-to xs) ⟩∎
      x D.∷ xs               ∎

------------------------------------------------------------------------
-- Conversion between L.Vec and Vec

opaque

  -- The types L.Vec A n and Vec A n are logically equivalent.
  --
  -- Note that the number argument is not erased and that the
  -- functions are defined by recursion on the structure of the
  -- numbers.

  Vecᴸ⇔Vec : ∀ {n} → L.Vec A n ⇔ Vec A n
  Vecᴸ⇔Vec {A} = record { to = to; from = from }
    where
    to : ∀ {n} → L.Vec A n → Vec A n
    to             (L.nil⁼ eq)       = nil⁼ eq
    to {n = zero}  (L.cons⁼ _ _ eq)  = ⊥-elim₀ (Nat.0≢+ (sym eq))
    to {n = suc n} (L.cons⁼ x xs eq) =
      cons x (to {n = n} (L.cast (Nat.cancel-suc eq) xs))

    from : ∀ {n} → Vec A n → L.Vec A n
    from             (nil⁼ eq)       = L.nil⁼ eq
    from {n = zero}  (cons⁼ _ _ eq)  = ⊥-elim₀ (Nat.0≢+ (sym eq))
    from {n = suc n} (cons⁼ x xs eq) =
      L.cons x (from {n = n} (cast (Nat.cancel-suc eq) xs))

opaque
  unfolding Vecᴸ⇔Vec nil L.nil

  -- A computation rule.

  to-Vecᴸ⇔Vec-nil :
    {A : Type a} →
    _⇔_.to Vecᴸ⇔Vec L.nil ≡ nil {A = A}
  to-Vecᴸ⇔Vec-nil = refl _

opaque
  unfolding Vecᴸ⇔Vec cons L.cons

  -- A "computation" rule.

  to-Vecᴸ⇔Vec-cons :
    ∀ {A : Type a} {n} {x : A} {xs : L.Vec A n} →
    []-cong-axiomatisation lzero →
    _⇔_.to Vecᴸ⇔Vec (L.cons x xs) ≡ cons x (_⇔_.to Vecᴸ⇔Vec xs)
  to-Vecᴸ⇔Vec-cons {n} {x} {xs} ax =
    cons x (to (L.cast (cong pred (refl (suc n))) xs))  ≡⟨ cong (λ xs → cons _ (to xs)) (L.cast-cong-pred-refl ax) ⟩∎
    cons x (to xs)                                      ∎
    where
    open module E = _⇔_ (Vecᴸ⇔Vec {n = n})

opaque
  unfolding Vecᴸ⇔Vec nil L.nil

  -- A computation rule.

  from-Vecᴸ⇔Vec-nil :
    {A : Type a} →
    _⇔_.from Vecᴸ⇔Vec nil ≡ L.nil {A = A}
  from-Vecᴸ⇔Vec-nil = refl _

opaque
  unfolding Vecᴸ⇔Vec cons L.cons

  -- A "computation" rule.

  from-Vecᴸ⇔Vec-cons :
    ∀ {A : Type a} {n} {x : A} {xs : Vec A n} →
    []-cong-axiomatisation lzero →
    _⇔_.from Vecᴸ⇔Vec (cons x xs) ≡ L.cons x (_⇔_.from Vecᴸ⇔Vec xs)
  from-Vecᴸ⇔Vec-cons {n} {x} {xs} ax =
    L.cons x (from (cast (cong pred (refl (suc n))) xs))  ≡⟨ cong (λ xs → L.cons _ (from xs)) (cast-cong-pred-refl ax) ⟩∎
    L.cons x (from xs)                                    ∎
    where
    open module E = _⇔_ (Vecᴸ⇔Vec {n = n})

opaque
  unfolding Vecᴸ⇔Vec

  -- The types L.Vec A n and Vec A n are equivalent (if []-cong is
  -- available).

  Vecᴸ≃Vec :
    ∀ {A : Type a} →
    []-cong-axiomatisation lzero →
    ∀ {n} → L.Vec A n ≃ Vec A n
  Vecᴸ≃Vec {A} = λ ax → Eq.↔→≃ to from (to-from ax) (from-to ax)
    where
    open module E {n} = _⇔_ (Vecᴸ⇔Vec {n = n})

    module _ (ax : []-cong-axiomatisation lzero) where

      to-from : ∀ {n} (xs : Vec A n) → to (from xs) ≡ xs
      to-from (nil⁼ _) =
        refl _
      to-from {n = zero} (cons⁼ _ _ eq) =
        ⊥-elim₀ (Nat.0≢+ (sym eq))
      to-from {n = suc n} (cons⁼ x xs eq) =
        to (L.cons x (from (cast (cong pred eq) xs)))  ≡⟨ to-Vecᴸ⇔Vec-cons {xs = from (cast _ xs)} ax ⟩
        cons x (to (from (cast (cong pred eq) xs)))    ≡⟨ cong (cons _) (to-from {n = n} _) ⟩
        cons x (cast (cong pred eq) xs)                ≡⟨ cons-cast-cong-pred ax ⟩∎
        cons⁼ x xs eq                                  ∎

      from-to : ∀ {n} (xs : L.Vec A n) → from (to xs) ≡ xs
      from-to (L.nil⁼ _) =
        refl _
      from-to {n = zero} (L.cons⁼ _ _ eq) =
        ⊥-elim₀ (Nat.0≢+ (sym eq))
      from-to {n = suc n} (L.cons⁼ x xs eq) =
        from (cons x (to (L.cast (cong pred eq) xs)))    ≡⟨ from-Vecᴸ⇔Vec-cons {xs = to (L.cast _ xs)} ax ⟩
        L.cons x (from (to (L.cast (cong pred eq) xs)))  ≡⟨ cong (L.cons _) (from-to {n = n} _) ⟩
        L.cons x (L.cast (cong pred eq) xs)              ≡⟨ L.cons-cast-cong-pred ax ⟩∎
        L.cons⁼ x xs eq                                  ∎

opaque
  unfolding Vecᴸ≃Vec

  -- The types L.Vec A n and Vec A n are equivalent (with erased
  -- proofs).

  Vecᴸ≃ᴱVec : ∀ {n} → L.Vec A n ≃ᴱ Vec A n
  Vecᴸ≃ᴱVec =
    EEq.[≃]→≃ᴱ
      (EEq.[proofs]
         (Vecᴸ≃Vec erased-instance-of-[]-cong-axiomatisation))

------------------------------------------------------------------------
-- Eliminators with non-erased lengths

opaque
  unfolding Vecᴸ≃Vec nil L.nil L.cons

  private

    -- A lemma used below.

    elimᴸ″ :
      {A : Type a} →
      []-cong-axiomatisation lzero →
      (P : ∀ {n} → Vec A n → Type p) →
      P nil →
      (∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
      ∀ {n} (xs : L.Vec A n) → P (_⇔_.to Vecᴸ⇔Vec xs)
    elimᴸ″ {A} ax P ni co xs =
      L.elim ax (λ xs → P (to xs)) ni
        (λ x xs ih →
           subst P (sym (to-Vecᴸ⇔Vec-cons ax)) $
           co x (to xs) ih)
        xs
      where
      open module E {n} = _≃_ (Vecᴸ≃Vec {A = A} ax {n = n})

  -- An eliminator for Vec with non-erased lengths.

  elimᴸ :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    (P : ∀ {n} → Vec A n → Type p) →
    P nil →
    (∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    ∀ {n} (xs : Vec A n) → P xs
  elimᴸ {A} ax P ni co xs =
    let open _≃_ (Vecᴸ≃Vec ax) in
    subst P (right-inverse-of xs) (elimᴸ″ ax P ni co (from xs))

opaque
  unfolding elimᴸ

  -- A "computation" rule.

  elimᴸ-nil :
    {ax : []-cong-axiomatisation lzero}
    {A : Type a} {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elimᴸ ax P pⁿ pᶜ nil ≡ pⁿ
  elimᴸ-nil {ax} {P} {pⁿ} {pᶜ} =
    elimᴸ ax P pⁿ pᶜ nil  ≡⟨ cong (subst _ _) L.elim-nil ⟩
    subst P (refl _) pⁿ   ≡⟨ subst-refl _ _ ⟩∎
    pⁿ                    ∎

opaque
  unfolding
    Cons-cast-cong-pred-refl elimᴸ to-Vecᴸ⇔Vec-cons from-Vecᴸ⇔Vec-cons

  -- A "computation" rule.

  elimᴸ-cons :
    {ax : []-cong-axiomatisation lzero}
    {A : Type a} {n : ℕ} {x : A} {xs : Vec A n}
    {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elimᴸ ax P pⁿ pᶜ (cons x xs) ≡ pᶜ x xs (elimᴸ ax P pⁿ pᶜ xs)
  elimᴸ-cons {ax} {A} {n} {x} {xs} {P} {pⁿ} {pᶜ} =
    elimᴸ ax P pⁿ pᶜ (cons x xs)                                      ≡⟨⟩

    subst P (right-inverse-of (cons x xs))
      (elimᴸ″ ax P pⁿ pᶜ (from (cons x xs)))                          ≡⟨ cong (subst _ _) $
                                                                         elim₁
                                                                           (λ {ys} eq →
                                                                              elimᴸ″ ax P pⁿ pᶜ (from (cons x xs)) ≡
                                                                              subst P (cong to eq) (elimᴸ″ ax P pⁿ pᶜ ys))
                                                                           (
      elimᴸ″ ax P pⁿ pᶜ (from (cons x xs))                                  ≡⟨ sym (subst-refl _ _) ⟩

      subst P (refl _) (elimᴸ″ ax P pⁿ pᶜ (from (cons x xs)))               ≡⟨ cong (flip (subst _) _) (sym (cong-refl _)) ⟩∎

      subst P (cong to (refl (L.cons _ _)))
        (elimᴸ″ ax P pⁿ pᶜ (from (cons x xs)))                              ∎)
                                                                           (sym (from-Vecᴸ⇔Vec-cons ax)) ⟩
    subst P (right-inverse-of (cons x xs))
      (subst P (cong to (sym (from-Vecᴸ⇔Vec-cons ax)))
         (elimᴸ″ ax P pⁿ pᶜ (L.cons x (from xs))))                    ≡⟨ subst-subst _ _ _ _ ⟩

    subst P
      (trans (cong to (sym (from-Vecᴸ⇔Vec-cons ax)))
         (right-inverse-of (cons x xs)))
      (elimᴸ″ ax P pⁿ pᶜ (L.cons x (from xs)))                        ≡⟨ cong (subst _ _) L.elim-cons ⟩

    subst P
      (trans (cong to (sym (from-Vecᴸ⇔Vec-cons ax)))
         (right-inverse-of (cons x xs)))
      (subst P (sym (to-Vecᴸ⇔Vec-cons ax))
         (pᶜ x (to (from xs)) (elimᴸ″ ax P pⁿ pᶜ (from xs))))         ≡⟨ subst-subst _ _ _ _ ⟩

    subst P
      (trans (sym (to-Vecᴸ⇔Vec-cons ax))
         (trans (cong to (sym (from-Vecᴸ⇔Vec-cons ax)))
            (right-inverse-of (cons x xs))))
      (pᶜ x (to (from xs)) (elimᴸ″ ax P pⁿ pᶜ (from xs)))             ≡⟨ cong (flip (subst _) _) lemma ⟩

    subst P (cong (cons x) (right-inverse-of xs))
      (pᶜ x (to (from xs)) (elimᴸ″ ax P pⁿ pᶜ (from xs)))             ≡⟨ elim₁
                                                                           (λ {ys} eq →
                                                                              ∀ ih →
                                                                              subst P (cong (cons x) eq) (pᶜ x ys ih) ≡ pᶜ x xs (subst P eq ih))
                                                                           (λ ih →
      subst P (cong (cons x) (refl _)) (pᶜ x xs ih)                          ≡⟨ cong (λ eq → subst P eq _) (cong-refl _) ⟩
      subst P (refl _) (pᶜ x xs ih)                                          ≡⟨ subst-refl _ _ ⟩
      pᶜ x xs ih                                                             ≡⟨ cong (pᶜ _ _) (sym (subst-refl _ _)) ⟩∎
      pᶜ x xs (subst P (refl _) ih)                                          ∎)
                                                                           _ _ ⟩∎
    pᶜ x xs
      (subst P (right-inverse-of xs) (elimᴸ″ ax P pⁿ pᶜ (from xs)))   ∎
    where
    open module E {n} = _≃_ (Vecᴸ≃Vec {A = A} ax {n = n})

    lemma :
      trans (sym (to-Vecᴸ⇔Vec-cons ax))
        (trans (cong to (sym (from-Vecᴸ⇔Vec-cons ax)))
           (right-inverse-of (cons x xs))) ≡
      cong (cons x) (right-inverse-of xs)
    lemma =
      trans (sym (to-Vecᴸ⇔Vec-cons ax))
        (trans (cong to (sym (from-Vecᴸ⇔Vec-cons ax)))
           (right-inverse-of (cons x xs)))              ≡⟨⟩

      trans (sym (cong (cons x ∘ to) (L.cast-cong-pred-refl ax)))
        (trans
           (cong to $ sym $
            cong (L.cons x ∘ from) (cast-cong-pred-refl ax))
           (trans (cong (cons x ∘ to) (L.cast-cong-pred-refl ax))
              (trans
                 (cong (cons x)
                    (right-inverse-of
                       (cast (cong pred (refl (suc n))) xs)))
                 (cons-cast-cong-pred ax))))                              ≡⟨ trans
                                                                               (cong (trans _) $
                                                                                cong₂ trans
                                                                                  (trans (cong-sym _ _) $ cong sym $
                                                                                   trans (cong-∘ _ _ _) $
                                                                                   trans
                                                                                     (elim¹
                                                                                        (λ eq →
                                                                                           cong (to ∘ L.cons x ∘ from) eq ≡
                                                                                           cong
                                                                                             (cons x ∘ to ∘ L.cast (cong pred (refl (suc n))) ∘
                                                                                              from)
                                                                                             eq)
                                                                                        (trans (cong-refl _) (sym (cong-refl _)))
                                                                                        _) $
                                                                                   sym (cong-∘ _ _ _))
                                                                                  (cong (trans _) (cong (trans _) cons-cast-cong-pred-refl))) $
                                                                             trans (sym (trans-assoc _ _ _)) $
                                                                             trans (sym (trans-assoc _ _ _)) $
                                                                             trans
                                                                               (cong₂ trans
                                                                                  (trans
                                                                                     (cong (flip trans _) $
                                                                                      trans (sym (sym-trans _ _)) $
                                                                                      trans (cong sym (sym (cong-trans _ _ _))) $
                                                                                      sym (cong-sym _ _)) $
                                                                                   trans (sym (cong-trans _ _ _)) $
                                                                                   sym (cong-∘ _ _ _))
                                                                                  (sym (cong-trans _ _ _))) $
                                                                             sym (cong-trans _ _ _) ⟩
      cong (cons x)
        (trans
           (cong to $
            trans
              (sym $
               trans
                 (cong (L.cast (cong pred (refl (suc n))) ∘ from) $
                  cast-cong-pred-refl ax)
                 (L.cast-cong-pred-refl ax))
              (L.cast-cong-pred-refl ax))
           (trans
              (right-inverse-of (cast (cong pred (refl (suc n))) xs))
              (cast-cong-pred-refl ax)))                                  ≡⟨ cong (cong (cons x)) $
                                                                             elim₁
                                                                               (λ {x = ys} eq →
                                                                                  trans
                                                                                    (cong to $
                                                                                     trans
                                                                                       (sym $
                                                                                        trans (cong (L.cast (cong pred (refl (suc n))) ∘ from) eq)
                                                                                          (L.cast-cong-pred-refl ax))
                                                                                       (L.cast-cong-pred-refl ax))
                                                                                    (trans (right-inverse-of ys) eq) ≡
                                                                                  trans
                                                                                    (cong {x = from xs} to $
                                                                                     trans (sym (L.cast-cong-pred-refl ax))
                                                                                       (L.cast-cong-pred-refl ax))
                                                                                    (right-inverse-of xs))
                                                                               (cong₂ trans
                                                                                  (cong (cong _) $ cong (flip trans _) $ cong sym $
                                                                                   trans (cong (flip trans _) (cong-refl _)) $
                                                                                   trans-reflˡ _)
                                                                                  (trans-reflʳ _))
                                                                               _ ⟩
      cong (cons x)
        (trans
           (cong to $
            trans (sym (L.cast-cong-pred-refl ax))
              (L.cast-cong-pred-refl ax))
           (right-inverse-of xs))                                         ≡⟨ cong (cong _) $
                                                                             trans
                                                                                (cong (flip trans _) $
                                                                                 trans (cong (cong _) (trans-symˡ _)) $
                                                                                 cong-refl _) $
                                                                             trans-reflˡ _ ⟩∎
      cong (cons x) (right-inverse-of xs)                                 ∎

private opaque

  -- A lemma used below.

  Very-stable-≡-ℕ :
    []-cong-axiomatisation lzero →
    {m n : ℕ} → Very-stable (m ≡ n)
  Very-stable-≡-ℕ ax = Decidable-equality→Very-stable-≡ Nat._≟_ _ _
    where
    open ES.[]-cong₁ ax

opaque

  -- An eliminator for Vec with non-erased lengths.
  --
  -- This eliminator does not go via L.Vec, and it is defined by
  -- recursion on the vector, but there are no "computation rules" for
  -- this eliminator in this module.
  --
  -- The "cons case" matches on the natural number partly in an
  -- attempt to ensure that the code is strict in the number.

  elimᴸ′ :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    (P : ∀ {n} → Vec A n → Type p) →
    P nil →
    (∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    ∀ {n} (xs : Vec A n) → P xs
  elimᴸ′ {A} ax P ni co {n} xs =
    subst P substᴱ-refl $
    elim ax
      (λ {n = m} xs → ∀ n (@0 eq : m ≡ n) → P (substᴱ (Vec A) eq xs))
      (λ n eq →
         elim¹ᴱ′ (Very-stable→Very-stableᴱ 0 (Very-stable-≡-ℕ ax))
           (λ eq → P (substᴱ (Vec A) eq nil))
           (subst P (sym (substᴱ-refl {P = Vec A})) ni) eq)
      (λ where
         _ _  _  zero    eq → ⊥-elim₀ (Nat.0≢+ (sym eq))
         x xs ih (suc o) eq →
           let @0 eq = Nat.cancel-suc eq in
           subst P (sym (push-substᴱ-cons′ ax))
             (co x (substᴱ (Vec A) eq xs) (ih o eq)))
      xs n (refl _)
    where
    open Erased.[]-cong₁ ax
    open ES.[]-cong₁ ax
