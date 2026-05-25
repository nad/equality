------------------------------------------------------------------------
-- A forded variant of the vectors in Vec.Data with non-erased lengths
-- but erased equality proofs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Data.Forded.Non-erased-lengths
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq hiding (elim)

open import Prelude hiding (Fin)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased hiding (map)
open import Erased.Stability eq as ES
open import Fin.Data.Forded eq as F hiding (cast; elim)
open import Function-universe eq
open import Nat eq as Nat using (pred)

private variable
  a b p  : Level
  @0 A B : Type _
  x      : A
  m n    : ℕ

------------------------------------------------------------------------
-- The type

-- Vectors.
--
-- Note that, because the parameter n is not erased, the natural
-- number argument of cons⁼ cannot be erased.

data Vec (A : Type a) (n : ℕ) : Type a where
  nil⁼  : (@0 eq : zero ≡ n) → Vec A n
  cons⁼ : A → Vec A m → (@0 eq : suc m ≡ n) → Vec A n

private variable
  xs ys : Vec _ _

-- An eliminator for Vec.

elim⁼ :
  (@0 P : ∀ {n} → Vec A n → Type p) →
  (∀ {n} (@0 eq : zero ≡ n) → P (nil⁼ eq)) →
  (∀ {m n} (x : A) (xs : Vec A m) (@0 eq : suc m ≡ n) → P xs →
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

  -- A lemma used below.

  Very-stable-≡-ℕ :
    []-cong-axiomatisation lzero →
    Very-stable (m ≡ n)
  Very-stable-≡-ℕ ax = Decidable-equality→Very-stable-≡ Nat._≟_ _ _
    where
    open ES.[]-cong₁ ax

opaque
  unfolding Very-stable-≡-ℕ nil cons

  -- Another eliminator for Vec.

  elim :
    []-cong-axiomatisation lzero →
    (P : ∀ {n} → Vec A n → Type p) →
    P nil →
    (∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    (xs : Vec A n) → P xs
  elim ax P ni co =
    elim⁼ P (λ {n} eq → elim¹ᴱ′ s (λ eq → P (nil⁼ eq)) ni eq)
      (λ x xs eq p →
         elim¹ᴱ′ s (λ eq → P (cons⁼ x xs eq)) (co x xs p) eq)
    where
    open ES.[]-cong₁ ax

    s : Very-stableᴱ (m ≡ n)
    s = Very-stable→Very-stableᴱ 0 (Very-stable-≡-ℕ ax)

opaque
  unfolding elim nil

  -- A "computation" rule.

  elim-nil :
    {ax : []-cong-axiomatisation lzero}
    {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elim ax P pⁿ pᶜ nil ≡ pⁿ
  elim-nil {ax} {P} {pⁿ} {pᶜ} =
    elim ax P pⁿ pᶜ nil                                        ≡⟨⟩

    elim¹ᴱ′ (Very-stable→Very-stableᴱ 0 (Very-stable-≡-ℕ ax))
      (λ eq → P (nil⁼ eq)) pⁿ (refl zero)                      ≡⟨ elim¹ᴱ′-refl (Very-stable-≡-ℕ ax) (λ eq → P (nil⁼ eq)) ⟩∎

    pⁿ                                                         ∎
    where
    open ES.[]-cong₁ ax

opaque
  unfolding elim cons

  -- A "computation" rule.

  elim-cons :
    {ax : []-cong-axiomatisation lzero}
    {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {x : A} {xs : Vec A n}
    {pᶜ : ∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elim ax P pⁿ pᶜ (cons x xs) ≡ pᶜ x xs (elim ax P pⁿ pᶜ xs)
  elim-cons {n} {ax} {P} {pⁿ} {x} {xs} {pᶜ} =
    elim ax P pⁿ pᶜ (cons x xs)                                  ≡⟨⟩

    elim¹ᴱ′ (Very-stable→Very-stableᴱ 0 (Very-stable-≡-ℕ ax))
      (λ eq → P (cons⁼ x xs eq)) (pᶜ x xs (elim ax P pⁿ pᶜ xs))
      (refl (suc n))                                             ≡⟨ elim¹ᴱ′-refl (Very-stable-≡-ℕ ax) (λ eq → P (cons⁼ x xs eq)) ⟩∎

    pᶜ x xs (elim ax P pⁿ pᶜ xs)                                 ∎
    where
    open ES.[]-cong₁ ax

-- A non-dependent eliminator for Vec.

rec : B → (∀ {n} → A → Vec A n → B → B) → Vec A n → B
rec {B} n c = elim⁼ (λ _ → B) (λ _ → n) (λ x xs _ → c x xs)

opaque
  unfolding nil

  -- A computation rule.

  _ :
    {B : Type b} {bⁿ : B}
    {bᶜ : ∀ {n} → A → Vec A n → B → B} →
    rec bⁿ bᶜ nil ≡ bⁿ
  _ = refl _

opaque
  unfolding cons

  -- A computation rule.

  _ :
    {B : Type b} {bⁿ : B} {xs : Vec A n}
    {bᶜ : ∀ {n} → A → Vec A n → B → B} →
    rec bⁿ bᶜ (cons x xs) ≡ bᶜ x xs (rec bⁿ bᶜ xs)
  _ = refl _

opaque
  unfolding nil cons

  -- A third eliminator for Vec, defined under the assumption that
  -- unlimited erased matches are allowed for identity types.

  elimᵁ :
    Unlimited-erased-matches lzero p →
    (@0 P : ∀ {n} → Vec A n → Type p) →
    P nil →
    (∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    (xs : Vec A n) → P xs
  elimᵁ (Jᴱ , _) P n c =
    elim⁼ P (λ eq → Jᴱ (λ eq → P (nil⁼ eq)) n eq)
      (λ x xs eq p → Jᴱ (λ eq → P (cons⁼ x xs eq)) (c x xs p) eq)

opaque
  unfolding elimᵁ nil

  -- A "computation" rule.

  elimᵁ-nil :
    {ax : Unlimited-erased-matches lzero p}
    {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elimᵁ ax P pⁿ pᶜ nil ≡ pⁿ
  elimᵁ-nil {ax = ax@(Jᴱ , Jᴱ-refl)} {P} {pⁿ} {pᶜ} =
    elimᵁ ax P pⁿ (λ {n = n} → pᶜ {n = n}) nil  ≡⟨⟩
    Jᴱ (λ eq → P (nil⁼ eq)) pⁿ (refl zero)      ≡⟨ Jᴱ-refl (λ eq → P (nil⁼ eq)) ⟩∎
    pⁿ                                          ∎

opaque
  unfolding elimᵁ cons

  -- A "computation" rule.

  elimᵁ-cons :
    {ax : Unlimited-erased-matches lzero p}
    {P : ∀ {n} → Vec A n → Type p} {pⁿ : P nil}
    {x : A} {xs : Vec A n}
    {pᶜ : ∀ {n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
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
    Erased.[]-cong₁.congᴱ ax nil⁼ (trans-reflʳ eq)
  cast-refl {xs = cons⁼ _ _ eq} ax =
    Erased.[]-cong₁.congᴱ ax (cons⁼ _ _) (trans-reflʳ eq)

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
    cons x (cast (cong pred eq) xs)                     ≡⟨ elim¹ᴱ′ (Very-stable→Very-stableᴱ 0 (Very-stable-≡-ℕ ax))
                                                             (λ eq → cons x (cast (cong pred eq) xs) ≡ cons⁼ x xs (cong suc (cong pred eq)))
                                                             (
      cons x (cast (cong pred (refl (suc m))) xs)             ≡⟨ cong (λ xs → cons _ xs) (cast-cong-pred-refl ax) ⟩
      cons x xs                                               ≡⟨ congᴱ (cons⁼ _ _) (sym (trans (cong (cong _) (cong-refl _)) (cong-refl _))) ⟩∎
      cons⁼ x xs (cong suc (cong pred (refl (suc m))))        ∎)
                                                             eq ⟩
    cons⁼ x xs (cong suc (cong pred eq))                ≡⟨ congᴱ (cons⁼ _ _) (_↔_.left-inverse-of suc≡suc↔ _) ⟩∎
    cons⁼ x xs eq                                       ∎
    where
    open Erased.[]-cong₁ ax
    open ES.[]-cong₁ ax

------------------------------------------------------------------------
-- Some simple functions

opaque

  -- Finds the element at the given position.

  index : Vec A n → Fin n → A
  index (nil⁼ p)      (zero q)   = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  index (nil⁼ p)      (suc _ q)  = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  index (cons⁼ x _ _) (zero _)   = x
  index (cons⁼ _ xs p) (suc i q) =
    index xs (F.cast (Nat.cancel-suc (trans q (sym p))) i)

opaque

  -- Updates the element at the given position.

  infix 3 _[_≔_]

  _[_≔_] : Vec A n → Fin n → A → Vec A n
  nil⁼ p       [ zero q  ≔ _ ] = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  nil⁼ p       [ suc _ q ≔ _ ] = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  cons⁼ _ xs p [ zero _  ≔ y ] = cons⁼ y xs p
  cons⁼ x xs p [ suc i q ≔ y ] =
    cons⁼ x (xs [ F.cast (Nat.cancel-suc (trans q (sym p))) i ≔ y ]) p

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
