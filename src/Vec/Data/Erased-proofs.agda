------------------------------------------------------------------------
-- Vectors defined as lists plus erased proofs showing that the lists
-- have correct lengths
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Vec.Data.Erased-proofs
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq hiding (elim)

open import Prelude hiding (Fin)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased hiding (map)
open import Fin.Data.Forded eq hiding (cast; elim)
open import Function-universe eq
import List eq as L
open import Nat eq as Nat using (pred)
import Vec.Data eq as D
import Vec.Data.Forded eq as F

private variable
  a b p  : Level
  @0 A B : Type _
  x      : A
  @0 m n : ℕ

------------------------------------------------------------------------
-- The type

opaque

  -- Vectors.

  Vec : Type a → @0 ℕ → Type a
  Vec A n = ∃ λ (xs : List A) → Erased (L.length xs ≡ n)

private variable
  xs ys : Vec _ _

opaque
  unfolding Vec

  -- Nil.

  nil : Vec A zero
  nil = [] , [ refl _ ]

opaque
  unfolding Vec

  -- Cons.

  cons : A → Vec A n → Vec A (suc n)
  cons x (xs , [ eq ]) = x ∷ xs , [ cong suc eq ]

opaque
  unfolding Vec nil cons

  -- An eliminator for Vec.
  --
  -- The eliminator is implemented using []-cong.

  elim :
    []-cong-axiomatisation lzero →
    (P : ∀ {@0 n} → Vec A n → Type p) →
    P nil →
    (∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)) →
    (xs : Vec A n) → P xs
  elim {A} ax P n c (xs , [ eq ]) =
    L.List-elim
      (λ xs → ∀ {@0 n} (@0 eq : L.length xs ≡ n) → P (xs , [ eq ]))
      (elim¹ᴱ (λ eq → P ([] , [ eq ])) n)
      (λ x xs ih →
         elim¹ᴱ (λ eq → P (x ∷ xs , [ eq ]))
           (substᴱ (λ eq → P (x ∷ xs , [ eq ])) (cong-refl _)
              (c x (xs , [ refl _ ]) (ih (refl _)))))
      xs eq
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding elim

  -- A "computation" rule.

  elim-nil :
    {ax : []-cong-axiomatisation lzero}
    {P : ∀ {@0 n} → Vec A n → Type p} {pⁿ : P nil}
    {pᶜ : ∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)} →
    elim ax P pⁿ pᶜ nil ≡ pⁿ
  elim-nil {ax} {P} {pⁿ} {pᶜ} =
    elim¹ᴱ (λ eq → P ([] , [ eq ])) pⁿ (refl _)  ≡⟨ elim¹ᴱ-refl (λ eq → P (_ , [ eq ])) ⟩
    pⁿ                                           ∎
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding elim

  -- A "computation" rule.

  elim-cons :
    {ax : []-cong-axiomatisation lzero}
    {P : ∀ {@0 n} → Vec A n → Type p} {pⁿ : P nil} {x : A}
    {pᶜ : ∀ {@0 n} (x : A) (xs : Vec A n) → P xs → P (cons x xs)}
    {xs : Vec A n} →
    elim ax P pⁿ pᶜ (cons x xs) ≡ pᶜ x xs (elim ax P pⁿ pᶜ xs)
  elim-cons {ax} {P} {pⁿ} {x} {pᶜ} {xs = xs , [ eq ]} =
    elim¹ᴱ
      (λ eq →
         elim¹ᴱ (λ eq → P (x ∷ xs , [ eq ]))
           (substᴱ (λ eq → P (x ∷ xs , [ eq ])) (cong-refl suc)
              (pᶜ x (xs , [ refl (L.length xs) ])
                 (elim ax P pⁿ pᶜ (xs , [ refl (L.length xs) ]))))
           (cong suc eq) ≡
         pᶜ x (xs , [ eq ]) (elim ax P pⁿ pᶜ (xs , [ eq ])))
      (elim₁ᴱ
         (λ {x = eq} eq′ →
            (p : P (x ∷ xs , [ eq ])) →
            elim¹ᴱ (λ eq → P (x ∷ xs , [ eq ]))
              (substᴱ (λ eq → P (x ∷ xs , [ eq ])) eq′ p) eq ≡
            p)
         (λ p →
            elim¹ᴱ (λ eq → P (x ∷ xs , [ eq ]))
              (substᴱ (λ eq → P (x ∷ xs , [ eq ]))
                 (refl (refl (L.length (x ∷ xs)))) p)
              (refl (L.length (x ∷ xs)))               ≡⟨ elim¹ᴱ-refl (λ eq → P (_ , [ eq ])) ⟩

            substᴱ (λ eq → P (x ∷ xs , [ eq ]))
              (refl (refl (L.length (x ∷ xs)))) p      ≡⟨ substᴱ-refl {P = λ eq → P (_ , [ eq ])} ⟩∎

            p                                          ∎)
         (cong-refl suc)
         (pᶜ x (xs , [ refl (L.length xs) ])
            (elim ax P pⁿ pᶜ (xs , [ refl (L.length xs) ]))))
      eq
    where
    open Erased.[]-cong₁ ax

opaque
  unfolding Vec

  -- A non-dependent eliminator for Vec.

  rec : B → (∀ {@0 n} → A → Vec A n → B → B) → Vec A n → B
  rec {B} n c (xs , [ eq ]) =
    L.List-elim (λ xs → ∀ {@0 n} → @0 L.length xs ≡ n → B) (λ _ → n)
      (λ x xs ih eq →
         let @0 eq = cong pred eq in
         c x (xs , [ eq ]) (ih eq))
      xs eq

opaque
  unfolding rec nil

  -- A computation rule.

  _ :
    {B : Type b} {bⁿ : B}
    {bᶜ : ∀ {@0 n} → A → Vec A n → B → B} →
    rec bⁿ bᶜ nil ≡ bⁿ
  _ = refl _

opaque
  unfolding rec cons

  -- A "computation" rule.

  rec-cons :
    {B : Type b} {bⁿ : B} {bᶜ : ∀ {@0 n} → A → Vec A n → B → B}
    {xs : Vec A n} →
    []-cong-axiomatisation lzero →
    rec bⁿ bᶜ (cons x xs) ≡ bᶜ x xs (rec bⁿ bᶜ xs)
  rec-cons {x} {B} {bⁿ} {bᶜ} {xs = xs , [ eq ]} ax =
    bᶜ x (xs , [ cong pred (cong suc eq) ])
      (L.List-elim (λ xs → ∀ {@0 n} → @0 L.length xs ≡ n → B) (λ _ → bⁿ)
         (λ x xs ih eq →
            bᶜ x (xs , [ cong pred eq ]) (ih (cong pred eq)))
         xs (cong pred (cong suc eq)))                                    ≡⟨ congᴱ
                                                                               (λ eq →
                                                                                  bᶜ x (xs , [ eq ])
                                                                                    (L.List-elim (λ xs → ∀ {@0 n} → @0 L.length xs ≡ n → B)
                                                                                       (λ _ → bⁿ)
                                                                                       (λ x xs ih eq →
                                                                                          bᶜ x (xs , [ cong pred eq ]) (ih (cong pred eq)))
                                                                                       xs eq))
                                                                               (_↔_.right-inverse-of suc≡suc↔ _) ⟩∎
    bᶜ x (xs , [ eq ])
      (L.List-elim (λ xs → ∀ {@0 n} → @0 L.length xs ≡ n → B) (λ _ → bⁿ)
         (λ x xs ih eq →
            bᶜ x (xs , [ cong pred eq ]) (ih (cong pred eq)))
         xs eq)                                                           ∎
    where
    open Erased.[]-cong₁ ax

------------------------------------------------------------------------
-- Conversion functions

opaque

  -- The types F.Vec A n and Vec A n are equivalent (if []-cong is
  -- available).

  F-Vec≃Vec :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    F.Vec A n ≃ Vec A n
  F-Vec≃Vec {A} ax = Eq.↔→≃ to from to-from from-to
    where
    to : F.Vec A n → Vec A n
    to = F.elim ax (λ {n} _ → Vec A n) nil (λ x _ xs → cons x xs)

    from : Vec A n → F.Vec A n
    from =
      elim ax (λ {n} _ → F.Vec A n) F.nil (λ x _ xs → F.cons x xs)

    to-from : (xs : Vec A n) → to (from xs) ≡ xs
    to-from =
      elim ax (λ xs → to (from xs) ≡ xs)
        (to (from nil)  ≡⟨ cong to elim-nil ⟩
         to F.nil       ≡⟨ F.elim-nil ⟩∎
         nil            ∎)
        (λ x xs hyp →
           to (from (cons x xs))    ≡⟨ cong to elim-cons ⟩
           to (F.cons x (from xs))  ≡⟨ F.elim-cons ⟩
           cons x (to (from xs))    ≡⟨ cong (cons _) hyp ⟩∎
           cons x xs                ∎)

    from-to : (xs : F.Vec A n) → from (to xs) ≡ xs
    from-to =
      F.elim ax (λ xs → from (to xs) ≡ xs)
        (from (to F.nil)  ≡⟨ cong from F.elim-nil ⟩
         from nil         ≡⟨ elim-nil ⟩∎
         F.nil            ∎)
        (λ x xs hyp →
           from (to (F.cons x xs))  ≡⟨ cong from F.elim-cons ⟩
           from (cons x (to xs))    ≡⟨ elim-cons ⟩
           F.cons x (from (to xs))  ≡⟨ cong (F.cons _) hyp ⟩∎
           F.cons x xs              ∎)

opaque

  -- The types D.Vec A n and Vec A n are equivalent (if []-cong is
  -- available).

  D-Vec≃Vec :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    D.Vec A n ≃ Vec A n
  D-Vec≃Vec {n} {A} ax =
    D.Vec A n  ↝⟨ F.Vec≃Vec ax ⟩
    F.Vec A n  ↝⟨ F-Vec≃Vec ax ⟩□
    Vec A n    □

------------------------------------------------------------------------
-- Some simple functions

opaque
  unfolding Vec

  -- A cast function for vectors.

  cast : @0 m ≡ n → Vec A m → Vec A n
  cast eq₁ (xs , [ eq₂ ]) = xs , [ trans eq₂ eq₁ ]

opaque
  unfolding Vec

  -- The length of a vector.

  length : Vec A n → ℕ
  length (xs , _) = L.length xs

opaque
  unfolding Vec

  -- Finds the element at the given position.

  index : Vec A n → Fin n → A
  index ([] , [ p ])     (zero q)  = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  index ([] , [ p ])     (suc _ q) = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  index (x ∷ _ , _)      (zero _)  = x
  index (_ ∷ xs , [ p ]) (suc i q) =
    index (xs , [ Nat.cancel-suc (trans p (sym q)) ]) i

opaque
  unfolding Vec

  -- Updates the element at the given position.

  infix 3 _[_≔_]

  _[_≔_] : Vec A n → Fin n → A → Vec A n
  []     , [ p ] [ zero q  ≔ _ ] = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  []     , [ p ] [ suc _ q ≔ _ ] = ⊥-elim₀ (Nat.0≢+ (trans p (sym q)))
  _ ∷ xs , p     [ zero _  ≔ y ] = y ∷ xs , p
  x ∷ xs , [ p ] [ suc i q ≔ y ] =
    cast q
      (cons x ((xs , [ Nat.cancel-suc (trans p (sym q)) ]) [ i ≔ y ]))

opaque
  unfolding Vec

  -- Applies the function to every element in the vector.

  map : (A → B) → Vec A n → Vec B n
  map f (xs , [ eq ])  = L.map f xs , [ trans (L.length∘map _ xs) eq ]

opaque
  unfolding Vec

  -- Constructs a vector containing a certain number of copies of the
  -- given element.

  replicate : ∀ {n} → A → Vec A n
  replicate {n} x = L.replicate n x , [ L.length-replicate n ]

opaque
  unfolding Vec

  -- The head of the vector.

  head : Vec A (suc n) → A
  head ([]    , [ eq ]) = ⊥-elim₀ (Nat.0≢+ eq)
  head (x ∷ _ , _)      = x

opaque
  unfolding Vec

  -- The tail of the vector.

  tail : Vec A (suc n) → Vec A n
  tail ([]     , [ eq ]) = ⊥-elim₀ (Nat.0≢+ eq)
  tail (_ ∷ xs , [ eq ]) = xs , [ Nat.cancel-suc eq ]

opaque
  unfolding Vec cons head tail

  -- Vec A (suc n) is equivalent to A × Vec A n (in the presence of
  -- []-cong).

  Vec-suc≃ :
    {A : Type a} →
    []-cong-axiomatisation lzero →
    Vec A (suc n) ≃ (A × Vec A n)
  Vec-suc≃ {n} {A} ax = Eq.↔→≃
    (λ xs → head xs , tail xs)
    (uncurry cons)
    (λ where
       (x , xs , [ eq ]) →
         x , xs , [ cong pred (cong suc eq) ]  ≡⟨ congᴱ (λ eq → _ , xs , [ eq ]) (_↔_.right-inverse-of suc≡suc↔ _) ⟩∎
         x , xs , [ eq ]                       ∎)
    (λ where
       ([] , [ eq ])     → ⊥-elim₀ (Nat.0≢+ eq)
       (x ∷ xs , [ eq ]) →
         x ∷ xs , [ cong suc (cong pred eq) ]  ≡⟨ congᴱ (λ eq → _ , [ eq ]) (_↔_.left-inverse-of suc≡suc↔ _) ⟩∎
         x ∷ xs , [ eq ]                       ∎)
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

private

  opaque
    unfolding cast length

    -- A lemma used below.

    length-cast :
      {@0 eq : m ≡ n} →
      length (cast eq xs) ≡ length xs
    length-cast {xs = _ , [ _ ]} = refl _

  opaque
    unfolding length replicate

    -- A lemma used below.

    length-replicate :
      {n : ℕ} → length (replicate {n = n} x) ≡ n
    length-replicate = L.length-replicate _

opaque
  unfolding elim length

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
  elim→[]-cong-ℕ {n} elim {m} eq =
    [ m ]                                ≡⟨ cong [_]→ (sym length-replicate) ⟩
    [ length (replicate {n = m} tt) ]    ≡⟨ cong [_]→ (sym length-cast) ⟩
    [ length (cast eq (replicate tt)) ]  ≡⟨ elim (λ {n} (xs , _) → [ L.length xs ] ≡ [ n ])
                                              (refl [ zero ])
                                              (λ { _ (_ , [ _ ]) → cong (Erased.map suc) })
                                              (cast eq (replicate tt)) ⟩∎
    [ n ]                                ∎
