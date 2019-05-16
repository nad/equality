------------------------------------------------------------------------
-- Record types with manifest fields and "with", based on Randy
-- Pollack's "Dependently Typed Records in Type Theory"
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- The module is parametrised by the type of labels, which should come
-- with decidable equality.

open import Equality

module Records-with-with
  {c⁺}
  (eq : ∀ {a p} → Equality-with-J a p c⁺)
  (open Derived-definitions-and-properties eq)
  (Label : Set)
  (_≟_ : Decidable-equality Label)
  where

open import Prelude hiding (id; proj₁; proj₂)

open import Bijection eq using (_↔_; ↑↔)
open import Function-universe eq hiding (_∘_)
open import List eq using (foldr)

------------------------------------------------------------------------
-- A Σ-type with a manifest field

-- A variant of Σ where the value of the second field is "manifest"
-- (given by the first).

infix 4 _,

record Manifest-Σ {a b} (A : Set a) {B : A → Set b}
                  (f : (x : A) → B x) : Set a where
  constructor _,
  field proj₁ : A

  proj₂ : B proj₁
  proj₂ = f proj₁

------------------------------------------------------------------------
-- Signatures and records

mutual

  infixl 5 _,_∶_ _,_≔_

  data Signature s : Set (lsuc s) where
    ∅     : Signature s
    _,_∶_ : (Sig : Signature s)
            (ℓ : Label)
            (A : Record Sig → Set s) →
            Signature s
    _,_≔_ : (Sig : Signature s)
            (ℓ : Label)
            {A : Record Sig → Set s}
            (a : (r : Record Sig) → A r) →
            Signature s

  -- Record is a record type to ensure that the signature can be
  -- inferred from a value of type Record Sig.

  record Record {s} (Sig : Signature s) : Set s where
    eta-equality
    inductive
    constructor rec
    field fun : Record-fun Sig

  Record-fun : ∀ {s} → Signature s → Set s
  Record-fun ∅             = ↑ _ ⊤
  Record-fun (Sig , ℓ ∶ A) =          Σ (Record Sig) A
  Record-fun (Sig , ℓ ≔ a) = Manifest-Σ (Record Sig) a

------------------------------------------------------------------------
-- Labels

-- A signature's labels, starting with the last one.

labels : ∀ {s} → Signature s → List Label
labels ∅             = []
labels (Sig , ℓ ∶ A) = ℓ ∷ labels Sig
labels (Sig , ℓ ≔ a) = ℓ ∷ labels Sig

-- Inhabited if the label is part of the signature.

infix 4 _∈_

_∈_ : ∀ {s} → Label → Signature s → Set
ℓ ∈ Sig =
  foldr (λ ℓ′ → if ℓ ≟ ℓ′ then (λ _ → ⊤) else id)
        ⊥
        (labels Sig)

------------------------------------------------------------------------
-- Projections

-- Signature restriction and projection. (Restriction means removal of
-- a given field and all subsequent fields.)

Restrict : ∀ {s} (Sig : Signature s) (ℓ : Label) → ℓ ∈ Sig →
           Signature s
Restrict ∅              ℓ ()
Restrict (Sig , ℓ′ ∶ A) ℓ ℓ∈ with ℓ ≟ ℓ′
... | yes _ = Sig
... | no  _ = Restrict Sig ℓ ℓ∈
Restrict (Sig , ℓ′ ≔ a) ℓ ℓ∈ with ℓ ≟ ℓ′
... | yes _ = Sig
... | no  _ = Restrict Sig ℓ ℓ∈

Restricted : ∀ {s} (Sig : Signature s) (ℓ : Label) → ℓ ∈ Sig → Set s
Restricted Sig ℓ ℓ∈ = Record (Restrict Sig ℓ ℓ∈)

Proj : ∀ {s} (Sig : Signature s) (ℓ : Label) (ℓ∈ : ℓ ∈ Sig) →
       Restricted Sig ℓ ℓ∈ → Set s
Proj ∅              ℓ ()
Proj (Sig , ℓ′ ∶ A) ℓ ℓ∈ with ℓ ≟ ℓ′
... | yes _ = A
... | no  _ = Proj Sig ℓ ℓ∈
Proj (_,_≔_ Sig ℓ′ {A = A} a) ℓ ℓ∈ with ℓ ≟ ℓ′
... | yes _ = A
... | no  _ = Proj Sig ℓ ℓ∈

-- Record restriction and projection.

infixl 5 _∣_

_∣_ : ∀ {s} {Sig : Signature s} → Record Sig →
      (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} → Restricted Sig ℓ ℓ∈
_∣_ {Sig = ∅}            r       ℓ {}
_∣_ {Sig = Sig , ℓ′ ∶ A} (rec r) ℓ {ℓ∈} with ℓ ≟ ℓ′
... | yes _ = Σ.proj₁ r
... | no  _ = _∣_ (Σ.proj₁ r) ℓ {ℓ∈}
_∣_ {Sig = Sig , ℓ′ ≔ a} (rec r) ℓ {ℓ∈} with ℓ ≟ ℓ′
... | yes _ = Manifest-Σ.proj₁ r
... | no  _ = _∣_ (Manifest-Σ.proj₁ r) ℓ {ℓ∈}

infixl 5 _·_

_·_ : ∀ {s} {Sig : Signature s} (r : Record Sig)
      (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} →
      Proj Sig ℓ ℓ∈ (r ∣ ℓ)
_·_ {Sig = ∅}            r       ℓ {}
_·_ {Sig = Sig , ℓ′ ∶ A} (rec r) ℓ {ℓ∈} with ℓ ≟ ℓ′
... | yes _ = Σ.proj₂ r
... | no  _ = _·_ (Σ.proj₁ r) ℓ {ℓ∈}
_·_ {Sig = Sig , ℓ′ ≔ a} (rec r) ℓ {ℓ∈} with ℓ ≟ ℓ′
... | yes _ = Manifest-Σ.proj₂ r
... | no  _ = _·_ (Manifest-Σ.proj₁ r) ℓ {ℓ∈}

------------------------------------------------------------------------
-- With

-- Sig With ℓ ≔ a is the signature Sig, but with the ℓ field set to a.

mutual

  infixl 5 _With_≔_

  _With_≔_ : ∀ {s} (Sig : Signature s) (ℓ : Label) {ℓ∈ : ℓ ∈ Sig} →
             ((r : Restricted Sig ℓ ℓ∈) → Proj Sig ℓ ℓ∈ r) → Signature s
  _With_≔_ ∅                ℓ {}   a
  _With_≔_ (Sig , ℓ′ ∶ A)   ℓ {ℓ∈} a with ℓ ≟ ℓ′
  ... | yes _ = Sig                   , ℓ′ ≔ a
  ... | no  _ = _With_≔_ Sig ℓ {ℓ∈} a , ℓ′ ∶ A ∘ drop-With
  _With_≔_  (Sig , ℓ′ ≔ a′) ℓ {ℓ∈} a with ℓ ≟ ℓ′
  ... | yes _ = Sig                   , ℓ′ ≔ a
  ... | no  _ = _With_≔_ Sig ℓ {ℓ∈} a , ℓ′ ≔ a′ ∘ drop-With

  drop-With : ∀ {s} {Sig : Signature s} {ℓ : Label} {ℓ∈ : ℓ ∈ Sig}
              {a : (r : Restricted Sig ℓ ℓ∈) → Proj Sig ℓ ℓ∈ r} →
              Record (_With_≔_ Sig ℓ {ℓ∈} a) → Record Sig
  drop-With {Sig = ∅} {ℓ∈ = ()}      r
  drop-With {Sig = Sig , ℓ′ ∶ A} {ℓ} (rec r) with ℓ ≟ ℓ′
  ... | yes _ = rec (Manifest-Σ.proj₁ r , Manifest-Σ.proj₂ r)
  ... | no  _ = rec (drop-With (Σ.proj₁ r) , Σ.proj₂ r)
  drop-With {Sig = Sig , ℓ′ ≔ a} {ℓ} (rec r) with ℓ ≟ ℓ′
  ... | yes _ = rec (Manifest-Σ.proj₁ r ,)
  ... | no  _ = rec (drop-With (Manifest-Σ.proj₁ r) ,)

------------------------------------------------------------------------
-- Alternative definitions of Record, along with some isomorphisms

-- An alternative definition of Record: right-nested, without the
-- record type, and without Manifest-Σ.

Recordʳ : ∀ {s} (Sig : Signature s) → (Record Sig → Set s) → Set s
Recordʳ ∅             κ = κ _
Recordʳ (Sig , ℓ ∶ A) κ = Recordʳ Sig (λ r → Σ (A r) (κ ∘ rec ∘ (r ,_)))
Recordʳ (Sig , ℓ ≔ a) κ = Recordʳ Sig (λ r → κ (rec (r ,)))

-- Manifest-Σ A f is isomorphic to A.

Manifest-Σ↔ :
  ∀ {a b} {A : Set a} {B : A → Set b} {f : (x : A) → B x} →
  Manifest-Σ A f ↔ A
Manifest-Σ↔ = record
  { surjection = record
    { logical-equivalence = record
      { to   = Manifest-Σ.proj₁
      ; from = _,
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Record is pointwise isomorphic to Record-fun.

Record↔Record-fun :
  ∀ {s} {Sig : Signature s} → Record Sig ↔ Record-fun Sig
Record↔Record-fun = record
  { surjection = record
    { logical-equivalence = record { to = Record.fun ; from = rec }
    ; right-inverse-of    = λ _ → refl _
    }
  ; left-inverse-of = λ _ → refl _
  }

-- Record and Recordʳ are, in a certain sense, isomorphic.

mutual

  Σ-Record↔Recordʳ :
    ∀ {s} (Sig : Signature s) (κ : Record Sig → Set s) →
    Σ (Record Sig) κ ↔ Recordʳ Sig κ
  Σ-Record↔Recordʳ Sig κ =
    Σ (Record Sig) κ              ↝⟨ Σ-cong Record↔Record-fun (λ _ → id) ⟩
    Σ (Record-fun Sig) (κ ∘ rec)  ↝⟨ Σ-Record-fun↔Recordʳ Sig κ ⟩□
    Recordʳ Sig κ                 □

  Σ-Record-fun↔Recordʳ :
    ∀ {s} (Sig : Signature s) (κ : Record Sig → Set s) →
    Σ (Record-fun Sig) (κ ∘ rec) ↔ Recordʳ Sig κ

  Σ-Record-fun↔Recordʳ ∅ κ =
    Σ (↑ _ ⊤) (κ ∘ rec)   ↝⟨ Σ-cong ↑↔ (λ _ → id) ⟩
    Σ ⊤ (κ ∘ rec ∘ lift)  ↝⟨ Σ-left-identity ⟩□
    κ _                   □

  Σ-Record-fun↔Recordʳ (Sig , ℓ ∶ A) κ =
    Σ (Σ (Record Sig) A) (κ ∘ rec)                     ↝⟨ inverse Σ-assoc ⟩
    Σ (Record Sig) (λ r → Σ (A r) (κ ∘ rec ∘ (r ,_)))  ↝⟨ Σ-Record↔Recordʳ Sig _ ⟩□
    Recordʳ Sig (λ r → Σ (A r) (κ ∘ rec ∘ (r ,_)))     □

  Σ-Record-fun↔Recordʳ (Sig , ℓ ≔ a) κ =
    Σ (Manifest-Σ (Record Sig) a) (κ ∘ rec)  ↝⟨ Σ-cong Manifest-Σ↔ (λ _ → id) ⟩
    Σ (Record Sig) (κ ∘ rec ∘ _,)            ↝⟨ Σ-Record↔Recordʳ Sig _ ⟩□
    Recordʳ Sig (κ ∘ rec ∘ _,)               □

-- Note that the continuation is initialised with a (lifted) unit
-- type.

Record↔Recordʳ :
  ∀ {s} (Sig : Signature s) →
  Record Sig ↔ Recordʳ Sig (λ _ → ↑ s ⊤)
Record↔Recordʳ Sig =
  Record Sig                 ↝⟨ inverse ×-right-identity ⟩
  Record Sig × ⊤             ↝⟨ id ×-cong inverse ↑↔ ⟩
  Record Sig × ↑ _ ⊤         ↝⟨ Σ-Record↔Recordʳ Sig _ ⟩□
  Recordʳ Sig (λ _ → ↑ _ ⊤)  □

-- Another alternative definition of Record: basically the same as
-- Recordʳ, but the continuation is initialised with the first
-- non-manifest field, if any, to avoid a pointless innermost unit
-- type.

Recʳ : ∀ {s} → Signature s → Set s
Recʳ ∅             = ↑ _ ⊤
Recʳ (Sig , ℓ ∶ A) = Recordʳ Sig A
Recʳ (Sig , ℓ ≔ a) = Recʳ Sig

-- Record and Recʳ are pointwise isomorphic.

mutual

  Record↔Recʳ :
    ∀ {s} {Sig : Signature s} →
    Record Sig ↔ Recʳ Sig
  Record↔Recʳ {Sig = Sig} =
    Record Sig      ↝⟨ Record↔Record-fun ⟩
    Record-fun Sig  ↝⟨ Record-fun↔Recʳ Sig ⟩□
    Recʳ Sig        □

  Record-fun↔Recʳ :
    ∀ {s} (Sig : Signature s) →
    Record-fun Sig ↔ Recʳ Sig

  Record-fun↔Recʳ ∅ = ↑ _ ⊤ □

  Record-fun↔Recʳ (Sig , ℓ ∶ A) =
    Σ (Record Sig) A  ↝⟨ Σ-Record↔Recordʳ Sig A ⟩□
    Recordʳ Sig A     □

  Record-fun↔Recʳ (Sig , ℓ ≔ a) =
    Manifest-Σ (Record Sig) a  ↝⟨ Manifest-Σ↔ ⟩
    Record Sig                 ↝⟨ Record↔Recʳ ⟩□
    Recʳ Sig                   □
