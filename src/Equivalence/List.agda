------------------------------------------------------------------------
-- Lists of equivalent types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.List
  {c⁺} (eq-J : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence eq-J as Eq using (_≃_)
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import List eq-J using (_++_)
open import Surjection eq-J using (_↠_)

private
  variable
    a b l      : Level
    ls ls₁ ls₂ : List Level
    A B        : Type a
    P          : ∀ {a} → Type a → Type a

------------------------------------------------------------------------
-- Functions used to compute levels

Type-list-level : List Level → Level
Type-list-level []       = lzero
Type-list-level (a ∷ ls) = lsuc a ⊔ Type-list-level ls

Last-level : Level → List Level → Level
Last-level a []       = a
Last-level a (b ∷ ls) = Last-level b ls

∈-level : Level → List Level → Level
∈-level _ []       = lzero
∈-level a (b ∷ ls) = a ⊔ b ⊔ ∈-level a ls

All-level : List Level → Level
All-level []       = lzero
All-level (l ∷ ls) = l ⊔ All-level ls

Implies-level : List Level → Level
Implies-level []               = lzero
Implies-level (_ ∷ [])         = lzero
Implies-level (a ∷ ls@(b ∷ _)) = (a ⊔ b) ⊔ Implies-level ls

Last-implies-first-level : List Level → Level
Last-implies-first-level []           = lzero
Last-implies-first-level (_ ∷ [])     = lzero
Last-implies-first-level (a ∷ b ∷ ls) = a ⊔ Last-level b ls

Logically-equivalent-level : List Level → Level
Logically-equivalent-level ls =
  Implies-level ls ⊔ Last-implies-first-level ls

Equivalent-level : List Level → Level
Equivalent-level ls =
  Logically-equivalent-level ls ⊔ All-level ls

------------------------------------------------------------------------
-- Lists of types and some related definitions

-- Lists of types.

Type-list : (ls : List Level) → Type (Type-list-level ls)
Type-list []               = ⊤
Type-list (l ∷ [])         = Type l
Type-list (l ∷ ls@(_ ∷ _)) = Type l × Type-list ls

-- Prepends a type to a list of types.

Cons : Type a → Type-list ls → Type-list (a ∷ ls)
Cons {ls = []}    A _  = A
Cons {ls = _ ∷ _} A As = A , As

-- The head of a non-empty list of types.

Head : Type-list (a ∷ ls) → Type a
Head {ls = []}    A       = A
Head {ls = _ ∷ _} (A , _) = A

-- The tail of a non-empty list of types.

Tail : Type-list (a ∷ ls) → Type-list ls
Tail {ls = []}    _        = _
Tail {ls = _ ∷ _} (_ , As) = As

-- The last element of a non-empty list of types.

Last : Type-list (a ∷ ls) → Type (Last-level a ls)
Last {ls = []}    A        = A
Last {ls = _ ∷ _} (_ , As) = Last As

-- Appends two lists.

Append : Type-list ls₁ → Type-list ls₂ → Type-list (ls₁ ++ ls₂)
Append {ls₁ = []}    _  Bs = Bs
Append {ls₁ = _ ∷ _} As Bs = Cons (Head As) (Append (Tail As) Bs)

-- The head of Cons A As is equivalent to A.

Head-Cons :
  ∀ {A : Type a} ls {As : Type-list ls} →
  Head (Cons A As) ≃ A
Head-Cons []      = F.id
Head-Cons (_ ∷ _) = F.id

-- If As is non-empty and Bs is empty, then the last element of
-- Append As Bs is the last element of As.

Last-Append-[] :
  (ls : List Level) {As : Type-list (a ∷ ls)} {Bs : Type-list []} →
  Last (Append As Bs) ≃ Last As
Last-Append-[] []       = F.id
Last-Append-[] (_ ∷ ls) = Last-Append-[] ls

-- If As and Bs are both non-empty, then the last element of
-- Append As Bs is the last element of Bs.

Last-Append-∷ :
  (ls₁ : List Level)
  {As : Type-list (a ∷ ls₁)} {Bs : Type-list (b ∷ ls₂)} →
  Last (Append As Bs) ≃ Last Bs
Last-Append-∷ []       = F.id
Last-Append-∷ (_ ∷ ls) = Last-Append-∷ ls

-- A ∈ As means that A is a member of As.

infix 4 _∈_

_∈_ : Type a → Type-list ls → Type (∈-level a ls)
_∈_ {ls = []}        _ _        = ⊥
_∈_ {ls = _ ∷ []}    A B        = A ≃ B
_∈_ {ls = _ ∷ _ ∷ _} A (B , As) = A ≃ B ⊎ A ∈ As

-- The head of a list of types is a member of the list.

Head∈ :
  {As : Type-list (a ∷ ls)} →
  Head As ∈ As
Head∈ {ls = []}    = F.id
Head∈ {ls = _ ∷ _} = inj₁ F.id

-- An ordering relation for membership proofs.

infix 4 _≤_

_≤_ :
  {As : Type-list ls} →
  A ∈ As → B ∈ As → Type
_≤_ {ls = _ ∷ []}    _         _         = ⊤
_≤_ {ls = _ ∷ _ ∷ _} (inj₁ _)  _         = ⊤
_≤_ {ls = _ ∷ _ ∷ _} (inj₂ _)  (inj₁ _)  = ⊥
_≤_ {ls = _ ∷ _ ∷ _} (inj₂ A∈) (inj₂ B∈) = A∈ ≤ B∈

-- Head∈ {As = As} is smaller than any other membership proof for As.

Head∈≤ :
  (As : Type-list (a ∷ ls)) {B : Type b} {p : B ∈ As} →
  Head∈ {As = As} ≤ p
Head∈≤ {ls = []}    _ = _
Head∈≤ {ls = _ ∷ _} _ = _

-- The ordering relation is total.

≤-total :
  {@0 A : Type a} {@0 B : Type b} {@0 As : Type-list ls} →
  (A∈As : A ∈ As) (B∈As : B ∈ As) → A∈As ≤ B∈As ⊎ B∈As ≤ A∈As
≤-total {ls = _ ∷ []}    _           _           = inj₁ _
≤-total {ls = _ ∷ _ ∷ _} (inj₁ _)    _           = inj₁ _
≤-total {ls = _ ∷ _ ∷ _} (inj₂ _)    (inj₁ _)    = inj₂ _
≤-total {ls = _ ∷ _ ∷ _} (inj₂ A∈As) (inj₂ B∈As) = ≤-total A∈As B∈As

-- All P As means that P A holds for every type A in As.

All :
  (P : ∀ {a} → Type a → Type a) →
  Type-list ls → Type (All-level ls)
All {ls = []}        _ _        = ⊤
All {ls = _ ∷ []}    P A        = P A
All {ls = _ ∷ _ ∷ _} P (A , As) = P A × All P As

-- If P respects equivalences, All P As holds, and A is a member of
-- As, then P A holds.

All-∈ :
  {As : Type-list ls} →
  (∀ {a b} {A : Type a} {B : Type b} → A ≃ B → P A → P B) →
  All P As → A ∈ As → P A
All-∈ {ls = _ ∷ []}    resp p         A≃        = resp (inverse A≃) p
All-∈ {ls = _ ∷ _ ∷ _} resp (p , _)   (inj₁ A≃) = resp (inverse A≃) p
All-∈ {ls = _ ∷ _ ∷ _} resp (_ , all) (inj₂ A∈) = All-∈ resp all A∈

------------------------------------------------------------------------
-- Lists containing (logically) equivalent types

-- Implies As means that every type in the list As implies the next
-- type in the list, if any.

Implies : Type-list ls → Type (Implies-level ls)
Implies {ls = []}            _                = ⊤
Implies {ls = _ ∷ []}        A                = ⊤
Implies {ls = _ ∷ _ ∷ []}    (A , B)          = A → B
Implies {ls = _ ∷ _ ∷ _ ∷ _} (A , As@(B , _)) = (A → B) × Implies As

-- A cons operation for Implies.

Implies-Cons :
  {A : Type a} {As : Type-list (b ∷ ls)} →
  (A → Head As) → Implies As → Implies (Cons A As)
Implies-Cons {ls = []}    f _       = f
Implies-Cons {ls = _ ∷ _} f implies = f , implies

-- A tail operation for Implies.

Implies-Tail :
  {As : Type-list (a ∷ ls)} →
  Implies As → Implies (Tail As)
Implies-Tail {ls = []}        implies       = _
Implies-Tail {ls = _ ∷ []}    implies       = _
Implies-Tail {ls = _ ∷ _ ∷ _} (_ , implies) = implies

-- A head operation for Implies.

Implies-Head :
  {As : Type-list (a ∷ b ∷ ls)} →
  Implies As → Head As → Head (Tail As)
Implies-Head {ls = []}    f       = f
Implies-Head {ls = _ ∷ _} (f , _) = f

-- Last-implies-first As holds if As contains at most one element, or
-- otherwise if the last type in As implies the first one.

Last-implies-first :
  Type-list ls → Type (Last-implies-first-level ls)
Last-implies-first {ls = []}        _        = ⊤
Last-implies-first {ls = _ ∷ []}    _        = ⊤
Last-implies-first {ls = _ ∷ _ ∷ _} (A , As) = Last As → A

-- Logically-equivalent As means that all types in As are logically
-- equivalent.

Logically-equivalent :
  Type-list ls → Type (Logically-equivalent-level ls)
Logically-equivalent As = Implies As × Last-implies-first As

-- Equivalent As means that all types in As are equivalent
-- propositions.

Equivalent : Type-list ls → Type (Equivalent-level ls)
Equivalent As = Logically-equivalent As × All Is-proposition As

-- If A and B are members of As, and Logically-equivalent As holds,
-- then A and B are logically equivalent.

logically-equivalent :
  {As : Type-list ls} →
  Logically-equivalent As →
  A ∈ As → B ∈ As → A ⇔ B
logically-equivalent (implies , last→first) A∈ B∈ =
  case ≤-total A∈ B∈ of λ where
    (inj₁ A≤B) → record
      { to   = forward _ _ A∈ B∈ A≤B implies
      ; from = around _ _ B∈ A∈ implies last→first
      }
    (inj₂ B≤A) → record
      { to   = around _ _ A∈ B∈ implies last→first
      ; from = forward _ _ B∈ A∈ B≤A implies
      }
  where
  -- One could use "around" for both directions, but that might lead
  -- to unnecessarily complicated proofs.

  forward :
    ∀ {A : Type a} {B : Type b}
      ls (As : Type-list ls) (A∈ : A ∈ As) (B∈ : B ∈ As) →
    A∈ ≤ B∈ → Implies As → A → B
  forward {A = A} {B = B} = λ where
    (_ ∷ []) C A≃ B≃ _ _ →
      A  ↔⟨ A≃ ⟩
      C  ↔⟨ inverse B≃ ⟩□
      B  □
    (_ ∷ _ ∷ _) (C , _) (inj₁ A≃) (inj₁ B≃) _ _ →
      A  ↔⟨ A≃ ⟩
      C  ↔⟨ inverse B≃ ⟩□
      B  □
    (_ ∷ _ ∷ _) (C , As) (inj₁ A≃) (inj₂ B∈) A≤B implies →
      A        ↔⟨ A≃ ⟩
      C        →⟨ Implies-Head implies ⟩
      Head As  →⟨ forward _ _ Head∈ B∈ (Head∈≤ As) (Implies-Tail implies) ⟩□
      B        □
    (_ ∷ _ ∷ _) _ (inj₂ A∈) (inj₂ B∈) A≤B implies →
      forward _ _ A∈ B∈ A≤B (Implies-Tail implies)

  first-implies :
    ∀ ls (As : Type-list (a ∷ ls)) (A∈ : A ∈ As) →
    Implies As →
    Head As → A
  first-implies {A = A} = λ where
    [] B A≃B _ →
      B  ↔⟨ inverse A≃B ⟩□
      A  □
    (_ ∷ _) (B , _) (inj₁ A≃B) _ →
      B  ↔⟨ inverse A≃B ⟩□
      A  □
    (_ ∷ _) As (inj₂ A∈) implies →
      Head As         →⟨ Implies-Head implies ⟩
      Head (Tail As)  →⟨ first-implies _ _ A∈ (Implies-Tail implies) ⟩□
      A               □

  implies-last :
    ∀ ls (As : Type-list (a ∷ ls)) (A∈ : A ∈ As) →
    Implies As →
    A → Last As
  implies-last {A = A} = λ where
    [] B A≃B _ →
      A  ↔⟨ A≃B ⟩□
      B  □
    (_ ∷ _) (B , As) (inj₁ A≃B) implies →
      A        ↔⟨ A≃B ⟩
      B        →⟨ Implies-Head implies ⟩
      Head As  →⟨ implies-last _ _ Head∈ (Implies-Tail implies) ⟩□
      Last As  □
    (_ ∷ _) _ (inj₂ A∈) implies →
      implies-last _ _ A∈ (Implies-Tail implies)

  around :
    ∀ {A : Type a} {B : Type b}
      ls (As : Type-list ls) (A∈ : A ∈ As) (B∈ : B ∈ As) →
    Implies As → Last-implies-first As → A → B
  around {A = A} {B = B} (_ ∷ []) C A≃C B≃C _ _ =
    A  ↔⟨ A≃C ⟩
    C  ↔⟨ inverse B≃C ⟩□
    B  □
  around {A = A} {B = B} (_ ∷ _ ∷ _) As A∈ B∈ implies last→first =
    A        →⟨ implies-last _ _ A∈ implies ⟩
    Last As  →⟨ last→first ⟩
    Head As  →⟨ first-implies _ _ B∈ implies ⟩□
    B        □

-- If A and B are members of As, and Equivalent As holds, then A and B
-- are equivalent.

equivalent :
  {As : Type-list ls} →
  Equivalent As →
  A ∈ As → B ∈ As → A ≃ B
equivalent (equiv , prop) A∈ B∈ =
  _↠_.from
    (Eq.≃↠⇔
       (All-∈ (H-level-cong _ 1) prop A∈)
       (All-∈ (H-level-cong _ 1) prop B∈))
    (logically-equivalent equiv A∈ B∈)

-- If the types in Cons A As are logically equivalent, and the types
-- in Cons A Bs are logically equivalent, then the types in
-- Cons A (Append As Bs) are logically equivalent.

Logically-equivalent-Append :
  {A : Type a} {As : Type-list ls₁} {Bs : Type-list ls₂} →
  Logically-equivalent (Cons A As) → Logically-equivalent (Cons A Bs) →
  Logically-equivalent (Cons A (Append As Bs))
Logically-equivalent-Append leq₁@(i₁ , l₁) (i₂ , l₂) =
    implies i₁ i₂ (last-implies-first₁ leq₁)
  , last-implies-first₂ l₁ l₂
  where
  last-implies-first₁ :
    {A : Type a} {As : Type-list ls₁} →
    Logically-equivalent (Cons A As) → Last (Cons A As) → A
  last-implies-first₁ {ls₁ = []}    _       = id
  last-implies-first₁ {ls₁ = _ ∷ _} (_ , l) = l

  last-implies-first₂ :
    {A : Type a} {As : Type-list ls₁} {Bs : Type-list ls₂} →
    Last-implies-first (Cons A As) →
    Last-implies-first (Cons A Bs) →
    Last-implies-first (Cons A (Append As Bs))
  last-implies-first₂ {ls₁ = []}                            _  l₂ = l₂
  last-implies-first₂ {ls₁ = _ ∷ []}          {ls₂ = []}    l₁ _  = l₁
  last-implies-first₂ {ls₁ = _ ∷ []}          {ls₂ = _ ∷ _} _  l₂ = l₂
  last-implies-first₂ {ls₁ = _ ∷ ls₁@(_ ∷ _)}               l₁ l₂ =
    last-implies-first₂ {ls₁ = ls₁} l₁ l₂

  implies :
    {A : Type a} {B : Type b} {As : Type-list ls₁} {Bs : Type-list ls₂} →
    Implies (Cons A As) → Implies (Cons B Bs) →
    (Last (Cons A As) → B) → Implies (Cons A (Append As Bs))
  implies {ls₁ = []} {ls₂ = []} = _

  implies {ls₁ = []} {ls₂ = _ ∷ _} _  i₂ f =
    Implies-Cons (Implies-Head i₂ ∘ f) (Implies-Tail i₂)

  implies {ls₁ = _ ∷ []} {ls₂ = []} i₁ _ f = i₁

  implies {ls₁ = _ ∷ []} {ls₂ = _ ∷ _} i₁ i₂ f =
    i₁ , implies {ls₁ = []} _ i₂ f

  implies {ls₁ = _ ∷ _ ∷ _} i₁ i₂ f =
    Implies-Head i₁ , implies (Implies-Tail i₁) i₂ f

------------------------------------------------------------------------
-- Some combinators that can be used to prove Logically-equivalent As

-- An example below illustrates how the combinators can be used.

infix  -1 finally-⇔
infixr -2 step-⇔ _↔⟨⟩⇔_

-- For an explanation of why step-⇔ takes the last two arguments in
-- the given order, see Equality.step-≡.

step-⇔ :
  (@0 A : Type a) {@0 As : Type-list (b ∷ ls)} →
  Implies {b ∷ ls} As →
  (A → Head As) →
  Implies {a ∷ b ∷ ls} (A , As)
step-⇔ {ls = []}    _ _       f = f
step-⇔ {ls = _ ∷ _} _ implies f = f , implies

syntax step-⇔ A implies A→B = A →⟨ A→B ⟩⇔ implies

finally-⇔ :
  (@0 A : Type a) {@0 B : Type b} → (A → B) → Implies (A , B)
finally-⇔ _ A→B = A→B

syntax finally-⇔ A A→B = A →⟨ A→B ⟩⇔□

_↔⟨⟩⇔_ :
  (@0 A : Type a) {@0 As : Type-list ls} →
  Implies {a ∷ ls} (Cons A As) →
  Implies {a ∷ ls} (Cons A As)
_ ↔⟨⟩⇔ implies = implies

------------------------------------------------------------------------
-- Some examples

private

  -- The unit type is logically equivalent to some lifted variants of
  -- itself.

  ex₁ :
    Logically-equivalent
      ( ⊤
      , ↑ (lsuc lzero) ⊤
      , ↑ (lsuc (lsuc lzero)) ⊤
      )
  ex₁ =
      (⊤                        →⟨ _ ⟩⇔
       ↑ (lsuc lzero) ⊤         →⟨ _ ⟩⇔□)
    , (↑ (lsuc (lsuc lzero)) ⊤  →⟨ _ ⟩□
       ⊤                        □)

  _ : ⊤ ⇔ ↑ (lsuc lzero) ⊤
  _ = logically-equivalent ex₁ (inj₁ F.id) (inj₂ (inj₁ F.id))

  _ : ↑ (lsuc (lsuc lzero)) ⊤ ⇔ ⊤
  _ = logically-equivalent ex₁ (inj₂ (inj₂ F.id)) (inj₁ F.id)

  -- The unit type is equivalent to some lifted variants of itself.

  ex₂ :
    Equivalent
      ( ⊤
      , ↑ (lsuc lzero) ⊤
      , ↑ (lsuc (lsuc lzero)) ⊤
      )
  ex₂ =
      ex₁
    , ( ⊤-prop
      , ↑-closure 1 ⊤-prop
      , ↑-closure 1 ⊤-prop
      )
    where
    ⊤-prop = H-level.mono₁ 0 ⊤-contractible

  _ : ⊤ ≃ ↑ (lsuc lzero) ⊤
  _ = equivalent ex₂ (inj₁ F.id) (inj₂ (inj₁ F.id))

  _ : ↑ (lsuc (lsuc lzero)) ⊤ ≃ ⊤
  _ = equivalent ex₂ (inj₂ (inj₂ F.id)) (inj₁ F.id)
