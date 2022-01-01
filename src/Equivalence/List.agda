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
    a b c l p q : Level
    ls ls₁ ls₂  : List Level
    A B         : Type a
    k           : A

------------------------------------------------------------------------
-- Functions used to compute levels

Type-list-level : List Level → Level
Type-list-level []       = lzero
Type-list-level (a ∷ ls) = lsuc a ⊔ Type-list-level ls

Last-level : Level → List Level → Level
Last-level a []       = a
Last-level a (b ∷ ls) = Last-level b ls

All-level : Level → List Level → Level
All-level p []       = lzero
All-level p (l ∷ ls) = p ⊔ l ⊔ All-level p ls

Any-level : Level → List Level → Level
Any-level = All-level

∈-level : Level → List Level → Level
∈-level = Any-level

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
  Logically-equivalent-level ls ⊔ All-level lzero ls

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

-- The tail of Cons A As is As.

Tail-Cons :
  {A : Type a} {As : Type-list ls} →
  Tail (Cons A As) ≡ As
Tail-Cons {ls = []}    = refl _
Tail-Cons {ls = _ ∷ _} = refl _

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

-- All P As means that P A holds for every type A in As.

All :
  ∀ p (P : ∀ {a} → Type a → Type (a ⊔ p)) →
  Type-list ls → Type (All-level p ls)
All {ls = []}    _ _ _  = ⊤
All {ls = _ ∷ _} p P As = P (Head As) × All p P (Tail As)

-- Any p P As means that P A holds for some type A in As.

Any :
  ∀ p (P : ∀ {a} → Type a → Type (a ⊔ p)) →
  Type-list ls → Type (Any-level p ls)
Any {ls = []}    _ _ _  = ⊥₀
Any {ls = _ ∷ _} p P As = P (Head As) ⊎ Any p P (Tail As)

-- A ∈ As means that A is a member of As.

infix 4 _∈_

_∈_ : Type a → Type-list ls → Type (∈-level a ls)
_∈_ {a = a} A As = Any a (A ≃_) As

-- A ∈⇔ As means that A is a member of As up to logical equivalence.

infix 4 _∈⇔_

_∈⇔_ : Type a → Type-list ls → Type (∈-level a ls)
_∈⇔_ {a = a} A As = Any a (A ⇔_) As

-- The head of a list of types is a member of the list.

Head∈ :
  {As : Type-list (a ∷ ls)} →
  Any a (Head As ↝[ k ]_) As
Head∈ = inj₁ F.id

-- A list's last element is a member of the list.

Last∈ :
  {As : Type-list (a ∷ ls)} →
  Any (Last-level a ls) (Last As ↝[ k ]_) As
Last∈ {ls = []}    = inj₁ F.id
Last∈ {ls = _ ∷ _} = inj₂ Last∈

-- A function used to state the type of Delete.

Delete-levels :
  {As : Type-list ls} → A ∈⇔ As → List Level
Delete-levels {ls = _ ∷ ls} {As = As} (inj₁ _) = ls
Delete-levels {ls = a ∷ ls} {As = As} (inj₂ p) = a ∷ Delete-levels p

-- Removes the element at the given position from the list.

Delete :
  {A : Type a} {As : Type-list ls}
  (A∈As : A ∈⇔ As) → Type-list (Delete-levels A∈As)
Delete {ls = _ ∷ _} {As = As} (inj₁ _) = Tail As
Delete {ls = _ ∷ _} {As = As} (inj₂ p) = Cons (Head As) (Delete p)

-- If A∈As has type A ∈⇔ As and B is a member of Delete A∈As, then B
-- is a member of As.

Delete∈→∈ :
  {A : Type a} {B : Type b} {As : Type-list ls}
  (A∈As : A ∈⇔ As) →
  Any b (B ↝[ k ]_) (Delete A∈As) → Any b (B ↝[ k ]_) As
Delete∈→∈ {ls = _ ∷ _} (inj₁ _) = inj₂

Delete∈→∈ {ls = _ ∷ _} {B = B} {As = As} (inj₂ p) (inj₁ q) = inj₁
  (B                                 ↝⟨ q ⟩
   Head (Cons (Head As) (Delete p))  ↔⟨ Head-Cons (Delete-levels p) ⟩□
   Head As                           □)

Delete∈→∈ {ls = _ ∷ _} (inj₂ p) (inj₂ q) =
  inj₂ (Delete∈→∈ p q′)
  where
  q′ = subst (Any _ _) (Tail-Cons {ls = Delete-levels p}) q

-- An ordering relation for Any.

infix 4 _≤_

_≤_ :
  {P : ∀ {a} → Type a → Type (a ⊔ p)}
  {Q : ∀ {a} → Type a → Type (a ⊔ q)}
  {As : Type-list ls} →
  Any p P As → Any q Q As → Type
_≤_ {ls = _ ∷ _} (inj₁ _) _        = ⊤
_≤_ {ls = _ ∷ _} (inj₂ _) (inj₁ _) = ⊥
_≤_ {ls = _ ∷ _} (inj₂ x) (inj₂ y) = x ≤ y

-- The ordering relation is total.

≤-total :
  {@0 P : ∀ {a} → Type a → Type (a ⊔ p)}
  {@0 Q : ∀ {a} → Type a → Type (a ⊔ q)}
  {@0 As : Type-list ls} →
  (x : Any p P As) (y : Any q Q As) → x ≤ y ⊎ y ≤ x
≤-total {ls = _ ∷ _} (inj₁ _) _        = inj₁ _
≤-total {ls = _ ∷ _} (inj₂ _) (inj₁ _) = inj₂ _
≤-total {ls = _ ∷ _} (inj₂ x) (inj₂ y) = ≤-total x y

-- If P respects equivalences, All P As holds, and A is a member of
-- As, then P A holds.

All-∈ :
  {P : ∀ {a} → Type a → Type (a ⊔ p)} {As : Type-list ls} →
  (∀ {a b} {A : Type a} {B : Type b} → A ≃ B → P A → P B) →
  All p P As → A ∈ As → P A
All-∈ {ls = _ ∷ _} resp (p , _)   (inj₁ A≃) = resp (inverse A≃) p
All-∈ {ls = _ ∷ _} resp (_ , all) (inj₂ A∈) = All-∈ resp all A∈

-- A map function for Any.

Any-map :
  {P : ∀ {a} → Type a → Type (a ⊔ p)}
  {Q : ∀ {a} → Type a → Type (a ⊔ q)}
  {As : Type-list ls} →
  (∀ {a} (A : Type a) → P A → Q A) →
  Any p P As → Any q Q As
Any-map {ls = _ ∷ _} f (inj₁ x) = inj₁ (f _ x)
Any-map {ls = _ ∷ _} f (inj₂ x) = inj₂ (Any-map f x)

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
  {@0 A : Type a} {@0 As : Type-list (b ∷ ls)} →
  (A → Head As) → Implies As → Implies (Cons A As)
Implies-Cons {ls = []}    f _       = f
Implies-Cons {ls = _ ∷ _} f implies = f , implies

-- A tail operation for Implies.

Implies-Tail :
  {@0 As : Type-list (a ∷ ls)} →
  Implies As → Implies (Tail As)
Implies-Tail {ls = []}        implies       = _
Implies-Tail {ls = _ ∷ []}    implies       = _
Implies-Tail {ls = _ ∷ _ ∷ _} (_ , implies) = implies

-- A head operation for Implies.

Implies-Head :
  {@0 As : Type-list (a ∷ b ∷ ls)} →
  Implies As → Head As → Head (Tail As)
Implies-Head {ls = []}    f       = f
Implies-Head {ls = _ ∷ _} (f , _) = f

-- A delete operation for Implies.

Implies-Delete :
  {A : Type a} {Bs : Type-list ls}
  (A∈Bs : A ∈⇔ Bs) → Implies Bs → Implies (Delete A∈Bs)
Implies-Delete {ls = _ ∷ _} (inj₁ _) =
  Implies-Tail
Implies-Delete {ls = _ ∷ _ ∷ []} (inj₂ (inj₁ _)) =
  _
Implies-Delete
  {ls = _ ∷ _ ∷ _ ∷ _} {Bs = B , C , Bs} (inj₂ (inj₁ _)) implies =
  Implies-Cons
    (B        →⟨ Implies-Head implies ⟩
     C        →⟨ Implies-Head (Implies-Tail implies) ⟩□
     Head Bs  □)
    (Implies-Tail (Implies-Tail implies))
Implies-Delete
  {ls = _ ∷ _ ∷ _} {Bs = B , Bs} (inj₂ A∈Bs@(inj₂ A∈)) implies =
  Implies-Cons
    (B                                  →⟨ Implies-Head implies ⟩
     Head Bs                            ↔⟨ inverse $ Head-Cons (Delete-levels A∈) ⟩□
     Head (Cons (Head Bs) (Delete A∈))  □)
    (Implies-Delete A∈Bs (Implies-Tail implies))

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
Equivalent As = Logically-equivalent As × All lzero Is-proposition As

-- If A and B are members of As (up to logical equivalence), and
-- Logically-equivalent As holds, then A and B are logically
-- equivalent.

logically-equivalent :
  {As : Type-list ls} →
  Logically-equivalent As →
  A ∈⇔ As → B ∈⇔ As → A ⇔ B
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
      ls (As : Type-list ls) (A∈ : A ∈⇔ As) (B∈ : B ∈⇔ As) →
    A∈ ≤ B∈ → Implies As → A → B
  forward {A = A} {B = B} = λ where
    (_ ∷ _) As (inj₁ A⇔) (inj₁ B⇔) _ _ →
      A        →⟨ _⇔_.to A⇔ ⟩
      Head As  →⟨ _⇔_.from B⇔ ⟩□
      B        □
    (_ ∷ _ ∷ _) (C , As) (inj₁ A⇔) (inj₂ B∈) _ implies →
      A        →⟨ _⇔_.to A⇔ ⟩
      C        →⟨ Implies-Head implies ⟩
      Head As  →⟨ forward _ _ Head∈ B∈ _ (Implies-Tail implies) ⟩□
      B        □
    (_ ∷ _) _ (inj₂ A∈) (inj₂ B∈) A≤B implies →
      forward _ _ A∈ B∈ A≤B (Implies-Tail implies)

  first-implies :
    ∀ ls (As : Type-list (a ∷ ls)) (A∈ : A ∈⇔ As) →
    Implies As →
    Head As → A
  first-implies {A = A} = λ where
    _ As (inj₁ A⇔Head-As) _ →
      Head As  →⟨ _⇔_.from A⇔Head-As ⟩□
      A        □
    (_ ∷ _) As (inj₂ A∈) implies →
      Head As         →⟨ Implies-Head implies ⟩
      Head (Tail As)  →⟨ first-implies _ _ A∈ (Implies-Tail implies) ⟩□
      A               □

  implies-last :
    ∀ ls (As : Type-list (a ∷ ls)) (A∈ : A ∈⇔ As) →
    Implies As →
    A → Last As
  implies-last {A = A} = λ where
    [] B (inj₁ A⇔B) _ →
      A  →⟨ _⇔_.to A⇔B ⟩□
      B  □
    (_ ∷ _) (B , As) (inj₁ A⇔B) implies →
      A        →⟨ _⇔_.to A⇔B ⟩
      B        →⟨ Implies-Head implies ⟩
      Head As  →⟨ implies-last _ _ Head∈ (Implies-Tail implies) ⟩□
      Last As  □
    (_ ∷ _) _ (inj₂ A∈) implies →
      implies-last _ _ A∈ (Implies-Tail implies)

  around :
    ∀ {A : Type a} {B : Type b}
      ls (As : Type-list ls) (A∈ : A ∈⇔ As) (B∈ : B ∈⇔ As) →
    Implies As → Last-implies-first As → A → B
  around {A = A} {B = B} (_ ∷ []) C (inj₁ A⇔C) (inj₁ B⇔C) _ _ =
    A  →⟨ _⇔_.to A⇔C ⟩
    C  →⟨ _⇔_.from B⇔C ⟩□
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
    (logically-equivalent equiv
       (Any-map (λ _ → from-equivalence) A∈)
       (Any-map (λ _ → from-equivalence) B∈))

-- If A is logically equivalent to B, B is a member of Bs (up to
-- logical equivalence), and Bs is a list of logically equivalent
-- types, then A is a member of Bs (up to logical equivalence). The
-- returned proof "points to" the last element of Bs.

Logically-equivalent→⇔→∈⇔→∈⇔ :
  {Bs : Type-list ls} →
  Logically-equivalent Bs →
  A ⇔ B → B ∈⇔ Bs → A ∈⇔ Bs
Logically-equivalent→⇔→∈⇔→∈⇔
  {ls = _ ∷ _} {A = A} {B = B} {Bs = Bs} eq A⇔B B∈Bs =
  Any-map
    (λ C Last-Bs⇔C →
       A        ↝⟨ A⇔B ⟩
       B        ↝⟨ logically-equivalent eq B∈Bs Last∈ ⟩
       Last Bs  ↝⟨ Last-Bs⇔C ⟩□
       C        □)
    (Last∈ {k = logical-equivalence})

-- If the types in Bs are logically equivalent, and the types in Cs
-- are logically equivalent, and there is some type A that is a member
-- (up to logical equivalence) of both Bs and Cs, and the second
-- membership proof is A∈Cs, then the types in Append As (Delete A∈Cs)
-- are logically equivalent.

Logically-equivalent-Append :
  {A : Type a} {Bs : Type-list ls₁} {Cs : Type-list ls₂} →
  A ∈⇔ Bs → (A∈Cs : A ∈⇔ Cs) →
  Logically-equivalent Bs → Logically-equivalent Cs →
  Logically-equivalent (Append Bs (Delete A∈Cs))
Logically-equivalent-Append A∈Bs A∈Cs eq₁ eq₂ =
    implies A∈Bs A∈Cs eq₁ eq₂
  , last-implies-first A∈Bs A∈Cs eq₁ eq₂
  where
  last-implies-first :
    {A : Type a} {Bs : Type-list ls₁} {Cs : Type-list ls₂} →
    A ∈⇔ Bs → (A∈Cs : A ∈⇔ Cs) →
    Logically-equivalent Bs →
    Logically-equivalent Cs →
    Last-implies-first (Append Bs (Delete A∈Cs))
  last-implies-first
    {ls₁ = _ ∷ []} {ls₂ = _ ∷ []} {A = A} {Bs = B} {Cs = C}
    (inj₁ A⇔B) (inj₁ A⇔C) _ _ =
    _
  last-implies-first
    {ls₁ = _ ∷ []} {ls₂ = _ ∷ _ ∷ _} {A = A} {Bs = B} {Cs = C , Cs}
    (inj₁ A⇔B) A∈C,Cs@(inj₁ _) _ eq₂ =
    Last Cs  →⟨ _⇔_.to (logically-equivalent eq₂ Last∈ A∈C,Cs) ⟩
    A        →⟨ _⇔_.to A⇔B ⟩□
    B        □
  last-implies-first
    {ls₁ = _ ∷ []} {ls₂ = _ ∷ _ ∷ ls₂} {A = A} {Bs = B} {Cs = Cs}
    (inj₁ A⇔B) A∈Cs@(inj₂ _) _ eq₂ =
    Last (Delete A∈Cs)  →⟨ _⇔_.to (logically-equivalent eq₂ (Delete∈→∈ A∈Cs Last∈) A∈Cs) ⟩
    A                   →⟨ _⇔_.to A⇔B ⟩□
    B                   □
  last-implies-first
    {ls₁ = _ ∷ _ ∷ ls₁} {ls₂ = _ ∷ []} {A = A} {Bs = B , Bs} {Cs = C}
    _ (inj₁ A⇔C) (_ , last-implies-first₁) _ =
    Last (Append Bs tt)  ↔⟨ Last-Append-[] ls₁ ⟩
    Last Bs              →⟨ last-implies-first₁ ⟩□
    B                    □
  last-implies-first
    {ls₁ = _ ∷ _ ∷ ls₁} {ls₂ = _ ∷ _ ∷ _}
    {A = A} {Bs = B , Bs} {Cs = C , Cs}
    A∈B,Bs A∈C,Cs@(inj₁ _) eq₁ eq₂ =
    Last (Append Bs Cs)  ↔⟨ Last-Append-∷ ls₁ ⟩
    Last Cs              →⟨ _⇔_.to (logically-equivalent eq₂ Last∈ A∈C,Cs) ⟩
    A                    →⟨ _⇔_.to (logically-equivalent eq₁ A∈B,Bs Head∈) ⟩□
    B                    □
  last-implies-first
    {ls₁ = _ ∷ _ ∷ ls₁} {ls₂ = _ ∷ ls₂@(_ ∷ _)}
    {A = A} {Bs = B , Bs} {Cs = Cs}
    A∈B,Bs A∈Cs@(inj₂ _) eq₁ eq₂ =
    Last (Append Bs (Delete A∈Cs))  ↔⟨ Last-Append-∷ (_ ∷ ls₁) {As = B , _} ⟩
    Last (Delete A∈Cs)              →⟨ _⇔_.to (logically-equivalent eq₂ (Delete∈→∈ A∈Cs Last∈) A∈Cs) ⟩
    A                               →⟨ _⇔_.to (logically-equivalent eq₁ A∈B,Bs Head∈) ⟩□
    B                               □

  implies-∷ :
    {A : Type a} {Bs : Type-list (b ∷ ls₁)} {Cs : Type-list ls₂} →
    A ⇔ Last Bs → (A∈Cs : A ∈⇔ Cs) →
    Implies Bs →
    Logically-equivalent Cs →
    Implies (Append Bs (Delete A∈Cs))
  implies-∷
    {ls₁ = []} {ls₂ = _ ∷ []} {A = A} {Bs = B} {Cs = C}
    A⇔B (inj₁ A⇔C) _ _ = _
  implies-∷
    {ls₁ = []} {ls₂ = _ ∷ _ ∷ ls₂} {A = A} {Bs = B} {Cs = C , Cs}
    A⇔B A∈@(inj₁ A⇔C) _ eq₂@(implies₂ , _) =
    Implies-Cons
      (B        →⟨ _⇔_.from A⇔B ⟩
       A        →⟨ _⇔_.to (logically-equivalent eq₂ A∈ (inj₂ Head∈)) ⟩□
       Head Cs  □)
      (Implies-Tail implies₂)
  implies-∷
    {ls₁ = []} {ls₂ = _ ∷ _ ∷ ls₂} {A = A} {Bs = B} {Cs = C , Cs}
    A⇔B A∈@(inj₂ A∈Cs) _ eq₂@(implies₂ , _) =
    Implies-Cons
      (B                            →⟨ _⇔_.from A⇔B ⟩
       A                            →⟨ _⇔_.to (logically-equivalent eq₂ A∈ Head∈) ⟩
       C                            ↔⟨ inverse $ Head-Cons (Delete-levels A∈Cs) ⟩□
       Head (Cons C (Delete A∈Cs))  □)
      (Implies-Delete A∈ implies₂)
  implies-∷
    {ls₁ = _ ∷ ls₁} {ls₂ = _ ∷ ls₂} {A = A} {Bs = B , Bs} {Cs = Cs}
    A⇔Last-Bs A∈Cs implies₁ eq₂ =
    Implies-Cons
      (B                                                       →⟨ Implies-Head implies₁ ⟩
       Head Bs                                                 ↔⟨ inverse $ Head-Cons (ls₁ ++ _) ⟩□
       Head (Cons (Head Bs) (Append (Tail Bs) (Delete A∈Cs)))  □)
      (implies-∷ A⇔Last-Bs A∈Cs (Implies-Tail implies₁) eq₂)

  implies :
    {A : Type a} {Bs : Type-list ls₁} {Cs : Type-list ls₂} →
    A ∈⇔ Bs → (A∈Cs : A ∈⇔ Cs) →
    Logically-equivalent Bs →
    Logically-equivalent Cs →
    Implies (Append Bs (Delete A∈Cs))
  implies {ls₁ = _ ∷ _} A∈Bs A∈Cs eq₁@(implies₁ , _) eq₂ =
    implies-∷
      (logically-equivalent eq₁ A∈Bs Last∈)
      A∈Cs implies₁ eq₂

------------------------------------------------------------------------
-- Some combinators that can be used to prove Logically-equivalent As

-- An example below illustrates how the combinators can be used.

infix  -1 finally-⇔
infixr -2 step-⇔ step-⇔→ _↔⟨⟩⇔_

-- For an explanation of why step-⇔ and step-⇔→ take the last two
-- arguments in the given order, see Equality.step-≡.

step-⇔ :
  (@0 A : Type a) {@0 As : Type-list (b ∷ ls)} →
  Implies {b ∷ ls} As →
  (A → Head As) →
  Implies {a ∷ b ∷ ls} (A , As)
step-⇔ {ls = []}    _ _       f = f
step-⇔ {ls = _ ∷ _} _ implies f = f , implies

syntax step-⇔ A implies A→B = A →⟨ A→B ⟩⇔ implies

step-⇔→ :
  (@0 A : Type a) {B : Type b} {@0 As : Type-list (c ∷ ls)} →
  Implies {b ∷ c ∷ ls} (B , As) →
  (A → B) →
  Implies {a ∷ c ∷ ls} (A , As)
step-⇔→ _ implies f =
  Implies-Cons (Implies-Head implies ∘ f) (Implies-Tail implies)

syntax step-⇔→ A implies A→B = A →⟨ A→B ⟩⇔→ implies

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
  _ = logically-equivalent ex₁ (inj₂ (inj₂ (inj₁ F.id))) (inj₁ F.id)

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
      , _
      )
    where
    ⊤-prop = H-level.mono₁ 0 ⊤-contractible

  _ : ⊤ ≃ ↑ (lsuc lzero) ⊤
  _ = equivalent ex₂ (inj₁ F.id) (inj₂ (inj₁ F.id))

  _ : ↑ (lsuc (lsuc lzero)) ⊤ ≃ ⊤
  _ = equivalent ex₂ (inj₂ (inj₂ (inj₁ F.id))) (inj₁ F.id)
