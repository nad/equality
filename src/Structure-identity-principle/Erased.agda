------------------------------------------------------------------------
-- A variant of the development in "Internalizing Representation
-- Independence with Univalence" (by Angiuli, Cavallo, Mörtberg and
-- Zeuner) with support for erasure
------------------------------------------------------------------------

-- This development follows parts of "Internalizing Representation
-- Independence with Univalence" (and sometimes the code supporting
-- that paper) fairly closely, but with explicit support for erasure,
-- and there are some other differences. Note that some things
-- discussed in the paper are not included, for instance tactics and
-- most examples.

-- This formalisation was started because an anonymous reviewer asked
-- whether something like this could be done, and when I had made some
-- initial experiments Andrea Vezzosi encouraged me to include more in
-- the formalisation.

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Structure-identity-principle.Erased
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as B using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equality.Path.Isomorphisms.Univalence eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased.Cubical eq as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages.Cubical eq as ECP
  using (Contractibleᴱ)
open import Equivalence-relation equality-with-J
open import Erased.Cubical eq as Er hiding (map; map-id)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional.Erased eq as T
  using (∥_∥ᴱ; ∣_∣)
import List equality-with-J as L
import Maybe equality-with-J as Maybe
import Monad equality-with-J as Monad
import Nat equality-with-J as Nat
open import Quotient.Erased eq as Q using (_/ᴱ_; [_])
open import Univalence-axiom equality-with-J

open import
  Nat.Binary equality-with-J instance-of-[]-cong-axiomatisation
  as Bin using (Bin)

private
  variable
    a b c d e r                                  : Level
    C                                            : Type c
    A A₁ A₂ B B₁ B₂ Ax F f G g M m N P R R₁ R₂ S
      x x′ x₁ x₂ y y′ ys z z₁ z₂                 : C

------------------------------------------------------------------------
-- The structure identity principle

-- Structures.

Structure : (a b : Level) → Type (lsuc (a ⊔ b))
Structure a b = Type a → Type b

-- Types with a given structure.

Type-with : Structure a b → Type (lsuc a ⊔ b)
Type-with {a} F = ∃ λ (A : Type a) → F A

-- Axioms.
--
-- Originally I made the argument of type Type-with F erased. After
-- feedback from Andrea Vezzosi I instead added a use of Erased in
-- _With-the-axioms_ below.

Axioms : Structure a b → (c : Level) → Type (lsuc a ⊔ b ⊔ lsuc c)
Axioms F c = Type-with F → Type c

-- One can add axioms to structures.

_With-the-axioms_ :
  (F : Structure a b) → Axioms F c → Structure a (b ⊔ c)
(F With-the-axioms Ax) A = ∃ λ (x : F A) → Erased (Ax (A , x))

-- A type of predicates defining when a given equivalence (with erased
-- proofs) is structure-preserving.

Structure-preserving-equivalence-predicate :
  Structure a b → (c : Level) → Type (lsuc a ⊔ b ⊔ lsuc c)
Structure-preserving-equivalence-predicate F c =
  (A B : Type-with F) → proj₁ A ≃ᴱ proj₁ B → Type c

-- One can lift a "structure-preserving equivalence predicate" from F
-- to F With-the-axioms Ax.

Lift-With-the-axioms :
  Structure-preserving-equivalence-predicate F c →
  Structure-preserving-equivalence-predicate (F With-the-axioms Ax) c
Lift-With-the-axioms P (A , x , _) (B , y , _) = P (A , x) (B , y)

-- Structure-preserving equivalences (with erased proofs).

infix 4 _≃[_]ᴱ_

_≃[_]ᴱ_ :
  {F : Structure a b} →
  Type-with F → @0 Structure-preserving-equivalence-predicate F c →
  Type-with F →
  Type (a ⊔ c)
A ≃[ P ]ᴱ B = ∃ λ (eq : proj₁ A ≃ᴱ proj₁ B) → Erased (P A B eq)

-- Univalent pairs of structures and predicates.

record Univalent
         (@0 F : Structure a b)
         (@0 P : Structure-preserving-equivalence-predicate F c) :
         Type (lsuc a ⊔ b ⊔ c) where
  field
    -- This field is erased because it uses univalence and EEq.≃ᴱ→≃.

    @0 univalent :
      {A B : Type-with F}
      (eq : proj₁ A ≃ᴱ proj₁ B) →
      P A B eq ≃
      (subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (proj₂ A) ≡ proj₂ B)

-- If Ax is pointwise propositional, then the functions
-- _With-the-axioms Ax and Lift-With-the-axioms preserve
-- Univalent univ.
--
-- This is a variant of Lemma 3.3 from "Internalizing Representation
-- Independence with Univalence".

Univalent-With-the-axioms :
  {@0 P : Structure-preserving-equivalence-predicate F c} →
  @0 (∀ A → Is-proposition (Ax A)) →
  Univalent F P →
  Univalent (F With-the-axioms Ax) (Lift-With-the-axioms P)
Univalent-With-the-axioms
  {F} {Ax} {P} prop u .Univalent.univalent
  {A = A₁ , x₁ , ax₁} {B = A₂ , x₂ , ax₂} eq =

  P (A₁ , x₁) (A₂ , x₂) eq                                            ↝⟨ u .Univalent.univalent eq ⟩

  subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x₁ ≡ x₂                            ↔⟨ ignore-propositional-component (H-level-Erased 1 (prop _)) ⟩

  (subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x₁ , _) ≡ (x₂ , ax₂)              ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $ push-subst-pair _ _ ⟩□

  subst (F With-the-axioms Ax) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (x₁ , ax₁) ≡
  (x₂ , ax₂)                                                          □

-- The structure identity principle.
--
-- This is a variant of Theorem 3.1 from "Internalizing Representation
-- Independence with Univalence". Note that the principle is erased.

@0 sip :
  Univalent F P →
  (A ≃[ P ]ᴱ B) ≃ (A ≡ B)
sip {F} {P} {A} {B} u =
  (A ≃[ P ]ᴱ B)                                                    ↔⟨⟩
  (∃ λ (eq : proj₁ A ≃ᴱ proj₁ B) → Erased (P A B eq))              ↔⟨ (∃-cong λ _ → erased Erased↔) ⟩
  (∃ λ (eq : proj₁ A ≃ᴱ proj₁ B) → P A B eq)                       ↝⟨ Σ-cong
                                                                        (inverse $ EEq.≃≃≃ᴱ F.∘ ≡≃≃ univ)
                                                                        (u .Univalent.univalent) ⟩
  (∃ λ (eq : proj₁ A ≡ proj₁ B) → subst F eq (proj₂ A) ≡ proj₂ B)  ↔⟨ B.Σ-≡,≡↔≡ ⟩□
  (A ≡ B)                                                          □

-- If there is a structure-preserving equivalence (for a univalent
-- pair of a structure and a predicate) between two types with
-- structures, where one side satisfies some axioms, then the other
-- side also satisfies the axioms (in erased contexts), and the
-- resulting triple is equivalent (with erased proofs) to the other
-- one.
--
-- This is a variant of Corollary 3.4 from "Internalizing
-- Representation Independence with Univalence".

induced-structures :
  {@0 P : Structure-preserving-equivalence-predicate F c} →
  @0 Univalent F P →
  (X@(A , x , _) : Type-with (F With-the-axioms Ax)) →
  ((B , y) : Type-with F) →
  (A , x) ≃[ P ]ᴱ (B , y) →
  ∃ λ (ax : Erased (Ax (B , y))) →
    X ≃[ Lift-With-the-axioms P ]ᴱ (B , y , ax)
induced-structures {Ax} u (A , x , ax) (B , y) eq =
    Er.map (subst Ax (_≃_.to (sip u) eq)) ax
  , eq

------------------------------------------------------------------------
-- Some binary relation combinators, along with some properties

-- The converse of a binary relation.

infix 10 _⁻¹

_⁻¹ : (A → B → Type c) → (B → A → Type c)
(R ⁻¹) x y = R y x

-- Propositionally truncated composition of two binary relations (the
-- definition uses ∥_∥ᴱ).

infixr 9 _;ᴱ_

_;ᴱ_ :
  {B : Type b} →
  (A → B → Type d) → (B → C → Type e) → A → C → Type (b ⊔ d ⊔ e)
(R ;ᴱ S) x z = ∥ (∃ λ y → R x y × S y z) ∥ᴱ

-- Two ways to compose a relation and its converse.

infix 10 _⟵ _⟶

_⟵ : {B : Type b} → (A → B → Type c) → A → A → Type (b ⊔ c)
R ⟵ = R ;ᴱ R ⁻¹

_⟶ : {A : Type a} → (A → B → Type c) → B → B → Type (a ⊔ c)
R ⟶ = R ⁻¹ ;ᴱ R

-- If R is a propositional equivalence relation targetting a certain
-- universe, then R ⟵ is pointwise logically equivalent (with erased
-- proofs) to R.

⟵≃ᴱ :
  {A : Type a}
  {R : A → A → Type a} →
  @0 (∀ x y → Is-proposition (R x y)) →
  Is-equivalence-relation R →
  ∀ {x y} → (R ⟵) x y ≃ᴱ R x y
⟵≃ᴱ prop equiv =
  EEq.⇔→≃ᴱ
    T.truncation-is-proposition
    (prop _ _)
    (T.rec λ where
       .T.truncation-is-propositionʳ → prop _ _
       .T.∣∣ʳ (_ , Rxy , Rzy)        →
         E.transitive Rxy (E.symmetric Rzy))
    (λ Rxz → ∣ _ , Rxz , E.reflexive ∣)
  where
  module E = Is-equivalence-relation equiv

-- If R is a propositional equivalence relation targetting a certain
-- universe, then R ⟶ is pointwise logically equivalent (with erased
-- proofs) to R.

⟶≃ᴱ :
  {A : Type a}
  {R : A → A → Type a} →
  @0 (∀ x y → Is-proposition (R x y)) →
  Is-equivalence-relation R →
  ∀ {x y} → (R ⟶) x y ≃ᴱ R x y
⟶≃ᴱ prop equiv =
  EEq.⇔→≃ᴱ
    T.truncation-is-proposition
    (prop _ _)
    (T.rec λ where
       .T.truncation-is-propositionʳ → prop _ _
       .T.∣∣ʳ (_ , Ryx , Ryz)        →
         E.transitive (E.symmetric Ryx) Ryz)
    (λ Rzx →
       ∣ _ , E.symmetric Rzx , E.reflexive ∣)
  where
  module E = Is-equivalence-relation equiv

-- If R is a propositional equivalence relation targetting a certain
-- universe, then R ⟵ is equal to R (in erased contexts).

@0 ⟵≡ :
  {A : Type a}
  {R : A → A → Type a} →
  (∀ x y → Is-proposition (R x y)) →
  Is-equivalence-relation R →
  R ⟵ ≡ R
⟵≡ prop equiv =
  ⟨ext⟩ λ _ → ⟨ext⟩ λ _ →
  ≃⇒≡ univ $
  EEq.≃ᴱ→≃ $
  ⟵≃ᴱ prop equiv

-- If R is a propositional equivalence relation targetting a certain
-- universe, then R ⟶ is equal to R (in erased contexts).

@0 ⟶≡ :
  {A : Type a}
  {R : A → A → Type a} →
  (∀ x y → Is-proposition (R x y)) →
  Is-equivalence-relation R →
  R ⟶ ≡ R
⟶≡ prop equiv =
  ⟨ext⟩ λ _ → ⟨ext⟩ λ _ →
  ≃⇒≡ univ $
  EEq.≃ᴱ→≃ $
  ⟶≃ᴱ prop equiv

-- The graph of a function.

Graph : {A : Type a} {B : Type b} → (A → B) → A → B → Type b
Graph f x y = f x ≡ y

-- If R is a propositional equivalence relation targetting a certain
-- universe, then Graph (Q.[_] {R = R}) ⟵ is equal to R (in erased
-- contexts).

@0 Graph-[]-⟵≡ :
  {A : Type a}
  {R : A → A → Type a} →
  (∀ x y → Is-proposition (R x y)) →
  Is-equivalence-relation R →
  Graph (Q.[_] {R = R}) ⟵ ≡ R
Graph-[]-⟵≡ {R} prop equiv =
  ⟨ext⟩ λ x → ⟨ext⟩ λ y →
  let
    lemma =
      Eq.⇔→≃
        T.truncation-is-proposition
        Q./ᴱ-is-set
        (T.rec λ @0 where
           .T.truncation-is-propositionʳ → Q./ᴱ-is-set
           .T.∣∣ʳ (_ , [x]≡z , [y]≡z)    → trans [x]≡z (sym [y]≡z))
        (λ [x]≡[y] → ∣ _ , [x]≡[y] , refl _ ∣)
  in
  ≃⇒≡ univ
    ((Graph [_] ⟵) x y  ↝⟨ lemma ⟩
     [ x ] ≡ [ y ]      ↔⟨ inverse $ Q.related≃[equal] equiv (prop _ _) ⟩□
     R x y              □)

-- If R is a propositional equivalence relation, then
-- R ;ᴱ Graph ([_] {R = R}) is equal to Graph ([_] {R = R}) (in erased
-- contexts).

@0 ;ᴱ-Graph-[]≡Graph-[] :
  {A : Type a}
  {R : A → A → Type r} →
  (∀ x y → Is-proposition (R x y)) →
  Is-equivalence-relation R →
  R ;ᴱ Graph ([_] {R = R}) ≡ Graph ([_] {R = R})
;ᴱ-Graph-[]≡Graph-[] {R} prop equiv =
  ⟨ext⟩ λ x → ⟨ext⟩ λ y →
  ≃⇒≡ univ $
  flip
    (Q.elim-prop
       {P = λ y → (R ;ᴱ Graph ([_] {R = R})) x y ≃
                  Graph ([_] {R = R}) x y})
    y
    λ @0 where
      .Q.is-propositionʳ _ →
        Eq.left-closure ext 0 $
        T.truncation-is-proposition
      .Q.[]ʳ y →
        Eq.⇔→≃
          T.truncation-is-proposition
          Q./ᴱ-is-set
          (T.rec λ @0 where
             .T.Rec.truncation-is-propositionʳ →
               Q./ᴱ-is-set
             .T.Rec.∣∣ʳ (z , Rxz , [z]≡[y]) →
               [ x ]  ≡⟨ Q.[]-respects-relation Rxz ⟩
               [ z ]  ≡⟨ [z]≡[y] ⟩∎
               [ y ]  ∎)
          ([ x ] ≡ [ y ]             ↔⟨ inverse $ Q.related≃[equal] equiv (prop _ _) ⟩
           R x y                     ↝⟨ (λ Rxy → ∣ _ , Rxy , refl _ ∣) ⟩
           (R ;ᴱ Graph [_]) x [ y ]  □)

------------------------------------------------------------------------
-- Quasi-equivalence relations

-- Quasi-PERs, or zigzag-complete relations (following Krishnaswami
-- and Dreyer, see "Internalizing Relational Parametricity in the
-- Extensional Calculus of Constructions").
--
-- Angiuli et al. only define what it means to be a quasi-PER for
-- propositional relations. The following definition applies to
-- arbitrary relations.

Is-QPER :
  {A : Type a} {B : Type b} →
  (A → B → Type c) → Type (a ⊔ b ⊔ c)
Is-QPER R =
  ∀ {x x′ y y′} →
  R x y → R x′ y → R x′ y′ → R x y′

-- Quasi-equivalence relations (QERs), defined using ∥_∥ᴱ instead of
-- ∥_∥.

Is-QER :
  {A : Type a} {B : Type b} →
  (A → B → Type c) → Type (a ⊔ b ⊔ c)
Is-QER R =
  Is-QPER R ×
  (∀ x → ∥ ∃ (λ y → R x y) ∥ᴱ) ×
  (∀ y → ∥ ∃ (λ x → R x y) ∥ᴱ)

-- Quasi-equivalence relations (QERs), defined using ∥_∥ᴱ instead of
-- ∥_∥, and with some parts erased.

Is-QERᴱ :
  {A : Type a} {B : Type b} →
  @0 (A → B → Type c) → Type (a ⊔ b ⊔ c)
Is-QERᴱ R =
  Erased (Is-QPER R) ×
  (∀ x → ∥ ∃ (λ y → Erased (R x y)) ∥ᴱ) ×
  (∀ y → ∥ ∃ (λ x → Erased (R x y)) ∥ᴱ)

-- Is-QERᴱ can be expressed using Is-QER and Erased.

Is-QERᴱ≃Is-QER-Erased :
  {@0 R : A → B → Type r} →
  Is-QERᴱ R ≃ Is-QER (λ x y → Erased (R x y))
Is-QERᴱ≃Is-QER-Erased {A} {B} {R} = ×-cong₁ λ _ →

  Erased (∀ {x x′ y y′} → R x y → R x′ y → R x′ y′ → R x y′)  ↝⟨ Erased-cong lemma ⟩

  Erased (∀ x x′ y y′ → R x y → R x′ y → R x′ y′ → R x y′)    ↝⟨ (∀-cong ext λ _ →
                                                                  (∀-cong ext λ _ →
                                                                   (∀-cong ext λ _ →
                                                                    Erased-Π↔Π ext) F.∘
                                                                   Erased-Π↔Π ext) F.∘
                                                                  Erased-Π↔Π ext) F.∘
                                                                 Erased-Π↔Π ext ⟩

  (∀ x x′ y y′ → Erased (R x y → R x′ y → R x′ y′ → R x y′))  ↝⟨ (∀-cong ext λ _ →
                                                                  ∀-cong ext λ _ →
                                                                  ∀-cong ext λ _ →
                                                                  ∀-cong ext λ _ →
                                                                  (∀-cong ext λ _ →
                                                                   (∀-cong ext λ _ →
                                                                    Erased-Π↔Π-Erased ext) F.∘
                                                                   Erased-Π↔Π-Erased ext) F.∘
                                                                  Erased-Π↔Π-Erased ext) ⟩
  (∀ x x′ y y′ →
   Erased (R x y) → Erased (R x′ y) →
   Erased (R x′ y′) → Erased (R x y′))                        ↝⟨ inverse lemma ⟩□

  (∀ {x x′ y y′} →
   Erased (R x y) → Erased (R x′ y) →
   Erased (R x′ y′) → Erased (R x y′))                        □
  where
  lemma :
    {P : A → A → B → B → Type r} →
    (∀ {x x′ y y′} → P x x′ y y′) ≃
    (∀ x x′ y y′ → P x x′ y y′)
  lemma = Eq.↔⇒≃ $
    (∀-cong ext λ _ →
     (∀-cong ext λ _ →
      (∀-cong ext λ _ →
       B.implicit-Π↔Π) F.∘
      B.implicit-Π↔Π) F.∘
     B.implicit-Π↔Π) F.∘
    B.implicit-Π↔Π

-- Is-QER R implies Is-QERᴱ R.

Is-QER→Is-QERᴱ : Is-QER R → Is-QERᴱ R
Is-QER→Is-QERᴱ =
  [_]→
    ×-cong
  (∀-cong _ λ x →
   T.∥∥ᴱ-map $ ∃-cong λ _ → [_]→)
    ×-cong
  (∀-cong _ λ x →
   T.∥∥ᴱ-map $ ∃-cong λ _ → [_]→)

-- In erased contexts Is-QER R is equivalent to Is-QERᴱ R.

@0 Is-QER≃Is-QERᴱ : Is-QER R ≃ Is-QERᴱ R
Is-QER≃Is-QERᴱ = Eq.↔⇒≃ $ inverse $
  Erased↔ .erased
    ×-cong
  (∀-cong ext λ x →
   T.∥∥ᴱ-cong $ ∃-cong λ _ → Erased↔ .erased)
    ×-cong
  (∀-cong ext λ x →
   T.∥∥ᴱ-cong $ ∃-cong λ _ → Erased↔ .erased)

-- The forward direction of Is-QER≃Is-QERᴱ {R = R} is definitionally
-- equal to Is-QER→Is-QERᴱ.

_ : _≃_.to (Is-QER≃Is-QERᴱ {R = R}) ≡ Is-QER→Is-QERᴱ
_ = refl _

-- If Is-QER R holds, then R ⟵ is an equivalence relation.

Is-QER→Is-equivalence-relation-⟵ :
  Is-QER R →
  Is-equivalence-relation (R ⟵)
Is-QER→Is-equivalence-relation-⟵ (qper , lr , rl) = λ where
  .Is-equivalence-relation.reflexive {x} →
    T.∥∥ᴱ-map (λ (y , Rxy) → y , Rxy , Rxy) (lr x)
  .Is-equivalence-relation.symmetric →
    T.∥∥ᴱ-map (Σ-map id swap)
  .Is-equivalence-relation.transitive →
    T.rec λ where
      .T.truncation-is-propositionʳ →
        Π-closure ext 1 λ _ →
        T.truncation-is-proposition
      .T.∣∣ʳ (_ , Rx₁y₁ , Rx₂y₁) → T.∥∥ᴱ-map
        λ (_ , Rx₂y₂ , Rx₃y₂) →
          _ , qper Rx₁y₁ Rx₂y₁ Rx₂y₂ , Rx₃y₂

-- If Is-QERᴱ R holds, then R ⟵ is an equivalence relation (in erased
-- contexts).

@0 Is-QERᴱ→Is-equivalence-relation-⟵ :
  Is-QERᴱ R →
  Is-equivalence-relation (R ⟵)
Is-QERᴱ→Is-equivalence-relation-⟵ {R} =
  Is-QERᴱ R                      ↔⟨ inverse Is-QER≃Is-QERᴱ ⟩
  Is-QER R                       ↝⟨ Is-QER→Is-equivalence-relation-⟵ ⟩□
  Is-equivalence-relation (R ⟵)  □

-- If Is-QER R holds, then R ⟶ is an equivalence relation.

Is-QER→Is-equivalence-relation-⟶ :
  Is-QER R →
  Is-equivalence-relation (R ⟶)
Is-QER→Is-equivalence-relation-⟶ (qper , lr , rl) = λ where
  .Is-equivalence-relation.reflexive {x = y} →
    T.∥∥ᴱ-map (λ (x , Rxy) → x , Rxy , Rxy) (rl y)
  .Is-equivalence-relation.symmetric →
    T.∥∥ᴱ-map (Σ-map id swap)
  .Is-equivalence-relation.transitive →
    T.rec λ where
      .T.truncation-is-propositionʳ →
        Π-closure ext 1 λ _ →
        T.truncation-is-proposition
      .T.∣∣ʳ (_ , Rx₁y₁ , Rx₁y₂) → T.∥∥ᴱ-map
        λ (_ , Rx₂y₂ , Rx₂y₃) →
          _ , qper Rx₂y₂ Rx₁y₂ Rx₁y₁ , Rx₂y₃

-- If Is-QERᴱ R holds, then R ⟶ is an equivalence relation (in erased
-- contexts).

@0 Is-QERᴱ→Is-equivalence-relation-⟶ :
  Is-QERᴱ R →
  Is-equivalence-relation (R ⟶)
Is-QERᴱ→Is-equivalence-relation-⟶ {R} =
  Is-QERᴱ R                      ↔⟨ inverse Is-QER≃Is-QERᴱ ⟩
  Is-QER R                       ↝⟨ Is-QER→Is-equivalence-relation-⟶ ⟩□
  Is-equivalence-relation (R ⟶)  □

-- A propositional QER R can be turned into an equivalence (with
-- erased proofs) satisfying a certain (partly erased) condition.
--
-- This is a variant of Lemma 5.4 from "Internalizing Representation
-- Independence with Univalence".

/ᴱ⟵≃ᴱ/ᴱ⟶ :
  Is-QER R →
  @0 (∀ x y → Is-proposition (R x y)) →
  ∃ λ (eq : A /ᴱ R ⟵ ≃ᴱ B /ᴱ R ⟶) →
    ∀ x y →
    ∃ λ (f : _≃ᴱ_.to eq [ x ] ≡ [ y ] → R x y) →
      Erased (Is-equivalence f)
/ᴱ⟵≃ᴱ/ᴱ⟶ {A} {B} {R} qer@(qper , lr , rl) prop =
    EEq.↔→≃ᴱ to from to-from from-to
  , (λ _ _ →
         to″
       , [ _≃_.is-equivalence $
           Eq.⇔→≃ Q./ᴱ-is-set (prop _ _) to″ from″
         ])
  where
  to′ : ∥ ∃ (R x) ∥ᴱ → B /ᴱ R ⟶
  to′ =
    _≃_.to (Q.Σ→Erased-Constant≃∥∥ᴱ→ Q./ᴱ-is-set)
      ( [_] ∘ proj₁
      , [ (λ (_ , r₁) (_ , r₂) →
             Q.[]-respects-relation ∣ _ , r₁ , r₂ ∣)
        ]
      )

  @0 to′-lemma :
    R x y → R x′ y →
    (p  : ∥ ∃ (R x) ∥ᴱ)
    (p′ : ∥ ∃ (R x′) ∥ᴱ) →
    to′ p ≡ to′ p′
  to′-lemma Rxy Rx′y = T.elim λ @0 where
    .T.truncation-is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Q./ᴱ-is-set
    .T.∣∣ʳ (y₁ , Rxy₁) → T.elim λ @0 where
      .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
      .T.∣∣ʳ (y₂ , Rx′y₂)             →
        [ y₁ ]  ≡⟨ Q.[]-respects-relation ∣ _ , Rxy₁ , qper Rxy Rx′y Rx′y₂ ∣ ⟩∎
        [ y₂ ]  ∎

  to : A /ᴱ R ⟵ → B /ᴱ R ⟶
  to = Q.rec λ where
    .Q.is-setʳ → Q./ᴱ-is-set

    .Q.[]ʳ → to′ ∘ lr

    .Q.[]-respects-relationʳ {x} {y = x′} → T.elim λ @0 where
      .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
      .T.∣∣ʳ (_ , Rxy , Rx′y)         →
        to′ (lr x)   ≡⟨ to′-lemma Rxy Rx′y (lr x) (lr x′) ⟩∎
        to′ (lr x′)  ∎

  from′ : ∥ ∃ ((R ⁻¹) y) ∥ᴱ → A /ᴱ R ⟵
  from′ =
    _≃_.to (Q.Σ→Erased-Constant≃∥∥ᴱ→ Q./ᴱ-is-set)
      ( [_] ∘ proj₁
      , [ (λ (_ , r₁) (_ , r₂) →
             Q.[]-respects-relation ∣ _ , r₁ , r₂ ∣)
        ]
      )

  @0 from′-lemma :
    R x y → R x y′ →
    (p  : ∥ ∃ ((R ⁻¹) y) ∥ᴱ)
    (p′ : ∥ ∃ ((R ⁻¹) y′) ∥ᴱ) →
    from′ p ≡ from′ p′
  from′-lemma Rxy Rxy′ = T.elim λ @0 where
    .T.truncation-is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Q./ᴱ-is-set
    .T.∣∣ʳ (x₁ , Rx₁y) → T.elim λ @0 where
      .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
      .T.∣∣ʳ (x₂ , Rx₂y′)             →
        [ x₁ ]  ≡⟨ Q.[]-respects-relation ∣ _ , Rx₁y , qper Rx₂y′ Rxy′ Rxy ∣ ⟩∎
        [ x₂ ]  ∎

  from : B /ᴱ R ⟶ → A /ᴱ R ⟵
  from = Q.rec λ where
    .Q.is-setʳ → Q./ᴱ-is-set

    .Q.[]ʳ → from′ ∘ rl

    .Q.[]-respects-relationʳ {x = y} {y = y′} → T.elim λ @0 where
      .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
      .T.∣∣ʳ (_ , Rxy , Rxy′)         →
        from′ (rl y)   ≡⟨ from′-lemma Rxy Rxy′ (rl y) (rl y′) ⟩∎
        from′ (rl y′)  ∎

  @0 to′≡[] :
    R x y → (p : ∥ ∃ (R x) ∥ᴱ) →
    to′ p ≡ [ y ]
  to′≡[] {x} {y} Rxy = T.elim λ @0 where
    .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
    .T.∣∣ʳ (y′ , Rxy′)              →
      [ y′ ]  ≡⟨ Q.[]-respects-relation ∣ _ , Rxy′ , Rxy ∣ ⟩∎
      [ y ]   ∎

  @0 to-from′ :
    ∀ y (p : ∥ ∃ ((R ⁻¹) y) ∥ᴱ) →
    to (from′ p) ≡ [ y ]
  to-from′ y = T.elim λ @0 where
    .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
    .T.∣∣ʳ (x , Rxy)                →
      to′ (lr x)  ≡⟨ to′≡[] Rxy (lr x) ⟩∎
      [ y ]       ∎

  @0 to-from : ∀ y → to (from y) ≡ y
  to-from = Q.elim-prop λ @0 where
    .Q.is-propositionʳ _ → Q./ᴱ-is-set
    .Q.[]ʳ y             →
      to (from′ (rl y))  ≡⟨ to-from′ y (rl y) ⟩∎
      [ y ]              ∎

  @0 from′≡[] :
    R x y → (p : ∥ ∃ ((R ⁻¹) y) ∥ᴱ) →
    from′ p ≡ [ x ]
  from′≡[] {x} {y} Rxy = T.elim λ @0 where
    .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
    .T.∣∣ʳ (x′ , Rx′y)              →
      [ x′ ]  ≡⟨ Q.[]-respects-relation ∣ _ , Rx′y , Rxy ∣ ⟩∎
      [ x ]   ∎

  @0 from-to′ :
    ∀ x (p : ∥ ∃ (R x) ∥ᴱ) →
    from (to′ p) ≡ [ x ]
  from-to′ x = T.elim λ @0 where
    .T.truncation-is-propositionʳ _ → Q./ᴱ-is-set
    .T.∣∣ʳ (y , Rxy)                →
      from′ (rl y)  ≡⟨ from′≡[] Rxy (rl y) ⟩∎
      [ x ]         ∎

  @0 from-to : ∀ x → from (to x) ≡ x
  from-to = Q.elim-prop λ @0 where
    .Q.is-propositionʳ _ → Q./ᴱ-is-set
    .Q.[]ʳ x             →
      from (to′ (lr x))  ≡⟨ from-to′ x (lr x) ⟩∎
      [ x ]              ∎

  to″ : to [ x ] ≡ [ y ] → R x y
  to″ {x} {y} =
    to′ (lr x) ≡ [ y ]  ↝⟨ flip (T.elim {P = λ p → to′ p ≡ [ y ] → R x y}) (lr x) (λ where
                             .T.truncation-is-propositionʳ _ →
                               Π-closure ext 1 λ _ →
                               prop _ _
                             .T.∣∣ʳ (y′ , Rxy′) →
                               [ y′ ] ≡ [ y ]  ↝⟨ Q.effective
                                                    (Is-QER→Is-equivalence-relation-⟶ qer)
                                                    T.truncation-is-proposition
                                                    ∣ _ , Rxy′ , Rxy′ ∣ ⟩
                               (R ⟶) y′ y      ↝⟨ T.rec (λ where
                                                    .T.truncation-is-propositionʳ → prop _ _
                                                    .T.∣∣ʳ (_ , Rx′y′ , Rx′y)     →
                                                      qper Rxy′ Rx′y′ Rx′y) ⟩□
                               R x y           □) ⟩□
    R x y               □

  @0 from″ : R x y → to [ x ] ≡ [ y ]
  from″ {x} {y} Rxy =
    to′ (lr x)  ≡⟨ to′≡[] Rxy (lr x) ⟩∎
    [ y ]       ∎

-- A propositional QER R (with erased proofs) can be turned into an
-- equivalence (with erased proofs) satisfying a certain (erased)
-- condition.
--
-- This is another variant of Lemma 5.4 from "Internalizing
-- Representation Independence with Univalence".

/ᴱ⟵≃ᴱ/ᴱ⟶ᴱ :
  {@0 R : A → B → Type c} →
  Is-QERᴱ R →
  @0 (∀ x y → Is-proposition (R x y)) →
  ∃ λ (eq : A /ᴱ R ⟵ ≃ᴱ B /ᴱ R ⟶) →
    Erased (∀ x y → (_≃ᴱ_.to eq [ x ] ≡ [ y ]) ≃ R x y)
/ᴱ⟵≃ᴱ/ᴱ⟶ᴱ {A} {B} {R} qer prop =                          $⟨ [ prop ] ⟩

  Erased (∀ x y → Is-proposition (R x y))                 ↝⟨ (λ ([ hyp ]) x y → H-level-Erased 1 (hyp x y)) ⦂ (_ → _) ⟩

  (∀ x y → Is-proposition (Rᴱ x y))                       ↝⟨ (λ prop → /ᴱ⟵≃ᴱ/ᴱ⟶ (_≃_.to Is-QERᴱ≃Is-QER-Erased qer) prop) ⟩

  (∃ λ (eq : A /ᴱ Rᴱ ⟵ ≃ᴱ B /ᴱ Rᴱ ⟶) →
     ∀ x y →
     ∃ λ (f : _≃ᴱ_.to eq [ x ] ≡ [ y ] → Rᴱ x y) →
       Erased (Is-equivalence f))                         ↝⟨ (λ (eq , ok) → drop-ᴱ eq , [ drop-ᴱ-ok eq ok ]) ⟩□

  (∃ λ (eq : A /ᴱ R ⟵ ≃ᴱ B /ᴱ R ⟶) →
    Erased (∀ x y → (_≃ᴱ_.to eq [ x ] ≡ [ y ]) ≃ R x y))  □
  where
  Rᴱ = λ x y → Erased (R x y)

  @0 lemma :
    ∀ x y →
    ((λ x y → Erased (R₁ x y)) ;ᴱ (λ x y → Erased (R₂ x y))) x y ⇔
    (R₁ ;ᴱ R₂) x y
  lemma {R₁} {R₂} x z =
    ∥ (∃ λ y → Erased (R₁ x y) × Erased (R₂ y z)) ∥ᴱ  ↔⟨ (T.∥∥ᴱ-cong $ ∃-cong λ _ →
                                                          Erased↔ .erased
                                                            ×-cong
                                                          Erased↔ .erased) ⟩□
    ∥ (∃ λ y → R₁ x y × R₂ y z) ∥ᴱ                    □

  drop-ᴱ :
    A /ᴱ Rᴱ ⟵ ≃ᴱ B /ᴱ Rᴱ ⟶ →
    A /ᴱ R ⟵ ≃ᴱ B /ᴱ R ⟶
  drop-ᴱ eq =
    A /ᴱ R ⟵   ↔⟨ Eq.id Q./ᴱ-cong (λ x y → inverse (lemma {R₁ = R} {R₂ = R ⁻¹} x y)) ⟩
    A /ᴱ Rᴱ ⟵  ↝⟨ eq ⟩
    B /ᴱ Rᴱ ⟶  ↔⟨ Eq.id Q./ᴱ-cong lemma ⟩□
    B /ᴱ R ⟶   □

  @0 drop-ᴱ-ok :
    (eq : A /ᴱ Rᴱ ⟵ ≃ᴱ B /ᴱ Rᴱ ⟶) →
    (∀ x y →
     ∃ λ (f : _≃ᴱ_.to eq [ x ] ≡ [ y ] → Rᴱ x y) →
       Erased (Is-equivalence f)) →
    ∀ x y → (_≃ᴱ_.to (drop-ᴱ eq) [ x ] ≡ [ y ]) ≃ R x y
  drop-ᴱ-ok eq ok x y =
    _≃ᴱ_.to (drop-ᴱ eq) [ x ] ≡ [ y ]                          ↔⟨⟩
    _≃_.to (Eq.id Q./ᴱ-cong lemma) (_≃ᴱ_.to eq [ x ]) ≡ [ y ]  ↝⟨ Eq.≃-≡ (Eq.id Q./ᴱ-cong lemma) ⟩
    _≃ᴱ_.to eq [ x ] ≡ [ y ]                                   ↝⟨ (let f , [ eq ] = ok x y in Eq.⟨ f , eq ⟩) ⟩
    Rᴱ x y                                                     ↔⟨ Erased↔ .erased ⟩□
    R x y                                                      □

------------------------------------------------------------------------
-- Relation transformers

-- Relation transformers for a given structure.

Relation-transformer-for :
  Structure a b → Type (lsuc (a ⊔ b))
Relation-transformer-for {a} {b} F =
  ∀ {A B} → (A → B → Type a) → F A → F B → Type b

-- A notion of "suitable" relation transformers.

record Suitable
         {F : Structure a b}
         (@0 G : Relation-transformer-for F) :
         Type (lsuc a ⊔ b) where
  field
    -- F preserves Is-set.

    @0 preserves-is-set :
      Is-set A → Is-set (F A)

    -- G preserves a variant of Is-proposition.

    @0 preserves-is-proposition :
      (∀ x y → Is-proposition (R x y)) →
      ∀ x y → Is-proposition (G R x y)

    -- G is "symmetric" for propositional relations.

    @0 symmetric :
      (∀ x y → Is-proposition (R x y)) →
      G R x y → G (R ⁻¹) y x

    -- G is "transitive" for propositional relations.

    @0 transitive :
      (∀ x y → Is-proposition (R x y)) →
      (∀ x y → Is-proposition (S x y)) →
      G R x y → G S y z → G (R ;ᴱ S) x z

    -- Descent to quotients. Note that this is the only non-erased
    -- field of this record type.

    descent :
      {@0 R : A → A → Type a} →
      @0 (∀ x y → Is-proposition (R x y)) →
      @0 Is-equivalence-relation R →
      @0 G R x x →
      Contractibleᴱ (∃ λ (y : F (A /ᴱ R)) → Erased (G (Graph [_]) x y))

  -- A variant of transitive.

  @0 transitive-;ᴱ :
      (∀ x y → Is-proposition (R x y)) →
      (∀ x y → Is-proposition (S x y)) →
      ∀ x z → (G R ;ᴱ G S) x z → G (R ;ᴱ S) x z
  transitive-;ᴱ R-prop S-prop _ _ = T.rec λ @0 where
    .T.truncation-is-propositionʳ →
      preserves-is-proposition
        (λ _ _ → T.truncation-is-proposition) _ _
    .T.∣∣ʳ (_ , GRxy , GSyz) →
      transitive R-prop S-prop GRxy GSyz

-- A variant of Univalent for relation transformers.

Univalentᴿ :
  {F : Structure a b} →
  @0 Relation-transformer-for F → Type (lsuc a ⊔ b)
Univalentᴿ {F} G =
  Suitable G ×
  Univalent F (λ (A , x) (B , y) eq → G (Graph (_≃ᴱ_.to eq)) x y)

-- A notion of "acting on functions" for relation transformers.

record Acts-on-functions
         {F : Structure a b}
         (@0 G : Relation-transformer-for F) :
         Type (lsuc a ⊔ b) where
  field
    -- A map function.

    map : (A → B) → F A → F B

    -- Mapping the identity function is the same thing as applying the
    -- identity function.

    @0 map-id  : map {A = A} id ≡ id

    -- G respects map in a certain way.

    @0 map-map :
      {R₁ : A₁ → B₁ → Type a} {R₂ : A₂ → B₂ → Type a} →
      (∀ {x y} → R₁ x y → R₂ (f x) (g y)) →
      G R₁ x y → G R₂ (map f x) (map g y)

-- Suitable respects equivalences.

Suitable-map :
  {@0 G H : Relation-transformer-for F} →
  @0 (∀ {A B} {R : A → B → _} {x y} → G R x y ≃ H R x y) →
  Suitable G → Suitable H
Suitable-map {G} {H} G≃H s-G = λ where
    .Suitable.preserves-is-set → S.preserves-is-set

    .Suitable.preserves-is-proposition {R} →
      (∀ x y → Is-proposition (R x y))    ↝⟨ S.preserves-is-proposition ⟩
      (∀ x y → Is-proposition (G R x y))  ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → H-level-cong _ 1 G≃H) ⟩□
      (∀ x y → Is-proposition (H R x y))  □

    .Suitable.symmetric {R} {x} {y} →
      (∀ x y → Is-proposition (R x y))  ↝⟨ S.symmetric ⟩
      (G R x y → G (R ⁻¹) y x)          ↝⟨ →-cong-→ (_≃_.from G≃H) (_≃_.to G≃H) ⟩□
      (H R x y → H (R ⁻¹) y x)          □

    .Suitable.transitive {R} {S} {x} {y} {z} → curry
      ((∀ x y → Is-proposition (R x y)) ×
       (∀ x y → Is-proposition (S x y))      ↝⟨ uncurry S.transitive ⟩

       (G R x y → G S y z → G (R ;ᴱ S) x z)  ↝⟨ →-cong-→ (_≃_.from G≃H) (→-cong-→ (_≃_.from G≃H) (_≃_.to G≃H)) ⟩□

       (H R x y → H S y z → H (R ;ᴱ S) x z)  □)

    .Suitable.descent {x} {R} prop equiv HRxx →           $⟨ [ HRxx ] ⟩
      Erased (H R x x)                                    ↔⟨ Erased-cong (inverse G≃H) ⟩
      Erased (G R x x)                                    ↝⟨ (λ ([ hyp ]) → S.descent prop equiv hyp) ⦂ (_ → _) ⟩
      Contractibleᴱ (∃ λ y → Erased (G (Graph [_]) x y))  ↝⟨ ECP.Contractibleᴱ-cong _ (∃-cong λ _ → Erased-cong G≃H) ⟩□
      Contractibleᴱ (∃ λ y → Erased (H (Graph [_]) x y))  □
  where
  module S = Suitable s-G

-- If R is a propositional QER (with erased proofs) between A and B, G
-- is a suitable relation transformer for F, and G R x y holds, then
-- there are structures in F (A /ᴱ R ⟵) and F (B /ᴱ R ⟶) that are
-- related in a certain way to x and y, respectively, and the two
-- structures are also related to each other by /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ in a certain
-- way.
--
-- This is a variant of Theorem 5.7 from "Internalizing Representation
-- Independence with Univalence". Note that quite a few inputs are
-- erased, and also parts of the result.

Suitable→/ᴱ⟵×/ᴱ⟶ :
  {F : Structure a b}
  ((A , x) (B , y) : Type-with F) →
  {@0 R : A → B → Type a}
  {@0 G : Relation-transformer-for F} →
  Suitable G →
  (qer : Is-QERᴱ R)
  (@0 prop : ∀ x y → Is-proposition (R x y)) →
  @0 G R x y →
  ∃ λ (x′ : F (A /ᴱ R ⟵)) → ∃ λ (y′ : F (B /ᴱ R ⟶)) →
  Erased
    (G (Graph [_]) x x′ × G (Graph [_]) y y′ ×
     G (Graph (_≃ᴱ_.to (/ᴱ⟵≃ᴱ/ᴱ⟶ᴱ qer prop .proj₁))) x′ y′)
Suitable→/ᴱ⟵×/ᴱ⟶ {F} (A , x) (B , y) {R} {G}
  s qer@([ qper ] , _) prop g =
  x″ , y″ , [ (Gxx″ , Gyy″ , g″) ]
  where
  module S = Suitable s

  @0 x∼x : G (R ⟵) x x
  x∼x = S.transitive prop (flip prop) g (S.symmetric prop g)

  @0 y∼y : G (R ⟶) y y
  y∼y = S.transitive (flip prop) prop (S.symmetric prop g) g

  x-lemma :
    Contractibleᴱ
      (∃ λ (x′ : F (A /ᴱ R ⟵)) → Erased (G (Graph [_]) x x′))
  x-lemma =
    S.descent
      (λ _ _ → T.truncation-is-proposition)
      (Is-QERᴱ→Is-equivalence-relation-⟵ qer)
      x∼x

  y-lemma :
    Contractibleᴱ
      (∃ λ (y′ : F (B /ᴱ R ⟶)) → Erased (G (Graph [_]) y y′))
  y-lemma =
    S.descent
      (λ _ _ → T.truncation-is-proposition)
      (Is-QERᴱ→Is-equivalence-relation-⟶ qer)
      y∼y

  x″ = x-lemma .proj₁ .proj₁
  y″ = y-lemma .proj₁ .proj₁

  @0 Gxx″ : G (Graph [_]) x x″
  Gxx″ = x-lemma .proj₁ .proj₂ .erased

  @0 Gyy″ : G (Graph [_]) y y″
  Gyy″ = y-lemma .proj₁ .proj₂ .erased

  @0 g′ : G (Graph [_] ⁻¹ ;ᴱ R ;ᴱ Graph [_]) x″ y″
  g′ =
    S.transitive
      (λ _ _ → Q./ᴱ-is-set)
      (λ _ _ → T.truncation-is-proposition)
      (S.symmetric (λ _ _ → Q./ᴱ-is-set) Gxx″)
      (S.transitive prop (λ _ _ → Q./ᴱ-is-set) g Gyy″)

  equiv = /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ qer prop .proj₁

  @0 to :
    ∀ {x y} →
    (Graph [_] ⁻¹ ;ᴱ R ;ᴱ Graph [_]) [ x ] [ y ] → R x y
  to {x} {y} =
    T.rec λ @0 where
      .T.truncation-is-propositionʳ →
        prop _ _
      .T.∣∣ʳ → uncurry λ x′ → uncurry λ [x′]≡[x] →
        T.rec λ @0 where
          .T.truncation-is-propositionʳ →
            prop _ _
          .T.∣∣ʳ (y′ , Rx′y′ , [y′]≡[y]) →
            let R⟵x′x : (R ⟵) x′ x
                R⟵x′x =
                  _≃_.from
                    (Q.related≃[equal]
                       (Is-QERᴱ→Is-equivalence-relation-⟵ qer)
                       T.truncation-is-proposition)
                    [x′]≡[x]

                R⟶y′y : (R ⟶) y′ y
                R⟶y′y =
                  _≃_.from
                    (Q.related≃[equal]
                       (Is-QERᴱ→Is-equivalence-relation-⟶ qer)
                       T.truncation-is-proposition)
                    [y′]≡[y]
            in
            flip T.rec R⟵x′x λ @0 where
              .T.truncation-is-propositionʳ →
                prop _ _
              .T.∣∣ʳ (_ , Rx′x″ , Rxx″) →
                flip T.rec R⟶y′y λ @0 where
                  .T.truncation-is-propositionʳ →
                    prop _ _
                  .T.∣∣ʳ (_ , Ry″y′ , Ry″y) →
                    qper Rxx″ Rx′x″ (qper Rx′y′ Ry″y′ Ry″y)

  @0 from :
    ∀ {x y} →
    R x y → (Graph [_] ⁻¹ ;ᴱ R ;ᴱ Graph [_]) [ x ] [ y ]
  from Rxy = ∣ _ , refl _ , ∣ _ , Rxy , refl _ ∣ ∣

  @0 lemma :
    ∀ x y →
    (Graph [_] ⁻¹ ;ᴱ R ;ᴱ Graph [_]) x y ≃
    Graph (_≃ᴱ_.to equiv) x y
  lemma = Q.elim-prop λ @0 where
    .Q.is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Eq.left-closure ext 0 T.truncation-is-proposition
    .Q.[]ʳ x → Q.elim-prop λ @0 where
      .Q.is-propositionʳ _ →
        Eq.left-closure ext 0 T.truncation-is-proposition
      .Q.[]ʳ y →
         (Graph [_] ⁻¹ ;ᴱ R ;ᴱ Graph [_]) [ x ] [ y ]  ↝⟨ Eq.⇔→≃ T.truncation-is-proposition (prop _ _) to from ⟩
         R x y                                         ↝⟨ inverse (/ᴱ⟵≃ᴱ/ᴱ⟶ᴱ qer prop .proj₂ .erased _ _) ⟩□
         Graph (_≃ᴱ_.to equiv) [ x ] [ y ]             □

  @0 g″ : G (Graph (_≃ᴱ_.to equiv)) x″ y″
  g″ =
    subst (λ R → G R x″ y″)
      (⟨ext⟩ λ x → ⟨ext⟩ λ y →
       ≃⇒≡ univ (lemma x y))
      g′

-- If R is a propositional QER (with erased proofs) between A and B, G
-- is a univalent relation transformer for F, and G R x y holds, then
-- there are structures x′ : F (A /ᴱ R ⟵) and y′ : F (B /ᴱ R ⟶) that
-- are related in a certain way to x and y, respectively, and
-- furthermore the two values A /ᴱ R ⟵ , x′ and B /ᴱ R ⟶ , y′ of type
-- Type-with F are equal (in erased contexts).
--
-- This is a corollary of Suitable→/ᴱ⟵×/ᴱ⟶, /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ and sip.

Univalentᴿ→/ᴱ⟵×/ᴱ⟶ :
  {F : Structure a b}
  ((A , x) (B , y) : Type-with F) →
  {@0 R : A → B → Type a}
  {@0 G : Relation-transformer-for F} →
  Univalentᴿ G →
  (qer : Is-QERᴱ R)
  (@0 prop : ∀ x y → Is-proposition (R x y)) →
  @0 G R x y →
  ∃ λ (x′ : F (A /ᴱ R ⟵)) → ∃ λ (y′ : F (B /ᴱ R ⟶)) →
  Erased (G (Graph [_]) x x′ × G (Graph [_]) y y′ ×
          _≡_ {A = Type-with F}
            (A /ᴱ R ⟵ , x′) (B /ᴱ R ⟶ , y′))
Univalentᴿ→/ᴱ⟵×/ᴱ⟶ (A , x) (B , y) {R} {G} (s , u) qer prop g =
  let (x′ , y′ , [ x∼x′ , y∼y′ , x′∼y′ ]) =
        Suitable→/ᴱ⟵×/ᴱ⟶ (A , x) (B , y) s qer prop g
  in
    x′
  , y′
  , [ ( x∼x′
      , y∼y′
      , (                                                             $⟨ /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ qer prop .proj₁ , [ x′∼y′ ] ⟩
         (A /ᴱ R ⟵ , x′)
           ≃[ (λ (A , x) (B , y) eq → G (Graph (_≃ᴱ_.to eq)) x y) ]ᴱ
         (B /ᴱ R ⟶ , y′)                                              ↝⟨ sip u ⟩□

         (A /ᴱ R ⟵ , x′) ≡ (B /ᴱ R ⟶ , y′)                            □)
      )
  ]

-- If G is a suitable relation transformer (for F) that acts on
-- functions, and R is a propositional equivalence relation on A, then
-- there is a function from F A /ᴱ G R to F (A /ᴱ R).
--
-- This is a variant of Lemma 5.10 from "Internalizing Representation
-- Independence with Univalence". Note that quite a few inputs are
-- erased.

/ᴱ→/ᴱ :
  {A : Type a}
  {@0 R : A → A → Type a}
  (@0 G : Relation-transformer-for F) →
  Suitable G →
  Acts-on-functions G →
  @0 (∀ x y → Is-proposition (R x y)) →
  @0 Is-equivalence-relation R →
  F A /ᴱ G R → F (A /ᴱ R)
/ᴱ→/ᴱ {F} {R} G s acts prop equiv =
  Q.rec λ where
    .Q.[]ʳ → map [_]

    .Q.is-setʳ → S.preserves-is-set Q./ᴱ-is-set

    .Q.[]-respects-relationʳ {x} {y} GRxy →
      let GRxx =         $⟨ GRxy ⟩
            G R x y      ↝⟨ (λ GRxy → S.transitive prop (flip prop) GRxy (S.symmetric prop GRxy)) ⟩
            G (R ⟵) x x  ↝⟨ subst (λ R → G R _ _) (⟵≡ prop equiv) ⟩□
            G R x x      □

          ((z , _) , [ unique ]) =                              $⟨ GRxx ⟩
            G R x x                                             ↝⟨ (λ GRxx → S.descent prop equiv GRxx) ⦂ (_ → _) ⟩□
            Contractibleᴱ (∃ λ z → Erased (G (Graph [_]) x z))  □

          lemma₁ =                                $⟨ map-map Q.[]-respects-relation GRxx ⟩
            G (Graph [_]) (map id x) (map [_] x)  ↝⟨ subst (λ x′ → G (Graph [_]) x′ (map [_] x)) (cong (_$ x) map-id) ⟩□
            G (Graph [_]) x (map [_] x)           □

          lemma₂ =                                $⟨ map-map Q.[]-respects-relation GRxy ⟩
            G (Graph [_]) (map id x) (map [_] y)  ↝⟨ subst (λ x → G (Graph [_]) x (map [_] y)) (cong (_$ x) map-id) ⟩□
            G (Graph [_]) x (map [_] y)           □
      in
      map [_] x  ≡⟨ sym $ cong proj₁ (unique (_ , [ lemma₁ ])) ⟩
      z          ≡⟨ cong proj₁ (unique (_ , [ lemma₂ ])) ⟩∎
      map [_] y  ∎
  where
  module S = Suitable s
  open Acts-on-functions acts

-- Positive relation transformers.
--
-- Angiuli et al. define this notion for suitable relation
-- transformers that act on functions. This definition works for
-- arbitrary relation transformers G, and instead inludes fields of
-- type Suitable G and Acts-on-functions G. (In their source code
-- Angiuli et al. take a third approach, with the property
-- corresponding to Suitable G as a parameter, and the property
-- corresponding to Acts-on-functions G as a field.)

record Positive
         {F : Structure a b}
         (@0 G : Relation-transformer-for F) :
         Type (lsuc a ⊔ b) where
  field
    -- G is suitable.

    suitable : Suitable G

    -- G acts on functions.

    acts-on-functions : Acts-on-functions G

    -- G is reflexive for a certain relation.

    @0 reflexive-∥≡∥ᴱ : G (λ x y → ∥ x ≡ y ∥ᴱ) x x

    -- The function Suitable.transitive-;ᴱ suitable is an equivalence
    -- (pointwise).

    @0 transitive-;ᴱ⁻¹ :
      {R : A → B → Type a} {S : B → C → Type a}
      (R-prop : ∀ x y → Is-proposition (R x y))
      (S-prop : ∀ x y → Is-proposition (S x y))
      (x : F A) (z : F C) →
      Is-equivalence
        (Suitable.transitive-;ᴱ suitable R-prop S-prop x z)

    -- The function /ᴱ→/ᴱ G suitable acts-on-functions is an
    -- equivalence with erased proofs (pointwise).

    commutes-with-/ᴱ :
      {@0 R : A → A → Type a}
      (@0 prop : ∀ x y → Is-proposition (R x y))
      (@0 equiv : Is-equivalence-relation R) →
      Is-equivalenceᴱ (/ᴱ→/ᴱ G suitable acts-on-functions prop equiv)

  -- G R is reflexive for propositional equivalence relations R (in
  -- erased contexts).

  @0 reflexive :
    (∀ x y → Is-proposition (R x y)) →
    Is-equivalence-relation R →
    ∀ x → G R x x
  reflexive {R} prop equiv x =     $⟨ reflexive-∥≡∥ᴱ ⟩
    G (λ x y → ∥ x ≡ y ∥ᴱ) x x     ↝⟨ A.map-map
                                        (T.rec λ @0 where
                                           .T.truncation-is-propositionʳ →
                                             prop _ _
                                           .T.∣∣ʳ x≡y →
                                             subst (R _) x≡y E.reflexive) ⟩
    G R (A.map id x) (A.map id x)  ↝⟨ subst (uncurry (G R)) (cong (λ f → f x , f x) A.map-id) ⟩□
    G R x x                        □
    where
    module A = Acts-on-functions acts-on-functions
    module E = Is-equivalence-relation equiv

------------------------------------------------------------------------
-- The Const and Constᴿ combinators, along with some properties

-- Constant structures.

Const : Type b → Structure a b
Const B = λ _ → B

-- Relation transformers for Const.

Constᴿ : (B : Type b) → Relation-transformer-for (Const {a = a} B)
Constᴿ _ _ = _≡_

-- When is an equivalence structure-preserving for Const?

Is-Const-equivalence :
  {B : Type b} →
  Structure-preserving-equivalence-predicate (Const {a = a} B) b
Is-Const-equivalence (_ , x) (_ , y) _ = x ≡ y

-- Const and Is-Const-equivalence are univalent.

Const-univalent : Univalent (Const {a = a} B) Is-Const-equivalence
Const-univalent {B} .Univalent.univalent {A = _ , x} {B = _ , y} eq =
  x ≡ y                                           ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $ subst-const _ ⟩□
  subst (Const B) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y  □

-- Constᴿ is suitable for sets.

Constᴿ-suitable : @0 Is-set B → Suitable (Constᴿ {a = a} B)
Constᴿ-suitable set = λ where
  .Suitable.preserves-is-set _             → set
  .Suitable.preserves-is-proposition _ _ _ → set
  .Suitable.symmetric _                    → sym
  .Suitable.transitive _ _                 → trans
  .Suitable.descent _ _ _                  → Contractibleᴱ-Erased-other-singleton

-- Constᴿ is univalent for sets.

Constᴿ-univalent : @0 Is-set B → Univalentᴿ (Constᴿ {a = a} B)
Constᴿ-univalent set = Constᴿ-suitable set , Const-univalent

-- Constᴿ acts on functions.

Constᴿ-acts-on-functions : Acts-on-functions (Constᴿ {a = a} B)
Constᴿ-acts-on-functions = λ where
  .Acts-on-functions.map _     → id
  .Acts-on-functions.map-id    → refl _
  .Acts-on-functions.map-map _ → id

-- Constᴿ is positive for sets.

Constᴿ-positive : @0 Is-set B → Positive (Constᴿ {a = a} B)
Constᴿ-positive {B} set = λ where
  .Positive.suitable → Constᴿ-suitable set

  .Positive.acts-on-functions → Constᴿ-acts-on-functions

  .Positive.reflexive-∥≡∥ᴱ → refl _

  .Positive.transitive-;ᴱ⁻¹ {R} {S} _ _ x z →
    _≃_.is-equivalence
      ((Constᴿ B R ;ᴱ Constᴿ B S) x z  ↔⟨⟩
       ∥ (∃ λ y → x ≡ y × y ≡ z) ∥ᴱ    ↝⟨ Eq.⇔→≃ T.truncation-is-proposition set _
                                            (λ x≡z → ∣ _ , x≡z , refl _ ∣) ⟩
       x ≡ z                           ↔⟨⟩
       Constᴿ B (R ;ᴱ S) x z           □)

  .Positive.commutes-with-/ᴱ {A = C} {R} prop equiv →
    _≃ᴱ_.is-equivalence $
    EEq.with-other-function
      (Const B C /ᴱ Constᴿ B R  ↔⟨⟩
       B /ᴱ _≡_                 ↔⟨ Q./ᴱ≡↔ set ⟩
       B                        ↔⟨⟩
       Const B (C /ᴱ R)         □)
      (/ᴱ→/ᴱ (Constᴿ B) (Constᴿ-suitable set) Constᴿ-acts-on-functions
         prop equiv)
      (Q.elim-prop λ @0 where
         .Q.is-propositionʳ _ → set
         .Q.[]ʳ _             → refl _)

------------------------------------------------------------------------
-- The Id and Idᴿ combinators, along with some properties

-- Identity structures.

Id : Structure a a
Id A = A

-- Relation transformers for Id.

Idᴿ : Relation-transformer-for (Id {a = a})
Idᴿ R = R

-- When is an equivalence structure-preserving for Id?

Is-Id-equivalence : Structure-preserving-equivalence-predicate Id a
Is-Id-equivalence (_ , x) (_ , y) eq = _≃ᴱ_.to eq x ≡ y

-- Id and Is-Id-equivalence are univalent.

Id-univalent : Univalent (Id {a = a}) Is-Id-equivalence
Id-univalent .Univalent.univalent {A = _ , x} {B = _ , y} eq =
  _≃ᴱ_.to eq x ≡ y                         ↝⟨ ≡⇒≃ $ cong (_≡ _) $ cong (λ eq → _≃_.to eq x) $ sym $
                                              _≃_.right-inverse-of (≡≃≃ univ) _ ⟩
  ≡⇒→ (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y       ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $
                                              subst-id-in-terms-of-≡⇒↝ equivalence ⟩□
  subst Id (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y  □

-- Idᴿ is suitable.

Idᴿ-suitable : Suitable (Idᴿ {a = a})
Idᴿ-suitable = λ where
  .Suitable.preserves-is-set         → id
  .Suitable.preserves-is-proposition → id
  .Suitable.symmetric _              → id
  .Suitable.transitive _ _ Rxy Syz   → ∣ _ , Rxy , Syz ∣
  .Suitable.descent _ _ _            →
    Contractibleᴱ-Erased-other-singleton

-- Idᴿ is univalent.

Idᴿ-univalent : Univalentᴿ (Idᴿ {a = a})
Idᴿ-univalent = Idᴿ-suitable , Id-univalent

-- Idᴿ acts on functions.

Idᴿ-acts-on-functions : Acts-on-functions (Idᴿ {a = a})
Idᴿ-acts-on-functions = λ where
  .Acts-on-functions.map       → id
  .Acts-on-functions.map-id    → refl _
  .Acts-on-functions.map-map f → f

-- Idᴿ is positive.

Idᴿ-positive : Positive (Idᴿ {a = a})
Idᴿ-positive = λ where
  .Positive.suitable → Idᴿ-suitable

  .Positive.acts-on-functions → Idᴿ-acts-on-functions

  .Positive.reflexive-∥≡∥ᴱ → ∣ refl _ ∣

  .Positive.transitive-;ᴱ⁻¹ {R} {S} R-prop S-prop x z →
    _≃_.is-equivalence $
    Eq.with-other-function
      ((Idᴿ R ;ᴱ Idᴿ S) x z  ↔⟨⟩
       (R ;ᴱ S) x z          ↔⟨⟩
       Idᴿ (R ;ᴱ S) x z      □)
      (Suitable.transitive-;ᴱ Idᴿ-suitable R-prop S-prop x z)
      (T.elim λ @0 where
         .T.truncation-is-propositionʳ _ →
           H-level.⇒≡ 1 T.truncation-is-proposition
         .T.∣∣ʳ _ →
           refl _)

  .Positive.commutes-with-/ᴱ {A} {R} prop equiv →
    _≃ᴱ_.is-equivalence $
    EEq.with-other-function
      (Id A /ᴱ Idᴿ R  ↔⟨⟩
       A /ᴱ R         ↔⟨⟩
       Id (A /ᴱ R)    □)
      (/ᴱ→/ᴱ Idᴿ Idᴿ-suitable Idᴿ-acts-on-functions prop equiv)
      (Q.elim-prop λ @0 where
         .Q.is-propositionʳ _ → Q./ᴱ-is-set
         .Q.[]ʳ _             → refl _)

------------------------------------------------------------------------
-- Combinators related to Cartesian products

-- Product structures.

Product : Structure a b → Structure a c → Structure a (b ⊔ c)
Product F G A = F A × G A

-- A combinator that, given relation transformers for F and G,
-- produces a relation transformer for Product F G.

Productᴿ :
  Relation-transformer-for F →
  Relation-transformer-for G →
  Relation-transformer-for (Product F G)
Productᴿ S T R = S R ×ᴾ T R

-- When is an equivalence structure-preserving for Product F G?

Is-Product-equivalence :
  Structure-preserving-equivalence-predicate F a →
  Structure-preserving-equivalence-predicate G b →
  Structure-preserving-equivalence-predicate (Product F G) (a ⊔ b)
Is-Product-equivalence Is-F-eq Is-G-eq (A , x₁ , x₂) (B , y₁ , y₂) eq =
  Is-F-eq (A , x₁) (B , y₁) eq ×
  Is-G-eq (A , x₂) (B , y₂) eq

-- If F and G are univalent, then Product F G is univalent.

Product-univalent :
  {@0 F : Structure a b}
  {@0 G : Structure a c}
  {@0 Is-F-eq : Structure-preserving-equivalence-predicate F d}
  {@0 Is-G-eq : Structure-preserving-equivalence-predicate G e} →
  @0 Univalent F Is-F-eq →
  @0 Univalent G Is-G-eq →
  Univalent (Product F G) (Is-Product-equivalence Is-F-eq Is-G-eq)
Product-univalent
  {F} {G} {Is-F-eq} {Is-G-eq}
  u-F u-G .Univalent.univalent {A = A , x₁ , x₂} {B = B , y₁ , y₂} eq =

  Is-F-eq (A , x₁) (B , y₁) eq × Is-G-eq (A , x₂) (B , y₂) eq         ↝⟨ u-F .Univalent.univalent eq
                                                                           ×-cong
                                                                         u-G .Univalent.univalent eq ⟩
  subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x₁ ≡ y₁ ×
  subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x₂ ≡ y₂                            ↔⟨ ≡×≡↔≡ ⟩

  ( subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x₁
  , subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x₂
  ) ≡ (y₁ , y₂)                                                       ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $
                                                                         push-subst-, _ _ ⟩□
  subst (Product F G) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (x₁ , x₂) ≡ (y₁ , y₂)  □

-- If S and T are suitable, then Productᴿ S T is suitable.

Productᴿ-suitable :
  {@0 S : Relation-transformer-for F}
  {@0 T : Relation-transformer-for G} →
  Suitable S →
  Suitable T →
  Suitable (Productᴿ S T)
Productᴿ-suitable {S} {T} s-S s-T = λ where
  .Suitable.preserves-is-set set →
    ×-closure 2
      (s-S .Suitable.preserves-is-set set)
      (s-T .Suitable.preserves-is-set set)

  .Suitable.preserves-is-proposition prop _ _ →
    ×-closure 1
      (s-S .Suitable.preserves-is-proposition prop _ _)
      (s-T .Suitable.preserves-is-proposition prop _ _)

  .Suitable.symmetric prop →
    Σ-map
      (s-S .Suitable.symmetric prop)
      (s-T .Suitable.symmetric prop)

  .Suitable.transitive prop₁ prop₂ →
    Σ-zip
      (s-S .Suitable.transitive prop₁ prop₂)
      (s-T .Suitable.transitive prop₁ prop₂)

  .Suitable.descent {x = x , y} {R} prop equiv (SRxx , Tryy) →           $⟨ [ SRxx ] , [ Tryy ] ⟩

    Erased (S R x x) × Erased (T R y y)                                  ↝⟨ Σ-map (λ ([ SRxx ]) → s-S .Suitable.descent prop equiv SRxx)
                                                                                  (λ ([ TRyy ]) → s-T .Suitable.descent prop equiv TRyy) ⟩
    Contractibleᴱ (∃ λ x′ → Erased (S (Graph [_]) x x′)) ×
    Contractibleᴱ (∃ λ y′ → Erased (T (Graph [_]) y y′))                 ↝⟨ uncurry ECP.Contractibleᴱ-× ⟩

    Contractibleᴱ
      ((∃ λ x′ → Erased (S (Graph [_]) x x′)) ×
       (∃ λ y′ → Erased (T (Graph [_]) y y′)))                           ↝⟨ ECP.Contractibleᴱ-cong _ $
                                                                            Σ-assoc F.∘
                                                                            (∃-cong λ _ → ∃-cong λ _ → inverse Erased-Σ↔Σ) F.∘
                                                                            (∃-cong λ _ → ∃-comm) F.∘
                                                                            inverse Σ-assoc ⟩□
    Contractibleᴱ (∃ λ p → Erased (Productᴿ S T (Graph [_]) (x , y) p))  □

-- If S and T are univalent, then Productᴿ S T is univalent.

Productᴿ-univalent :
  {@0 S : Relation-transformer-for F}
  {@0 T : Relation-transformer-for G} →
  Univalentᴿ S →
  Univalentᴿ T →
  Univalentᴿ (Productᴿ S T)
Productᴿ-univalent (s-S , u-S) (s-T , u-T) =
    Productᴿ-suitable s-S s-T
  , Product-univalent u-S u-T

-- If S and T act on functions, then Productᴿ S T acts on functions.

Productᴿ-acts-on-functions :
  {@0 S : Relation-transformer-for F}
  {@0 T : Relation-transformer-for G} →
  Acts-on-functions S →
  Acts-on-functions T →
  Acts-on-functions (Productᴿ S T)
Productᴿ-acts-on-functions {S} {T} a-S a-T = λ where
  .Acts-on-functions.map f →
    Σ-map (a-S .Acts-on-functions.map f)
          (a-T .Acts-on-functions.map f)

  .Acts-on-functions.map-id →
    Σ-map (a-S .Acts-on-functions.map id)
          (a-T .Acts-on-functions.map id)  ≡⟨ cong₂ (λ f g → Σ-map f g)
                                                (a-S .Acts-on-functions.map-id)
                                                (a-T .Acts-on-functions.map-id) ⟩
    Σ-map id id                            ≡⟨⟩

    id                                     ∎

  .Acts-on-functions.map-map
    {f} {g} {x = x₁ , x₂} {y = y₁ , y₂} {R₁} {R₂} R₁→R₂ →

    S R₁ x₁ y₁ × T R₁ x₂ y₂                   ↝⟨ a-S .Acts-on-functions.map-map R₁→R₂
                                                   ×-cong
                                                 a-T .Acts-on-functions.map-map R₁→R₂ ⟩□
    S R₂ (a-S .Acts-on-functions.map f x₁)
         (a-S .Acts-on-functions.map g y₁) ×
    T R₂ (a-T .Acts-on-functions.map f x₂)
         (a-T .Acts-on-functions.map g y₂)    □

-- If S and T are positive, then Productᴿ S T is positive.

Productᴿ-positive :
  {@0 S : Relation-transformer-for F}
  {@0 T : Relation-transformer-for G} →
  Positive S →
  Positive T →
  Positive (Productᴿ S T)
Productᴿ-positive {F} {G} {S} {T} p-S p-T = λ where
    .Positive.suitable → suitable

    .Positive.acts-on-functions → acts-on-functions

    .Positive.reflexive-∥≡∥ᴱ → SP.reflexive-∥≡∥ᴱ , TP.reflexive-∥≡∥ᴱ

    .Positive.transitive-;ᴱ⁻¹
      {R = R₁} {S = R₂} R₁-prop R₂-prop x@(x₁ , x₂) z@(z₁ , z₂) →

      _≃_.is-equivalence $
      Eq.with-other-function
        ((Productᴿ S T R₁ ;ᴱ Productᴿ S T R₂) x z     ↝⟨ lemma ⟩
         (S R₁ ;ᴱ S R₂) x₁ z₁ × (T R₁ ;ᴱ T R₂) x₂ z₂  ↝⟨ Eq.⟨ _ , SP.transitive-;ᴱ⁻¹ R₁-prop R₂-prop _ _ ⟩
                                                           ×-cong
                                                         Eq.⟨ _ , TP.transitive-;ᴱ⁻¹ R₁-prop R₂-prop _ _ ⟩ ⟩
         S (R₁ ;ᴱ R₂) x₁ z₁ × T (R₁ ;ᴱ R₂) x₂ z₂      ↔⟨⟩

         Productᴿ S T (R₁ ;ᴱ R₂) x z                  □)
        _
        (T.elim λ @0 where
           .T.truncation-is-propositionʳ _ →
             H-level.mono₁ 1 $
             ×-closure 1
               (SS.preserves-is-proposition
                  (λ _ _ → T.truncation-is-proposition) _ _)
               (TS.preserves-is-proposition
                  (λ _ _ → T.truncation-is-proposition) _ _)
           .T.∣∣ʳ _ →
             refl _)

    .Positive.commutes-with-/ᴱ {A} {R} prop equiv →
      _≃ᴱ_.is-equivalence $
      EEq.with-other-function
        (Product F G A /ᴱ Productᴿ S T R  ↔⟨⟩
         (F A × G A) /ᴱ Productᴿ S T R    ↔⟨ Q.×/ᴱ (SP.reflexive prop equiv _) (TP.reflexive prop equiv _) ⟩
         F A /ᴱ S R × G A /ᴱ T R          ↝⟨ EEq.⟨ _ , SP.commutes-with-/ᴱ prop equiv ⟩
                                               ×-cong
                                             EEq.⟨ _ , TP.commutes-with-/ᴱ prop equiv ⟩ ⟩
         F (A /ᴱ R) × G (A /ᴱ R)          ↔⟨⟩
         Product F G (A /ᴱ R)             □)
        _
        (Q.elim-prop λ @0 where
           .Q.is-propositionʳ _ →
             ×-closure 2
               (SS.preserves-is-set Q./ᴱ-is-set)
               (TS.preserves-is-set Q./ᴱ-is-set)
           .Q.[]ʳ _ → refl _)
  where
  module SP = Positive p-S
  module SS = Suitable SP.suitable
  module TP = Positive p-T
  module TS = Suitable TP.suitable

  suitable =
    Productᴿ-suitable
      SP.suitable
      TP.suitable

  acts-on-functions =
    Productᴿ-acts-on-functions
      SP.acts-on-functions
      TP.acts-on-functions

  @0 lemma :
    (Productᴿ S T R₁ ;ᴱ Productᴿ S T R₂) (x₁ , x₂) (z₁ , z₂) ≃
    ((S R₁ ;ᴱ S R₂) x₁ z₁ × (T R₁ ;ᴱ T R₂) x₂ z₂)
  lemma = Eq.⇔→≃
    T.truncation-is-proposition
    (×-closure 1
       T.truncation-is-proposition
       T.truncation-is-proposition)
    (T.rec λ @0 where
       .T.truncation-is-propositionʳ →
         ×-closure 1
           T.truncation-is-proposition
           T.truncation-is-proposition
       .T.∣∣ʳ (_ , (SR₁x₁y₁ , TR₁x₂y₂) , (SR₂y₁z₁ , TR₂y₂z₂)) →
           ∣ _ , SR₁x₁y₁ , SR₂y₁z₁ ∣
         , ∣ _ , TR₁x₂y₂ , TR₂y₂z₂ ∣)
    (uncurry $ T.rec λ @0 where
       .T.truncation-is-propositionʳ →
         Π-closure ext 1 λ _ →
         T.truncation-is-proposition
       .T.∣∣ʳ (_ , SR₁x₁y₁ , SR₂y₁z₁) →
         T.∥∥ᴱ-map
           λ (_ , TR₁x₂y₂ , TR₂y₂z₂) →
             _ , (SR₁x₁y₁ , TR₁x₂y₂) , (SR₂y₁z₁ , TR₂y₂z₂))

------------------------------------------------------------------------
-- Combinators related to Maybe

-- A combinator that, given a relation transformer for F, produces a
-- relation transformer for Maybe ∘ F.

Maybeᴿ :
  Relation-transformer-for F →
  Relation-transformer-for (Maybe ∘ F)
Maybeᴿ = Maybeᴾ ∘_

-- When is an equivalence structure-preserving for Maybe ∘ F?

Is-Maybe-equivalence :
  Structure-preserving-equivalence-predicate F a →
  Structure-preserving-equivalence-predicate (Maybe ∘ F) a
Is-Maybe-equivalence Is-F-eq = λ where
  (A , nothing) (B , nothing) eq → ↑ _ ⊤
  (A , just x)  (B , just y)  eq → Is-F-eq (A , x) (B , y) eq
  (A , _)       (B , _)       eq → ⊥

-- If F is univalent, then Maybe ∘ F is univalent.

Maybe-univalent :
  {@0 F : Structure a b}
  {@0 Is-F-eq : Structure-preserving-equivalence-predicate F c} →
  @0 Univalent F Is-F-eq →
  Univalent (Maybe ∘ F) (Is-Maybe-equivalence Is-F-eq)
Maybe-univalent
  {F} {Is-F-eq} u-F .Univalent.univalent {A = A , x} {B = B , y} =
  lemma x y
  where
  lemma :
    (x : Maybe (F A)) (y : Maybe (F B)) →
    (eq : A ≃ᴱ B) →
    Is-Maybe-equivalence Is-F-eq (A , x) (B , y) eq ≃
    (subst (Maybe ∘ F) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y)
  lemma nothing nothing eq =
    ↑ _ ⊤                                                         ↔⟨ B.↑↔ ⟩

    ⊤                                                             ↔⟨ inverse tt≡tt↔⊤ ⟩

    tt ≡ tt                                                       ↔⟨ B.≡↔inj₁≡inj₁ ⟩

    nothing ≡ nothing                                             ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $ push-subst-inj₁ _ _ ⟩□

    subst (Maybe ∘ F) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) nothing ≡ nothing  □

  lemma nothing (just y) eq =
    ⊥                                                            ↔⟨ ⊥↔⊥ ⟩
    ⊥                                                            ↔⟨ inverse B.≡↔⊎ ⟩
    nothing ≡ just y                                             ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $ push-subst-inj₁ _ _ ⟩□
    subst (Maybe ∘ F) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) nothing ≡ just y  □

  lemma (just x) nothing eq =
    ⊥                                                              ↔⟨ ⊥↔⊥ ⟩
    ⊥                                                              ↔⟨ inverse B.≡↔⊎ ⟩
    just _ ≡ nothing                                               ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $ push-subst-inj₂ _ _ ⟩□
    subst (Maybe ∘ F) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (just x) ≡ nothing  □

  lemma (just x) (just y) eq =
    Is-F-eq (A , x) (B , y) eq                                    ↝⟨ u-F .Univalent.univalent eq ⟩
    subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y                        ↔⟨ B.≡↔inj₂≡inj₂ ⟩
    just (subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x) ≡ just y            ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym $ push-subst-inj₂ _ _ ⟩□
    subst (Maybe ∘ F) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (just x) ≡ just y  □

-- If G is suitable, then Maybeᴿ G is suitable.

Maybeᴿ-suitable :
  {@0 G : Relation-transformer-for F} →
  Suitable G →
  Suitable (Maybeᴿ G)
Maybeᴿ-suitable {G} s-G = λ where
    .Suitable.preserves-is-set set →
      Maybe-closure 0 (S.preserves-is-set set)

    .Suitable.preserves-is-proposition prop → λ @0 where
      nothing nothing →
        H-level.mono₁ 0 $
        ↑-closure 0 ⊤-contractible

      nothing (just _) →
        ⊥-propositional

      (just _) nothing →
        ⊥-propositional

      (just x) (just y) →
        S.preserves-is-proposition prop x y

    .Suitable.symmetric {x = nothing} {y = nothing} → _
    .Suitable.symmetric {x = just x}  {y = just y}  → S.symmetric

    .Suitable.transitive {x = nothing} {y = nothing} {z = nothing} → _
    .Suitable.transitive {x = just _}  {y = just _}  {z = just _}  →
      S.transitive

    .Suitable.descent {x = nothing} {R} prop equiv _ →
        (nothing , [ _ ])
      , [ (λ @0 where
             (nothing , [ _ ]) → refl _)
        ]
    .Suitable.descent {x = just x} {R} prop equiv SRxx →
                                                                        $⟨ [ SRxx ] ⟩
      Erased (G R x x)                                                  ↝⟨ (λ ([ SRxx ]) → S.descent prop equiv SRxx) ⟩
      Contractibleᴱ (∃ λ y → Erased (G (Graph [_]) x y))                ↝⟨ ECP.Contractibleᴱ-cong _
                                                                             (Eq.↔→≃
                                                                                (Σ-map just id)
                                                                                (λ where
                                                                                   (nothing , [ () ])
                                                                                   (just y , s)       → y , s)
                                                                                (λ where
                                                                                   (nothing , [ () ])
                                                                                   (just _ , _)       → refl _)
                                                                                refl)
                                                                             ⦂ (_ → _) ⟩□
      Contractibleᴱ (∃ λ y → Erased (Maybeᴿ G (Graph [_]) (just x) y))  □
  where
  module S = Suitable s-G

-- If G is univalent, then Maybeᴿ G is univalent.

Maybeᴿ-univalent :
  {@0 G : Relation-transformer-for F} →
  Univalentᴿ G →
  Univalentᴿ (Maybeᴿ G)
Maybeᴿ-univalent {F} {G} (s-G , u-G) =
    Maybeᴿ-suitable s-G
  , (                                                              $⟨ Maybe-univalent u-G ⟩
     Univalent (Maybe ∘ F)
       (Is-Maybe-equivalence λ (A , x) (B , y) eq →
          G (Graph (_≃ᴱ_.to eq)) x y)                              ↝⟨ substᴱ (Univalent _)
                                                                        (⟨ext⟩ λ p → ⟨ext⟩ λ q → lemma (p .proj₂) (q .proj₂)) ⟩□
     Univalent (Maybe ∘ F)
       (λ (A , x) (B , y) eq → Maybeᴿ G (Graph (_≃ᴱ_.to eq)) x y)  □)
  where
  @0 lemma :
    ∀ x y →
    Is-Maybe-equivalence
      (λ (A , x) (B , y) eq → G (Graph (_≃ᴱ_.to eq)) x y)
      (A , x) (B , y) ≡
    (λ eq → Maybeᴿ G (Graph (_≃ᴱ_.to eq)) x y)
  lemma nothing  nothing  = refl _
  lemma nothing  (just _) = refl _
  lemma (just _) nothing  = refl _
  lemma (just _) (just _) = refl _

-- If G acts on functions, then Maybeᴿ G acts on functions.

Maybeᴿ-acts-on-functions :
  {@0 G : Relation-transformer-for F} →
  Acts-on-functions G →
  Acts-on-functions (Maybeᴿ G)
Maybeᴿ-acts-on-functions {G} a-G = λ where
    .Acts-on-functions.map f →
      Monad.map (A.map f)
    .Acts-on-functions.map-id →
      Monad.map (A.map id)  ≡⟨ cong Monad.map A.map-id ⟩
      Monad.map id          ≡⟨ ⟨ext⟩ Monad.map-id ⟩∎
      id                    ∎
    .Acts-on-functions.map-map {x = nothing} {y = nothing}      → _
    .Acts-on-functions.map-map {x = nothing} {y = just _}  _ ()
    .Acts-on-functions.map-map {x = just _}  {y = nothing} _ ()
    .Acts-on-functions.map-map {x = just _}  {y = just _}       →
      A.map-map
  where
  module A = Acts-on-functions a-G

-- If G is positive, then Maybeᴿ G is positive.

Maybeᴿ-positive :
  {@0 G : Relation-transformer-for F} →
  Positive G →
  Positive (Maybeᴿ G)
Maybeᴿ-positive {F} {G} p-G = λ where
    .Positive.suitable → suitable

    .Positive.acts-on-functions → acts-on-functions

    .Positive.reflexive-∥≡∥ᴱ {x = nothing} → _
    .Positive.reflexive-∥≡∥ᴱ {x = just _}  → SP.reflexive-∥≡∥ᴱ

    .Positive.transitive-;ᴱ⁻¹ R₁-prop R₂-prop x z →
      _≃_.is-equivalence $
      Eq.with-other-function
        (lemma R₁-prop R₂-prop x z .proj₁)
        _
        (lemma R₁-prop R₂-prop x z .proj₂)

    .Positive.commutes-with-/ᴱ {A} {R} prop equiv →
      _≃ᴱ_.is-equivalence $
      EEq.with-other-function
        (Maybe (F A) /ᴱ Maybeᴿ G R  ↔⟨ Q.Maybe/ᴱ ⟩
         Maybe (F A /ᴱ G R)         ↝⟨ F.id ⊎-cong EEq.⟨ _ , SP.commutes-with-/ᴱ prop equiv ⟩ ⟩□
         Maybe (F (A /ᴱ R))         □)
        (/ᴱ→/ᴱ (Maybeᴿ G) suitable acts-on-functions prop equiv)
        (Q.elim-prop λ @0 where
           .Q.is-propositionʳ _ →
             Maybe-closure 0 (SS.preserves-is-set Q./ᴱ-is-set)
           .Q.[]ʳ nothing  → refl _
           .Q.[]ʳ (just _) → refl _)
  where
  module SP = Positive p-G
  module SS = Suitable SP.suitable

  suitable          = Maybeᴿ-suitable SP.suitable
  acts-on-functions = Maybeᴿ-acts-on-functions SP.acts-on-functions

  @0 lemma :
    (R₁-prop : ∀ x y → Is-proposition (R₁ x y)) →
    (R₂-prop : ∀ x y → Is-proposition (R₂ x y)) →
    ∀ x z →
    ∃ λ (eq : (Maybeᴿ G R₁ ;ᴱ Maybeᴿ G R₂) x z ≃
              Maybeᴿ G (R₁ ;ᴱ R₂) x z) →
      ∀ p →
      _≃_.to eq p ≡
      Suitable.transitive-;ᴱ suitable R₁-prop R₂-prop x z p
  lemma {R₁} {R₂} R₁-prop R₂-prop = λ @0 where
    nothing nothing →
        ((Maybeᴿ G R₁ ;ᴱ Maybeᴿ G R₂) nothing nothing  ↝⟨ Eq.⇔→≃
                                                            T.truncation-is-proposition
                                                            (H-level.mono₁ 0 $ ↑-closure 0 ⊤-contractible)
                                                            _
                                                            (λ _ → ∣ nothing , _ ∣) ⟩□
         ↑ _ ⊤                                         □)
      , (λ _ → refl _)

    nothing (just z) →
        ((Maybeᴿ G R₁ ;ᴱ Maybeᴿ G R₂) nothing (just z)  ↝⟨ Eq.⇔→≃
                                                             T.truncation-is-proposition
                                                             ⊥-propositional
                                                             (T.rec λ @0 where
                                                                .T.truncation-is-propositionʳ →
                                                                  ⊥-propositional
                                                                .T.∣∣ʳ (nothing , _ , ())
                                                                .T.∣∣ʳ (just _ , () , _))
                                                             ⊥-elim ⟩□
         ⊥                                              □)
      , (T.elim λ @0 where
           .T.truncation-is-propositionʳ _ →
             H-level.⇒≡ 1 $
             ⊥-propositional
           .T.∣∣ʳ (nothing , _ , ())
           .T.∣∣ʳ (just _ , () , _))

    (just x) nothing →
         ((Maybeᴿ G R₁ ;ᴱ Maybeᴿ G R₂) (just x) nothing  ↝⟨ Eq.⇔→≃
                                                              T.truncation-is-proposition
                                                              ⊥-propositional
                                                              (T.rec λ @0 where
                                                                 .T.truncation-is-propositionʳ →
                                                                   ⊥-propositional
                                                                 .T.∣∣ʳ (nothing , () , _)
                                                                 .T.∣∣ʳ (just _ , _ , ()))
                                                              ⊥-elim ⟩□
          ⊥                                              □)
      , (T.elim λ @0 where
           .T.truncation-is-propositionʳ _ →
             H-level.⇒≡ 1 $
             ⊥-propositional
           .T.∣∣ʳ (nothing , () , _)
           .T.∣∣ʳ (just _ , _ , ()))

    (just x) (just z) →
        ((Maybeᴿ G R₁ ;ᴱ Maybeᴿ G R₂) (just x) (just z)  ↝⟨ Eq.⇔→≃
                                                             T.truncation-is-proposition
                                                             T.truncation-is-proposition
                                                             (T.∥∥ᴱ-map λ where
                                                                (nothing , () , ())
                                                                (just _ , p)        → _ , p)
                                                             (T.∥∥ᴱ-map (Σ-map just id)) ⟩
         (G R₁ ;ᴱ G R₂) x z                              ↝⟨ Eq.⟨ _ , SP.transitive-;ᴱ⁻¹ R₁-prop R₂-prop _ _ ⟩ ⟩□
         G (R₁ ;ᴱ R₂) x z                                □)
      , (T.elim λ @0 where
           .T.truncation-is-propositionʳ _ →
             H-level.⇒≡ 1 $
             SS.preserves-is-proposition
               (λ _ _ → T.truncation-is-proposition) _ _
           .T.∣∣ʳ (nothing , () , ())
           .T.∣∣ʳ (just _ , _)        → refl _)

------------------------------------------------------------------------
-- The Function and Functionᴿ combinators, along with some properties

-- Function structures.

Function : Structure a b → Structure a c → Structure a (b ⊔ c)
Function F G A = F A → G A

-- A combinator that, given relation transformers for F and G,
-- produces a relation transformer for Function F G.

Functionᴿ :
  {F : Structure a b}
  {G : Structure a c} →
  Relation-transformer-for F →
  Relation-transformer-for G →
  Relation-transformer-for (Function F G)
Functionᴿ S T R f g = ∀ {x y} → S R x y → T R (f x) (g y)

-- A variant of Functionᴿ ∘ Constᴿ.

Function-Constᴿ :
  {F : Structure b c}
  (A : Type a) →
  Relation-transformer-for F →
  Relation-transformer-for (Function (Const A) F)
Function-Constᴿ A G R f g = (x : A) → G R (f x) (g x)

-- Function-Constᴿ is pointwise equivalent to Functionᴿ ∘ Constᴿ.

Function-Constᴿ≃Functionᴿ∘Constᴿ :
  {f : A → F B} {g : A → F C}
  (G : Relation-transformer-for F) →
  Function-Constᴿ A G R f g ≃
  (Functionᴿ ∘ Constᴿ) A G R f g
Function-Constᴿ≃Functionᴿ∘Constᴿ {R} {f} {g} G =
  (∀ x → G R (f x) (g x))              ↝⟨ (∀-cong ext λ _ → ∀-intro _ ext) ⟩
  (∀ x y → x ≡ y → G R (f x) (g y))    ↔⟨ inverse (∀-cong ext (λ _ → B.implicit-Π↔Π) F.∘ B.implicit-Π↔Π) ⟩□
  (∀ {x y} → x ≡ y → G R (f x) (g y))  □

-- When is an equivalence structure-preserving for Function F G?

Is-Function-equivalence :
  {F : Structure a b} →
  Structure-preserving-equivalence-predicate F c →
  Structure-preserving-equivalence-predicate G d →
  Structure-preserving-equivalence-predicate (Function F G) (b ⊔ c ⊔ d)
Is-Function-equivalence Is-F-eq Is-G-eq (A , f) (B , g) eq =
  ∀ {x y} → Is-F-eq (A , x) (B , y) eq → Is-G-eq (A , f x) (B , g y) eq

-- A variant of Is-Function-equivalence.

Is-Function-equivalence′ :
  {F : Structure a b} →
  (∀ {A B} → A ≃ᴱ B → F A ≃ᴱ F B) →
  Structure-preserving-equivalence-predicate G c →
  Structure-preserving-equivalence-predicate (Function F G) (b ⊔ c)
Is-Function-equivalence′ F-cong Is-G-eq (A , f) (B , g) eq =
  ∀ x → Is-G-eq (A , f x) (B , g (_≃ᴱ_.to (F-cong eq) x)) eq

-- If F and G are univalent, then Function F G is univalent.

Function-univalent :
  {@0 F : Structure a b}
  {@0 G : Structure a c}
  {@0 Is-F-eq : Structure-preserving-equivalence-predicate F d}
  {@0 Is-G-eq : Structure-preserving-equivalence-predicate G e} →
  @0 Univalent F Is-F-eq →
  @0 Univalent G Is-G-eq →
  Univalent (Function F G) (Is-Function-equivalence Is-F-eq Is-G-eq)
Function-univalent
  {F} {G} {Is-F-eq} {Is-G-eq}
  u-F u-G .Univalent.univalent
  {A = A , f} {B = B , g} eq =

  (∀ {x y} → Is-F-eq (A , x) (B , y) eq →
   Is-G-eq (A , f x) (B , g y) eq)                                 ↔⟨ B.implicit-Π↔Π F.∘
                                                                      implicit-∀-cong ext B.implicit-Π↔Π ⟩
  (∀ x y → Is-F-eq (A , x) (B , y) eq →
   Is-G-eq (A , f x) (B , g y) eq)                                 ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                       →-cong ext (u-F .Univalent.univalent eq) (u-G .Univalent.univalent eq)) ⟩
  (∀ x y → subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y →
   subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (f x) ≡ g y)                   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext $
                                                                       ≡⇒≃ (cong (_ ≡_) $ _≃_.left-inverse-of (Eq.subst-as-equivalence _ _) _) F.∘
                                                                       inverse (Eq.≃-≡ $ inverse $ Eq.subst-as-equivalence _ _) F.∘
                                                                       from-bijection ≡-comm) ⟩
  (∀ x y → subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) y ≡ x →
   subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (f x) ≡ g y)                   ↔⟨ Π-comm ⟩

  (∀ y x → subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) y ≡ x →
   subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (f x) ≡ g y)                   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ eq →
                                                                       ≡⇒≃ $ cong (_≡ _) $ cong (subst G _) $ cong f $ sym eq) ⟩
  (∀ y x → subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) y ≡ x →
   subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))
     (f (subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) y)) ≡
   g y)                                                            ↝⟨ (∀-cong ext λ _ → inverse $
                                                                       ∀-intro _ ext) ⟩
  (∀ y →
   subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))
     (f (subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) y)) ≡
   g y)                                                            ↝⟨ (∀-cong ext λ _ → ≡⇒≃ $ cong (_≡ _) $ sym $
                                                                       subst-→) ⟩

  (∀ y → subst (Function F G) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) f y ≡ g y)  ↝⟨ Eq.extensionality-isomorphism ext ⟩□

  subst (Function F G) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) f ≡ g              □

-- A variant of Function-univalent that is stated using
-- Is-Function-equivalence′ instead of Is-Function-equivalence.

Function-univalent′ :
  {@0 G : Structure a c}
  {@0 Is-G-eq : Structure-preserving-equivalence-predicate G e}
  (@0 F-cong : ∀ {A B} → A ≃ᴱ B → F A ≃ᴱ F B) →
  @0 (∀ {A} (x : F A) → _≃ᴱ_.to (F-cong F.id) x ≡ x) →
  @0 Univalent G Is-G-eq →
  Univalent (Function F G) (Is-Function-equivalence′ F-cong Is-G-eq)
Function-univalent′
  {F} {G} {Is-G-eq}
  F-cong F-cong-id u-G .Univalent.univalent
  {A = A , f} {B = B , g} eq =

  (∀ x → Is-G-eq (A , f x) (B , g (_≃ᴱ_.to (F-cong eq) x)) eq)          ↝⟨ (∀-cong ext λ _ → u-G .Univalent.univalent eq) ⟩

  (∀ x →
   subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) (f x) ≡ g (_≃ᴱ_.to (F-cong eq) x))  ↝⟨ Eq.extensionality-isomorphism ext ⟩

  subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ≡ g ∘ _≃ᴱ_.to (F-cong eq)        ↝⟨ ≡⇒≃ $ cong (subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ≡_) $
                                                                           cong (g ∘_) $ cong _≃ᴱ_.to $ cong F-cong $ sym $
                                                                           _≃_.right-inverse-of EEq.≃≃≃ᴱ _ ⟩
  subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ≡
  g ∘ _≃ᴱ_.to (F-cong $ EEq.≃→≃ᴱ $ EEq.≃ᴱ→≃ eq)                         ↝⟨ ≡⇒≃ $ cong (subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ≡_) $
                                                                           cong (g ∘_) $ ⟨ext⟩ $
                                                                           transport-theorem
                                                                             F (_≃ᴱ_.to ∘ F-cong ∘ EEq.≃→≃ᴱ) F-cong-id univ (EEq.≃ᴱ→≃ eq) ⟩
  subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ≡
  g ∘ subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))                                  ↝⟨ inverse $ Eq.≃-≡ $ →-cong₁ ext $ Eq.subst-as-equivalence _ _ ⟩

  subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ∘
  subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) ≡
  g ∘ subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘
  subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)))                                ↝⟨ ≡⇒≃ $ cong (subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ∘
                                                                                       subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) ≡_) $
                                                                           cong (g ∘_) $ ⟨ext⟩ $
                                                                           _≃_.right-inverse-of (Eq.subst-as-equivalence _ _) ⟩
  subst G (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) ∘ f ∘
  subst F (sym (≃⇒≡ univ (EEq.≃ᴱ→≃ eq))) ≡
  g                                                                     ↝⟨ (≡⇒≃ $ cong (_≡ _) $ sym $ ⟨ext⟩ λ _ →
                                                                            subst-→) ⟩□
  subst (Function F G) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) f ≡ g                   □

-- If S is positive and T is suitable, then Functionᴿ S T is suitable.
--
-- This is a variant of Theorem 5.12 from "Internalizing
-- Representation Independence with Univalence".

Functionᴿ-suitable :
  {@0 S : Relation-transformer-for F} →
  {@0 T : Relation-transformer-for G} →
  Positive S →
  Suitable T →
  Suitable (Functionᴿ S T)
Functionᴿ-suitable {F} {G} {S} {T} p-S s-T = λ where
    .Suitable.preserves-is-set set →
      Π-closure ext 2 λ _ →
      TS.preserves-is-set set

    .Suitable.preserves-is-proposition prop _ _ →
      implicit-Π-closure ext 1 λ _ →
      implicit-Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      TS.preserves-is-proposition prop _ _

    .Suitable.symmetric {R} {x = f} {y = g} prop S→T {x} {y} →
      S (R ⁻¹) x y          ↝⟨ SS.symmetric (flip prop) ⟩
      S R y x               ↝⟨ S→T ⟩
      T R (f y) (g x)       ↝⟨ TS.symmetric prop ⟩□
      T (R ⁻¹) (g x) (f y)  □

    .Suitable.transitive
      {R = R₁} {S = R₂} {x = f} {y = g} {z = h}
      R₁-prop R₂-prop S→T₁ S→T₂ {x} {y} →

      S (R₁ ;ᴱ R₂) x y            ↔⟨ inverse Eq.⟨ _ , SP.transitive-;ᴱ⁻¹ R₁-prop R₂-prop _ _ ⟩ ⟩
      (S R₁ ;ᴱ S R₂) x y          ↝⟨ T.∥∥ᴱ-map (Σ-map _ (Σ-map S→T₁ S→T₂)) ⟩
      (T R₁ ;ᴱ T R₂) (f x) (h y)  ↝⟨ TS.transitive-;ᴱ R₁-prop R₂-prop _ _ ⟩□
      T (R₁ ;ᴱ R₂) (f x) (h y)    □

    .Suitable.descent {A} {x = f} {R} prop equiv S→T →
      let
        d :
          (x : F A) →
          Contractibleᴱ (∃ λ y → Erased (T (Graph [_]) (f x) y))
        d x = TS.descent prop equiv (S→T (SP.reflexive prop equiv x))

        g-[] : F A → G (A /ᴱ R)
        g-[] x = d x .proj₁ .proj₁

        S→T′ : Erased (S R x y → T (Graph [_]) (f x) (g-[] y))
        S→T′ = λ {x = x} {y = y} →
          [ S R x y                            ↝⟨ S→T ⟩
            T R (f x) (f y)                    ↝⟨ flip (TS.transitive prop (λ _ _ → Q./ᴱ-is-set)) (d y .proj₁ .proj₂ .erased) ⟩
            T (R ;ᴱ Graph [_]) (f x) (g-[] y)  ↝⟨ subst (λ R → T R (f x) (g-[] y)) (;ᴱ-Graph-[]≡Graph-[] prop equiv) ⟩□
            T (Graph [_]) (f x) (g-[] y)       □
          ]

        S-[]-map-[] : ∀ {x} → Erased (S (Graph [_]) x (SA.map [_] x))
        S-[]-map-[] = λ {x = x} →
          [                                             $⟨ SA.map-map Q.[]-respects-relation (SP.reflexive prop equiv x) ⟩
            S (Graph [_]) (SA.map id x) (SA.map [_] x)  ↝⟨ subst (λ f → S (Graph (Q.[_] {R = R})) (f x) (SA.map Q.[_] x)) SA.map-id ⟩□
            S (Graph [_]) x (SA.map [_] x)              □
          ]

        g : F A /ᴱ S R → G (A /ᴱ R)
        g = Q.rec λ where
          .Q.is-setʳ → TS.preserves-is-set Q./ᴱ-is-set

          .Q.[]ʳ → g-[]

          .Q.[]-respects-relationʳ {x} {y} SRxy →
            g-[] x  ≡⟨ cong proj₁ $
                       d x .proj₂ .erased
                         (g-[] y , Er.map (_$ SRxy) S→T′) ⟩∎
            g-[] y  ∎

        h : F A /ᴱ S R ≃ᴱ F (A /ᴱ R)
        h = EEq.⟨ _ , SP.commutes-with-/ᴱ prop equiv ⟩
      in
        ( (F (A /ᴱ R)  ↝⟨ _≃ᴱ_.from h ⟩
           F A /ᴱ S R  ↝⟨ g ⟩□
           G (A /ᴱ R)  □)
        , [ (λ {x = x} {y = y} →
               let
                 lemma :
                   ∀ y →
                   S (Graph [_]) x (_≃ᴱ_.to h y) →
                   T (Graph [_]) (f x) (g y)
                 lemma = Q.elim-prop λ @0 where
                   .Q.is-propositionʳ _ →
                     Π-closure ext 1 λ _ →
                     TS.preserves-is-proposition
                       (λ _ _ → Q./ᴱ-is-set) _ _
                   .Q.[]ʳ y →
                     let
                       s =                                  $⟨ S-[]-map-[] .erased ⟩
                         S (Graph [_]) y (SA.map [_] y)     ↝⟨ SS.symmetric (λ _ _ → Q./ᴱ-is-set) ⟩□
                         S (Graph [_] ⁻¹) (SA.map [_] y) y  □
                     in
                     S (Graph [_]) x (SA.map [_] y)    ↝⟨ flip (SS.transitive (λ _ _ → Q./ᴱ-is-set) λ _ _ → Q./ᴱ-is-set) s ⟩
                     S (Graph [_] ⟵) x y               ↝⟨ subst (λ R → S R x y) (Graph-[]-⟵≡ prop equiv) ⟩
                     S R x y                           ↝⟨ S→T′ .erased ⟩□
                     T (Graph [_]) (f x) (g-[] y)      □
               in
               S (Graph [_]) x y                            ↝⟨ subst (S (Graph [_]) x) (sym $ _≃ᴱ_.right-inverse-of h _) ⟩
               S (Graph [_]) x (_≃ᴱ_.to h (_≃ᴱ_.from h y))  ↝⟨ lemma (_≃ᴱ_.from h y) ⟩□
               T (Graph [_]) (f x) (g (_≃ᴱ_.from h y))      □)
          ]
        )
      , [ (λ (g′ , [ g′-hyp ]) →
             let
               lemma : ∀ y → g y ≡ g′ (_≃ᴱ_.to h y)
               lemma = Q.elim-prop λ @0 where
                 .Q.is-propositionʳ _ →
                   TS.preserves-is-set Q./ᴱ-is-set
                 .Q.[]ʳ y →
                   g-[] y                                     ≡⟨ cong proj₁ $
                                                                 d y .proj₂ .erased
                                                                   ( g′ (SA.map [_] y)
                                                                   , [
                                                                       $⟨ S-[]-map-[] .erased ⟩
                     S (Graph [_]) y (SA.map [_] y)                    ↝⟨ g′-hyp ⟩□
                     T (Graph [_]) (f y) (g′ (SA.map [_] y))           □
                                                                     ]
                                                                   ) ⟩∎
                   g′ (SA.map [_] y)                          ∎
             in
             Σ-≡,≡→≡
               (⟨ext⟩ λ x →
                g (_≃ᴱ_.from h x)               ≡⟨ lemma (_≃ᴱ_.from h x) ⟩
                g′ (_≃ᴱ_.to h (_≃ᴱ_.from h x))  ≡⟨ cong g′ $ _≃ᴱ_.right-inverse-of h _ ⟩∎
                g′ x                            ∎)
               (H-level-Erased 1
                  (implicit-Π-closure ext 1 λ _ →
                   implicit-Π-closure ext 1 λ _ →
                   Π-closure ext 1 λ _ →
                   TS.preserves-is-proposition (λ _ _ → Q./ᴱ-is-set) _ _)
                  _ _))
        ]
  where
  module SP = Positive p-S
  module SA = Acts-on-functions SP.acts-on-functions
  module SS = Suitable SP.suitable
  module TS = Suitable s-T

-- If A is a set and G is suitable, then Function-Constᴿ A G is
-- suitable.

Function-Constᴿ-suitable :
  {@0 G : Relation-transformer-for F} →
  @0 Is-set A →
  Suitable G →
  Suitable (Function-Constᴿ A G)
Function-Constᴿ-suitable {F} {A} {G} set =
  Suitable G                         ↝⟨ Functionᴿ-suitable (Constᴿ-positive set) ⟩
  Suitable (Functionᴿ (Constᴿ A) G)  ↝⟨ Suitable-map (inverse $ Function-Constᴿ≃Functionᴿ∘Constᴿ G) ⟩□
  Suitable (Function-Constᴿ A G)     □

-- If S is positive and univalent, and T is univalent, then
-- Functionᴿ S T is univalent.

Functionᴿ-univalent :
  {@0 S : Relation-transformer-for F}
  {@0 T : Relation-transformer-for G} →
  Positive S →
  Univalentᴿ S →
  Univalentᴿ T →
  Univalentᴿ (Functionᴿ S T)
Functionᴿ-univalent p-S (_ , u-S) (s-T , u-T) =
    Functionᴿ-suitable p-S s-T
  , Function-univalent u-S u-T

-- If A is a set and G is univalent, then Function-Constᴿ A G is
-- univalent.

Function-Constᴿ-univalent :
  {@0 G : Relation-transformer-for F} →
  @0 Is-set A →
  Univalentᴿ G →
  Univalentᴿ (Function-Constᴿ A G)
Function-Constᴿ-univalent set (s-G , u-G) =
    Function-Constᴿ-suitable set s-G
  , Function-univalent′ (λ _ → F.id) refl u-G

------------------------------------------------------------------------
-- Combinators related to Erased

-- A combinator that, given a relation transformer for F, produces a
-- relation transformer for λ A → Erased (F A).
--
-- Note that I have not proved that Erasedᴿ G is positive if G is
-- positive.

Erasedᴿ :
  {@0 F : Structure a b} →
  @0 Relation-transformer-for F →
  Relation-transformer-for (λ A → Erased (F A))
Erasedᴿ G R = Erasedᴾ (G R)

-- When is an equivalence structure-preserving for λ A → Erased (F A)?

Is-Erased-equivalence :
  @0 Structure-preserving-equivalence-predicate F a →
  Structure-preserving-equivalence-predicate (λ A → Erased (F A)) a
Is-Erased-equivalence Is-F-eq (_ , x) (_ , y) eq =
  Erased (Is-F-eq (_ , erased x) (_ , erased y) eq)

-- If F is univalent, then λ A → Erased (F A) is univalent.

Erased-univalent :
  {@0 F : Structure a b}
  {@0 Is-F-eq : Structure-preserving-equivalence-predicate F c} →
  @0 Univalent F Is-F-eq →
  Univalent (λ A → Erased (F A)) (Is-Erased-equivalence Is-F-eq)
Erased-univalent
  {F} {Is-F-eq} u-F .Univalent.univalent
  {A = A , [ x ]} {B = B , [ y ]} eq =

  Erased (Is-F-eq (A , x) (B , y) eq)                                ↝⟨ Erased-cong (u-F .Univalent.univalent eq) ⟩

  Erased (subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ≡ y)                    ↔⟨ Erased-≡↔[]≡[] ⟩

  [ subst F (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) x ] ≡ [ y ]                     ↝⟨ ≡⇒≃ $ cong (_≡ _) $ sym push-subst-[] ⟩□

  subst (λ A → Erased (F A)) (≃⇒≡ univ (EEq.≃ᴱ→≃ eq)) [ x ] ≡ [ y ]  □

-- If G is suitable, then Erasedᴿ G is suitable.

Erasedᴿ-suitable :
  {@0 G : Relation-transformer-for F} →
  @0 Suitable G →
  Suitable (Erasedᴿ G)
Erasedᴿ-suitable {G} s-G = λ where
  .Suitable.preserves-is-set set →
    H-level-Erased 2 (s-G .Suitable.preserves-is-set set)

  .Suitable.preserves-is-proposition prop _ _ →
    H-level-Erased 1 (s-G .Suitable.preserves-is-proposition prop _ _)

  .Suitable.symmetric prop →
    Er.map (s-G .Suitable.symmetric prop)

  .Suitable.transitive R-prop S-prop [ GRxy ] [ GSyz ] →
    [ s-G .Suitable.transitive R-prop S-prop GRxy GSyz ]

  .Suitable.descent {x = [ x ]} {R} prop equiv [GRxx] →                $⟨ [ [GRxx] .erased ] ⟩
    Erased (G R x x)                                                   ↝⟨ Er.map (λ GRxx → s-G .Suitable.descent prop equiv GRxx) ⟩
    Erased (Contractibleᴱ (∃ λ y → Erased (G (Graph [_]) x y)))        ↝⟨ ECP.Erased-Contractibleᴱ↔Contractibleᴱ-Erased _ ⟩
    Contractibleᴱ (Erased (∃ λ y → Erased (G (Graph [_]) x y)))        ↝⟨ ECP.Contractibleᴱ-cong _ Erased-Σ↔Σ ⟩
    Contractibleᴱ (∃ λ ([ y ]) → Erased (Erased (G (Graph [_]) x y)))  ↔⟨⟩
    Contractibleᴱ (∃ λ y → Erased (Erasedᴿ G (Graph [_]) [ x ] y))     □

-- If G is univalent, then Erasedᴿ G is univalent.

Erasedᴿ-univalent :
  {@0 G : Relation-transformer-for F} →
  @0 Univalentᴿ G →
  Univalentᴿ (Erasedᴿ G)
Erasedᴿ-univalent (s-G , u-G) =
    Erasedᴿ-suitable s-G
  , Erased-univalent u-G

-- If G acts on functions, then Erasedᴿ G acts on functions.

Erasedᴿ-acts-on-functions :
  {@0 G : Relation-transformer-for F} →
  @0 Acts-on-functions G →
  Acts-on-functions (Erasedᴿ G)
Erasedᴿ-acts-on-functions {G} a-G = λ where
  .Acts-on-functions.map f →
    Er.map (a-G .Acts-on-functions.map f)
  .Acts-on-functions.map-id →
    Er.map (a-G .Acts-on-functions.map id)  ≡⟨ cong (λ f → Er.map f) (a-G .Acts-on-functions.map-id) ⟩
    Er.map id                               ≡⟨ (⟨ext⟩ λ _ → Er.map-id) ⟩
    id                                      ∎
  .Acts-on-functions.map-map
    {f} {g} {x = [ x ]} {y = [ y ]} {R₁} {R₂} R₁→R₂ →

    Erased (G R₁ x y)                               ↝⟨ Er.map (a-G .Acts-on-functions.map-map R₁→R₂) ⟩□

    Erased (G R₂ (a-G .Acts-on-functions.map f x)
                 (a-G .Acts-on-functions.map g y))  □

------------------------------------------------------------------------
-- An example: monoids

-- This is a variant of Examples 3.5 and 3.6 from "Internalizing
-- Representation Independence with Univalence".

module Example₁ where

  -- Raw monoid structures.

  Raw-monoid-structure : Structure a a
  Raw-monoid-structure A = A × (A → A → A)

  -- Raw-monoid-structure can be expressed using some combinators.

  _ :
    Raw-monoid-structure {a = a} ≡
    Product Id (Function Id (Function Id Id))
  _ = refl _

  -- Raw monoids, i.e., monoids without the monoid laws.

  Raw-monoid : (a : Level) → Type (lsuc a)
  Raw-monoid _ = Type-with Raw-monoid-structure

  -- Raw monoid equivalence predicates.

  Is-raw-monoid-equivalence :
    Structure-preserving-equivalence-predicate Raw-monoid-structure a
  Is-raw-monoid-equivalence (_ , id₁ , _∘₁_) (_ , id₂ , _∘₂_) eq =
    _≃ᴱ_.to eq id₁ ≡ id₂ ×
    (∀ x y → _≃ᴱ_.to eq (x ∘₁ y) ≡ _≃ᴱ_.to eq x ∘₂ _≃ᴱ_.to eq y)

  -- Is-raw-monoid-equivalence can be expressed using some
  -- combinators.

  _ :
    Is-raw-monoid-equivalence {a = a} ≡
    Is-Product-equivalence
      Is-Id-equivalence
      (Is-Function-equivalence′ id
         (Is-Function-equivalence′ id
            Is-Id-equivalence))
  _ = refl _

  -- Raw monoid equivalences (with erased proofs).

  infix 4 _≃ᴿᴹᴱ_

  _≃ᴿᴹᴱ_ : Raw-monoid a → Raw-monoid a → Type a
  _≃ᴿᴹᴱ_ = _≃[ Is-raw-monoid-equivalence ]ᴱ_

  -- The combination of Raw-monoid-structure and
  -- Is-raw-monoid-equivalence is univalent (in erased settings).

  Is-raw-monoid-equivalence-univalent :
    Univalent (Raw-monoid-structure {a = a}) Is-raw-monoid-equivalence
  Is-raw-monoid-equivalence-univalent =
    Product-univalent
      Id-univalent
      (Function-univalent′ id refl
         (Function-univalent′ id refl
            Id-univalent))

  -- The monoid laws.

  Monoid-laws : Axioms Raw-monoid-structure a
  Monoid-laws (A , id , _∘_) =
    Is-set A ×
    (∀ x → id ∘ x ≡ x) ×
    (∀ x → x ∘ id ≡ x) ×
    (∀ x y z → x ∘ (y ∘ z) ≡ (x ∘ y) ∘ z)

  -- The monoid laws are propositional.

  Monoid-laws-propositional :
    (M : Raw-monoid a) → Is-proposition (Monoid-laws M)
  Monoid-laws-propositional (A , id , _∘_) =
    Σ-closure 1 (H-level-propositional ext 2) λ A-set →
    ×-closure 1 (Π-closure ext 1 λ _ → A-set) $
    ×-closure 1 (Π-closure ext 1 λ _ → A-set) $
    Π-closure ext 1 λ _ → Π-closure ext 1 λ _ → Π-closure ext 1 λ _ →
    A-set

  -- Monoid structures.

  Monoid-structure : Structure a a
  Monoid-structure =
    Raw-monoid-structure With-the-axioms Monoid-laws

  -- Monoids.

  Monoid : (a : Level) → Type (lsuc a)
  Monoid _ = Type-with Monoid-structure

  -- Monoid equivalence predicates.

  Is-monoid-equivalence :
    Structure-preserving-equivalence-predicate Monoid-structure a
  Is-monoid-equivalence = Lift-With-the-axioms Is-raw-monoid-equivalence

  -- Monoid equivalences (with erased proofs).

  infix 4 _≃ᴹᴱ_

  _≃ᴹᴱ_ : Monoid a → Monoid a → Type a
  _≃ᴹᴱ_ = _≃[ Is-monoid-equivalence ]ᴱ_

  -- The combination of Monoid-structure and Is-monoid-equivalence is
  -- univalent (in erased settings).

  Is-monoid-equivalence-univalent :
    Univalent (Monoid-structure {a = a}) Is-monoid-equivalence
  Is-monoid-equivalence-univalent =
    Univalent-With-the-axioms
      Monoid-laws-propositional
      Is-raw-monoid-equivalence-univalent

  -- The structure identity principle for monoids.

  @0 sip-for-monoids : (M ≃ᴹᴱ N) ≃ (M ≡ N)
  sip-for-monoids = sip Is-monoid-equivalence-univalent

  -- If a raw monoid M₂ is equivalent (with erased proofs) to the
  -- underlying raw monoid of a monoid M₁, then the monoid laws hold
  -- for M₂ (in erased contexts), and M₁ is equivalent (with erased
  -- proofs) to the monoid constructed from M₂ and the laws.

  induced-monoid :
    (M₁@(A₁ , ops₁ , _) : Monoid a)
    (M₂@(A₂ , ops₂) : Raw-monoid a) →
    (A₁ , ops₁) ≃ᴿᴹᴱ M₂ →
    ∃ λ (l₂ : Erased (Monoid-laws M₂)) → M₁ ≃ᴹᴱ (A₂ , ops₂ , l₂)
  induced-monoid =
    induced-structures Is-raw-monoid-equivalence-univalent

  -- The unary natural numbers form a monoid.

  ℕ-monoid : Monoid lzero
  ℕ-monoid =
      ℕ
    , (0 , _+_)
    , [ ( ℕ-set
        , refl
        , (λ _ → Nat.+-right-identity)
        , (λ m _ _ → Nat.+-assoc m)
        )
      ]

  -- One variant of binary natural numbers forms a raw monoid.

  Bin-raw-monoid : Raw-monoid lzero
  Bin-raw-monoid =
      Bin
    , Bin.Operations-for-Bin.zero
    , Bin.Operations-for-Bin._+_

  -- The raw monoid underlying ℕ-monoid is equivalent (with erased
  -- proofs) to Bin-raw-monoid.

  ℕ≃ᴿᴹᴱBin : (ℕ , (0 , _+_)) ≃ᴿᴹᴱ Bin-raw-monoid
  ℕ≃ᴿᴹᴱBin =
      (ℕ    ↔⟨ inverse Bin.Bin↔ℕ ⟩□
       Bin  □)
    , [ ( (_↔_.from Bin.Bin↔ℕ 0         ≡⟨ _↔_.to Bin.≡-for-indices↔≡ [ refl _ ] ⟩∎
           Bin.Operations-for-Bin.zero  ∎)
        , (λ m n →
             _↔_.from Bin.Bin↔ℕ (m + n)                     ≡⟨ _↔_.to Bin.≡-for-indices↔≡ [ refl _ ] ⟩∎

             _↔_.from Bin.Bin↔ℕ m Bin.Operations-for-Bin.+
             _↔_.from Bin.Bin↔ℕ n                           ∎)
        )
      ]

  -- The monoid laws hold for Bin-raw-monoid (in erased contexts).

  @0 Bin-monoid-laws : Monoid-laws Bin-raw-monoid
  Bin-monoid-laws =
    induced-monoid ℕ-monoid Bin-raw-monoid ℕ≃ᴿᴹᴱBin .proj₁ .erased

  -- One variant of binary natural numbers forms a monoid.

  Bin-monoid : Monoid lzero
  Bin-monoid =
    Bin-raw-monoid .proj₁ , Bin-raw-monoid .proj₂ , [ Bin-monoid-laws ]

  -- This monoid is equivalent, with erased proofs, to ℕ-monoid.

  ℕ≃ᴹᴱBin : ℕ-monoid ≃ᴹᴱ Bin-monoid
  ℕ≃ᴹᴱBin =
    induced-monoid ℕ-monoid Bin-raw-monoid ℕ≃ᴿᴹᴱBin .proj₂

  -- In erased contexts the monoid is equal to ℕ-monoid.

  @0 ℕ≡Bin : ℕ-monoid ≡ Bin-monoid
  ℕ≡Bin = _≃_.to sip-for-monoids ℕ≃ᴹᴱBin

------------------------------------------------------------------------
-- Another example: bags

-- This is a variant of Examples 5.5 and 5.13 from "Internalizing
-- Representation Independence with Univalence".

-- The type A is assumed to come with decidable equality.

module Example₂ {A : Type a} (_≟_ : Decidable-equality A) where

  private

    -- The type A is a set.

    set : Is-set A
    set = decidable⇒set _≟_

  -- Raw bag structures.

  Raw-bag-structure : Structure a a
  Raw-bag-structure Bag =
    -- An empty bag.
    Bag ×
    -- Insertion.
    (A → Bag → Bag) ×
    -- Union.
    (Bag → Bag → Bag) ×
    -- The number of occurrences of the given element in the given
    -- bag.
    (A → Bag → ℕ)

  -- Raw-bag-structure can be expressed using some combinators.

  _ :
    Raw-bag-structure ≡
    Product Id
      (Product (Function (Const A) (Function Id Id))
         (Product (Function Id (Function Id Id))
            (Function (Const A) (Function Id (Const ℕ)))))
  _ = refl _

  -- Raw bag types.

  Raw-bag-type : Type (lsuc a)
  Raw-bag-type = Type-with Raw-bag-structure

  -- Raw bag equivalence predicates.

  Is-raw-bag-equivalence :
    Structure-preserving-equivalence-predicate Raw-bag-structure a
  Is-raw-bag-equivalence
    (_ , empty₁ , insert₁ , union₁ , count₁)
    (_ , empty₂ , insert₂ , union₂ , count₂)
    eq =
    _≃ᴱ_.to eq empty₁ ≡ empty₂ ×
    (∀ x xs → _≃ᴱ_.to eq (insert₁ x xs) ≡ insert₂ x (_≃ᴱ_.to eq xs)) ×
    (∀ xs ys →
       _≃ᴱ_.to eq (union₁ xs ys) ≡
       union₂ (_≃ᴱ_.to eq xs) (_≃ᴱ_.to eq ys)) ×
    (∀ x xs → count₁ x xs ≡ count₂ x (_≃ᴱ_.to eq xs))

  -- Is-raw-bag-equivalence can be expressed using some combinators.

  _ :
    Is-raw-bag-equivalence ≡
    Is-Product-equivalence
      Is-Id-equivalence
      (Is-Product-equivalence
         (Is-Function-equivalence′ (λ _ → EEq.id)
            (Is-Function-equivalence′ id
               Is-Id-equivalence))
         (Is-Product-equivalence
           (Is-Function-equivalence′ id
             (Is-Function-equivalence′ id
                Is-Id-equivalence))
             (Is-Function-equivalence′ (λ _ → EEq.id)
               (Is-Function-equivalence′ id
                  Is-Const-equivalence))))
  _ = refl _

  -- Raw bag equivalences (with erased proofs).

  infix 4 _≃ᴮᴱ_

  _≃ᴮᴱ_ : Raw-bag-type → Raw-bag-type → Type a
  _≃ᴮᴱ_ = _≃[ Is-raw-bag-equivalence ]ᴱ_

  -- Relation transformers for raw bag types.

  Raw-bag-typeᴿ : Relation-transformer-for Raw-bag-structure
  Raw-bag-typeᴿ =
    Productᴿ Idᴿ
      (Productᴿ (Function-Constᴿ A (Functionᴿ Idᴿ Idᴿ))
         (Productᴿ (Functionᴿ Idᴿ (Functionᴿ Idᴿ Idᴿ))
            (Function-Constᴿ A (Functionᴿ Idᴿ (Constᴿ ℕ)))))

  -- Raw-bag-typeᴿ is univalent.

  Raw-bag-typeᴿ-univalent : Univalentᴿ Raw-bag-typeᴿ
  Raw-bag-typeᴿ-univalent =
    Productᴿ-univalent Idᴿ-univalent
      (Productᴿ-univalent
         (Function-Constᴿ-univalent set
            (Functionᴿ-univalent Idᴿ-positive Idᴿ-univalent
               Idᴿ-univalent))
         (Productᴿ-univalent
            (Functionᴿ-univalent Idᴿ-positive Idᴿ-univalent
               (Functionᴿ-univalent Idᴿ-positive Idᴿ-univalent
                  Idᴿ-univalent))
            (Function-Constᴿ-univalent set
               (Functionᴿ-univalent Idᴿ-positive Idᴿ-univalent
                  (Constᴿ-univalent ℕ-set)))))

  -- One implementation of bags.

  List-bag : Type a
  List-bag = List A

  count₁′ : A → A → ℕ
  count₁′ x y = if x ≟ y then 1 else 0

  count₁ : A → List-bag → ℕ
  count₁ x = L.foldr (λ y → count₁′ x y +_) 0

  Raw-bag-structure-List-bag : Raw-bag-structure List-bag
  Raw-bag-structure-List-bag =
      []
    , _∷_
    , L._++_
    , count₁

  Raw-bag-type-List-bag : Raw-bag-type
  Raw-bag-type-List-bag = List-bag , Raw-bag-structure-List-bag

  -- Another implementation of bags.

  Assoc-list-bag : Type a
  Assoc-list-bag = List (ℕ × A)

  insert : ℕ → A → Assoc-list-bag → Assoc-list-bag
  insert m x []             = (m , x) ∷ []
  insert m x ((n , y) ∷ ys) =
    if x ≟ y
    then (m + n , y) ∷ ys
    else (n , y) ∷ insert m x ys

  union : Assoc-list-bag → Assoc-list-bag → Assoc-list-bag
  union = flip (L.foldr (uncurry insert))

  count₂′ : A → ℕ × A → ℕ
  count₂′ x (n , y) = if x ≟ y then n else 0

  count₂ : A → Assoc-list-bag → ℕ
  count₂ x = L.foldr (λ y → count₂′ x y +_) 0

  Raw-bag-structure-Assoc-list-bag : Raw-bag-structure Assoc-list-bag
  Raw-bag-structure-Assoc-list-bag =
      []
    , insert 1
    , union
    , count₂

  Raw-bag-type-Assoc-list-bag : Raw-bag-type
  Raw-bag-type-Assoc-list-bag =
    Assoc-list-bag , Raw-bag-structure-Assoc-list-bag

  -- Some properties of count₁.

  count₁-++ :
    ∀ xs → count₁ z (xs L.++ ys) ≡ count₁ z xs + count₁ z ys
  count₁-++          []       = refl _
  count₁-++ {z} {ys} (x ∷ xs) =
    count₁′ z x + (count₁ z (xs L.++ ys))      ≡⟨ cong (count₁′ z x +_) $ count₁-++ xs ⟩
    count₁′ z x + (count₁ z xs + count₁ z ys)  ≡⟨ Nat.+-assoc (count₁′ z x) ⟩∎
    (count₁′ z x + count₁ z xs) + count₁ z ys  ∎

  count₁-replicate :
    ∀ n → count₁ z (L.replicate n y) ≡ count₂′ z (n , y)
  count₁-replicate {z} {y} zero with z ≟ y
  … | yes _ = refl _
  … | no _  = refl _
  count₁-replicate {z} {y} (suc n) =
    count₁′ z y + count₁ z (L.replicate n y)  ≡⟨ cong (count₁′ z y +_) $ count₁-replicate n ⟩
    count₁′ z y + count₂′ z (n , y)           ≡⟨ lemma ⟩∎
    count₂′ z (suc n , y)                     ∎
    where
    lemma : count₁′ z y + count₂′ z (n , y) ≡ count₂′ z (suc n , y)
    lemma with z ≟ y
    … | yes _ = refl _
    … | no _  = refl _

  -- Some properties of count₂.

  count₂-insert-≡ :
    z ≡ x → ∀ ys → count₂ z (insert m x ys) ≡ m + count₂ z ys
  count₂-insert-≡ {z} {x} {m} z≡x = helper
    where
    helper : ∀ ys → count₂ z (insert m x ys) ≡ m + count₂ z ys
    helper [] with z ≟ x
    … | yes _  = m + 0  ∎
    … | no z≢x = ⊥-elim $ z≢x z≡x
    helper ((n , y) ∷ ys) with x ≟ y
    helper ((n , y) ∷ ys) | no x≢y =
      count₂′ z (n , y) + count₂ z (insert m x ys)  ≡⟨ cong (count₂′ z (n , y) +_) $ helper ys ⟩
      count₂′ z (n , y) + (m + count₂ z ys)         ≡⟨ Nat.+-assoc (count₂′ z (n , y)) ⟩
      (count₂′ z (n , y) + m) + count₂ z ys         ≡⟨ cong (_+ count₂ z ys) $ sym $ Nat.+-comm m ⟩
      (m + count₂′ z (n , y)) + count₂ z ys         ≡⟨ sym $ Nat.+-assoc m ⟩∎
      m + (count₂′ z (n , y) + count₂ z ys)         ∎
    helper ((n , y) ∷ ys) | yes x≡y =
      count₂′ z (m + n , y) + count₂ z ys    ≡⟨ cong (_+ _) lemma ⟩
      (m + count₂′ z (n , y)) + count₂ z ys  ≡⟨ sym $ Nat.+-assoc m ⟩∎
      m + (count₂′ z (n , y) + count₂ z ys)  ∎
      where
      lemma : count₂′ z (m + n , y) ≡ m + count₂′ z (n , y)
      lemma with z ≟ y
      … | yes _  = m + n  ∎
      … | no z≢y = ⊥-elim $ z≢y (trans z≡x x≡y)

  count₂-insert-≢ :
    z ≢ x → ∀ ys → count₂ z (insert m x ys) ≡ count₂ z ys
  count₂-insert-≢ {z} {x} {m} z≢x = helper
    where
    helper : ∀ ys → count₂ z (insert m x ys) ≡ count₂ z ys
    helper [] with z ≟ x
    … | no _    = 0  ∎
    … | yes z≡x = ⊥-elim $ z≢x z≡x
    helper ((n , y) ∷ ys) with x ≟ y
    … | no _ =
      count₂′ z (n , y) + count₂ z (insert m x ys)  ≡⟨ cong (count₂′ z (n , y) +_) $ helper ys ⟩∎
      count₂′ z (n , y) + count₂ z ys               ∎
    … | yes x≡y =
      count₂′ z (m + n , y) + count₂ z ys  ≡⟨ cong (_+ _) lemma ⟩∎
      count₂′ z (    n , y) + count₂ z ys  ∎
      where
      lemma : count₂′ z (m + n , y) ≡ count₂′ z (n , y)
      lemma with z ≟ y
      … | no _    = 0  ∎
      … | yes z≡y = ⊥-elim $ z≢x (trans z≡y (sym x≡y))

  count₂-insert :
    ∀ ys → count₂ z (insert m x ys) ≡ count₂′ z (m , x) + count₂ z ys
  count₂-insert {z} {m} {x} ys with z ≟ x
  … | yes z≡x =
    count₂ z (insert m x ys)  ≡⟨ count₂-insert-≡ z≡x ys ⟩∎
    m + count₂ z ys           ∎
  … | no z≢x =
    count₂ z (insert m x ys)  ≡⟨ count₂-insert-≢ z≢x ys ⟩∎
    count₂ z ys               ∎

  count₂-union :
    ∀ xs → count₂ z (union xs ys) ≡ count₂ z xs + count₂ z ys
  count₂-union {z} {ys} [] =
    count₂ z ys  ∎
  count₂-union {z} {ys} ((m , x) ∷ xs) =
    count₂ z (insert m x (union xs ys))              ≡⟨ count₂-insert (union xs ys) ⟩
    count₂′ z (m , x) + count₂ z (union xs ys)       ≡⟨ cong (count₂′ z (m , x) +_) $ count₂-union xs ⟩
    count₂′ z (m , x) + (count₂ z xs + count₂ z ys)  ≡⟨ Nat.+-assoc (count₂′ z (m , x)) ⟩∎
    (count₂′ z (m , x) + count₂ z xs) + count₂ z ys  ∎

  -- A relation relating values of the two bag types.

  infix 4 _∼_

  _∼_ : List-bag → Assoc-list-bag → Type a
  xs ∼ ys = ∀ z → count₁ z xs ≡ count₂ z ys

  -- The relation _∼_ is propositional.

  ∼-propositional : ∀ xs ys → Is-proposition (xs ∼ ys)
  ∼-propositional _ _ =
    Π-closure ext 1 λ _ →
    ℕ-set

  -- The relation _∼_ is a QER.

  ∼-QER : Is-QER _∼_
  ∼-QER =
      (λ {xs₁ xs₂ ys₁ ys₂} xs₁∼ys₁ xs₂∼ys₁ xs₂∼ys₂ z →
         count₁ z xs₁  ≡⟨ xs₁∼ys₁ z ⟩
         count₂ z ys₁  ≡⟨ sym $ xs₂∼ys₁ z ⟩
         count₁ z xs₂  ≡⟨ xs₂∼ys₂ z ⟩∎
         count₂ z ys₂  ∎)
    , (λ xs → ∣ to xs , ∼to xs ∣)
    , (λ ys → ∣ from ys , from∼ ys ∣)
    where
    to : List-bag → Assoc-list-bag
    to = L.foldr (insert 1) []

    from : Assoc-list-bag → List-bag
    from = L.foldr (λ (n , x) → L.replicate n x L.++_) []

    ∼to : ∀ xs → xs ∼ to xs
    ∼to []       _ = refl _
    ∼to (x ∷ xs) z =
      count₁′ z x + count₁ z xs             ≡⟨ cong (count₁′ z x +_) $ ∼to xs z ⟩
      count₁′ z x + count₂ z (to xs)        ≡⟨⟩
      count₂′ z (1 , x) + count₂ z (to xs)  ≡⟨ sym $ count₂-insert (to xs) ⟩∎
      count₂ z (insert 1 x (to xs))         ∎

    from∼ : ∀ ys → from ys ∼ ys
    from∼ []             _ = refl _
    from∼ ((n , y) ∷ ys) z =
      count₁ z (L.replicate n y L.++ from ys)          ≡⟨ count₁-++ (L.replicate n y) ⟩
      count₁ z (L.replicate n y) + count₁ z (from ys)  ≡⟨ cong (count₁ z (L.replicate n y) +_) $ from∼ ys z ⟩
      count₁ z (L.replicate n y) + count₂ z ys         ≡⟨ cong (_+ count₂ z ys) $ count₁-replicate n ⟩
      count₂′ z (n , y) + count₂ z ys                  ≡⟨⟩
      count₂ z ((n , y) ∷ ys)                          ∎

  -- Raw-bag-structure-List-bag and Raw-bag-structure-Assoc-list-bag
  -- are related by Raw-bag-typeᴿ _∼_.

  List-bag∼Assoc-list-bag :
    Raw-bag-typeᴿ _∼_
      Raw-bag-structure-List-bag Raw-bag-structure-Assoc-list-bag
  List-bag∼Assoc-list-bag =
      (λ z →
         count₁ z []  ≡⟨⟩
         count₂ z []  ∎)
    , (λ x {x = xs} {y = ys} xs∼ys z →
         count₁ z (x ∷ xs)                ≡⟨⟩
         count₁′ z x + count₁ z xs        ≡⟨ cong (count₁′ z x +_) (xs∼ys z) ⟩
         count₁′ z x + count₂ z ys        ≡⟨⟩
         count₂′ z (1 , x) + count₂ z ys  ≡⟨ sym $ count₂-insert ys ⟩∎
         count₂ z (insert 1 x ys)         ∎)
    , (λ {x = xs₁} {y = ys₁} xs₁∼ys₁ {x = xs₂} {y = ys₂} xs₂∼ys₂ z →
         count₁ z (xs₁ L.++ xs₂)      ≡⟨ count₁-++ xs₁ ⟩
         count₁ z xs₁ + count₁ z xs₂  ≡⟨ cong₂ _+_ (xs₁∼ys₁ z) (xs₂∼ys₂ z) ⟩
         count₂ z ys₁ + count₂ z ys₂  ≡⟨ sym $ count₂-union ys₁ ⟩∎
         count₂ z (union ys₁ ys₂)     ∎)
    , (λ x {x = xs} {y = ys} xs∼ys →
         count₁ x xs  ≡⟨ xs∼ys x ⟩∎
         count₂ x ys  ∎)

  -- There is an equivalence (with erased proofs) between List-bag
  -- quotiented by _∼_ ⟵ and Assoc-list-bag quotiented by _∼_ ⟶
  -- (where _/ᴱ_ is used for the quotients).

  List-bag≃ᴱAssoc-list-bag :
    List-bag /ᴱ _∼_ ⟵ ≃ᴱ Assoc-list-bag /ᴱ _∼_ ⟶
  List-bag≃ᴱAssoc-list-bag =
    /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ (Is-QER→Is-QERᴱ ∼-QER) ∼-propositional .proj₁

  -- Lists that are related by List-bag≃ᴱAssoc-list-bag (in a
  -- certain way) are also related by _∼_.
  --
  -- Note that this definition is not erased: it uses /ᴱ⟵≃ᴱ/ᴱ⟶
  -- instead of /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ, and ∼-QER instead of
  -- Is-QER→Is-QERᴱ ∼-QER.

  →∼ :
    ∀ xs ys →
    _≃ᴱ_.to List-bag≃ᴱAssoc-list-bag [ xs ] ≡ [ ys ] →
    xs ∼ ys
  →∼ xs ys = /ᴱ⟵≃ᴱ/ᴱ⟶ ∼-QER ∼-propositional .proj₂ xs ys .proj₁

  -- The function →∼ is an equivalence (in erased contexts).

  @0 →∼-equivalence : ∀ xs ys → Is-equivalence (→∼ xs ys)
  →∼-equivalence xs ys =
    /ᴱ⟵≃ᴱ/ᴱ⟶ ∼-QER ∼-propositional .proj₂ xs ys .proj₂ .erased

  -- The relation _∼_ can be expressed using
  -- List-bag≃ᴱAssoc-list-bag (in erased contexts).

  @0 ≃∼ :
    ∀ xs ys →
    (_≃ᴱ_.to List-bag≃ᴱAssoc-list-bag [ xs ] ≡ [ ys ]) ≃ (xs ∼ ys)
  ≃∼ = /ᴱ⟵≃ᴱ/ᴱ⟶ᴱ (Is-QER→Is-QERᴱ ∼-QER) ∼-propositional .proj₂ .erased

  private

    instance-of-Suitable→/ᴱ⟵×/ᴱ⟶ =
      Suitable→/ᴱ⟵×/ᴱ⟶
        Raw-bag-type-List-bag
        Raw-bag-type-Assoc-list-bag
        (Raw-bag-typeᴿ-univalent .proj₁)
        (Is-QER→Is-QERᴱ ∼-QER)
        ∼-propositional
        List-bag∼Assoc-list-bag

  -- There is a raw bag structure on List-bag /ᴱ _∼_ ⟵.

  Raw-bag-structure-List-bag-/ᴱ :
    Raw-bag-structure (List-bag /ᴱ _∼_ ⟵)
  Raw-bag-structure-List-bag-/ᴱ = instance-of-Suitable→/ᴱ⟵×/ᴱ⟶ .proj₁

  Raw-bag-type-List-bag-/ᴱ : Raw-bag-type
  Raw-bag-type-List-bag-/ᴱ =
    List-bag /ᴱ _∼_ ⟵ , Raw-bag-structure-List-bag-/ᴱ

  -- There is a raw bag structure on Assoc-list-bag /ᴱ _∼_ ⟶.

  Raw-bag-structure-Assoc-list-bag-/ᴱ :
    Raw-bag-structure (Assoc-list-bag /ᴱ _∼_ ⟶)
  Raw-bag-structure-Assoc-list-bag-/ᴱ =
    instance-of-Suitable→/ᴱ⟵×/ᴱ⟶ .proj₂ .proj₁

  Raw-bag-type-Assoc-list-bag-/ᴱ : Raw-bag-type
  Raw-bag-type-Assoc-list-bag-/ᴱ =
    Assoc-list-bag /ᴱ _∼_ ⟶ , Raw-bag-structure-Assoc-list-bag-/ᴱ

  -- The two raw bag structures are related to the underlying raw
  -- bag structures (in erased contexts).

  @0 List∼List-/ᴱ :
    Raw-bag-typeᴿ (Graph [_])
      Raw-bag-structure-List-bag Raw-bag-structure-List-bag-/ᴱ
  List∼List-/ᴱ = instance-of-Suitable→/ᴱ⟵×/ᴱ⟶ .proj₂ .proj₂ .erased .proj₁

  @0 Assoc-list∼Assoc-list-/ᴱ :
    Raw-bag-typeᴿ (Graph [_])
      Raw-bag-structure-Assoc-list-bag
      Raw-bag-structure-Assoc-list-bag-/ᴱ
  Assoc-list∼Assoc-list-/ᴱ =
    instance-of-Suitable→/ᴱ⟵×/ᴱ⟶ .proj₂ .proj₂ .erased .proj₂ .proj₁

  -- They are also related to each other (in erased contexts).

  @0 List-/ᴱ∼Assoc-list-/ᴱ :
    Raw-bag-typeᴿ (Graph (_≃ᴱ_.to List-bag≃ᴱAssoc-list-bag))
      Raw-bag-structure-List-bag-/ᴱ
      Raw-bag-structure-Assoc-list-bag-/ᴱ
  List-/ᴱ∼Assoc-list-/ᴱ =
    instance-of-Suitable→/ᴱ⟵×/ᴱ⟶ .proj₂ .proj₂ .erased .proj₂ .proj₂

  -- Raw-bag-type-List-bag-/ᴱ is equal to
  -- Raw-bag-type-Assoc-list-bag-/ᴱ (in erased contexts).

  @0 List-/ᴱ≡Assoc-list-/ᴱ :
    Raw-bag-type-List-bag-/ᴱ ≡ Raw-bag-type-Assoc-list-bag-/ᴱ
  List-/ᴱ≡Assoc-list-/ᴱ =
    Univalentᴿ→/ᴱ⟵×/ᴱ⟶
      Raw-bag-type-List-bag
      Raw-bag-type-Assoc-list-bag
      Raw-bag-typeᴿ-univalent
      (Is-QER→Is-QERᴱ ∼-QER)
      ∼-propositional
      List-bag∼Assoc-list-bag
      .proj₂ .proj₂ .erased .proj₂ .proj₂

  -- For List-bag /ᴱ _∼_ ⟵ equality of two lists can be expressed in
  -- terms of the induced count function (in erased contexts).

  @0 List-≡≃ :
    let count = Raw-bag-structure-List-bag-/ᴱ .proj₂ .proj₂ .proj₂ in
    (xs ys : List-bag /ᴱ _∼_ ⟵) →
    (xs ≡ ys) ≃ (∀ z → count z xs ≡ count z ys)
  List-≡≃ = Q.elim-prop λ @0 where
    .Q.is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Eq.left-closure ext 0 $
      Q./ᴱ-is-set
    .Q.[]ʳ xs → Q.elim-prop λ @0 where
      .Q.is-propositionʳ _ →
        Eq.left-closure ext 0 $
        Q./ᴱ-is-set
      .Q.[]ʳ ys →
        ([ xs ] ≡ [ ys ])                  ↝⟨ inverse $
                                              Q.related≃[equal]
                                                (Is-QER→Is-equivalence-relation-⟵ ∼-QER)
                                                T.truncation-is-proposition ⟩
        (_∼_ ⟵) xs ys                      ↝⟨ Eq.⇔→≃
                                                T.truncation-is-proposition
                                                (Π-closure ext 1 λ _ → ℕ-set)
                                                (T.rec λ @0 where
                                                   .T.truncation-is-propositionʳ →
                                                     Π-closure ext 1 λ _ → ℕ-set
                                                   .T.∣∣ʳ (zs , xs∼zs , ys∼zs) z →
                                                     count₁ z xs  ≡⟨ xs∼zs z ⟩
                                                     count₂ z zs  ≡⟨ sym $ ys∼zs z ⟩∎
                                                     count₁ z ys  ∎)
                                                (λ xs∼ys →
                                                   T.∥∥ᴱ-map
                                                     (λ (zs , xs∼zs) →
                                                          zs
                                                        , xs∼zs
                                                        , λ z →
                                                            count₁ z ys  ≡⟨ sym $ xs∼ys z ⟩
                                                            count₁ z xs  ≡⟨ xs∼zs z ⟩∎
                                                            count₂ z zs  ∎)
                                                     (∼-QER .proj₂ .proj₁ xs)) ⟩□
        (∀ z → count₁ z xs ≡ count₁ z ys)  □

  -- This property can easily be transported to
  -- Assoc-list-bag /ᴱ _∼_ ⟶.

  @0 Assoc-list-≡≃ :
    let count = Raw-bag-structure-Assoc-list-bag-/ᴱ
                  .proj₂ .proj₂ .proj₂ in
    (xs ys : Assoc-list-bag /ᴱ _∼_ ⟶) →
    (xs ≡ ys) ≃ (∀ z → count z xs ≡ count z ys)
  Assoc-list-≡≃ =
    subst
      (λ B → let count = B .proj₂ .proj₂ .proj₂ .proj₂ in
             (xs ys : B .proj₁) →
             (xs ≡ ys) ≃ (∀ z → count z xs ≡ count z ys))
      List-/ᴱ≡Assoc-list-/ᴱ
      List-≡≃
