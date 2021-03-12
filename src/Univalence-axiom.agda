------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Equality

module Univalence-axiom
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq as Bijection using (_↔_)
open import Bool eq
open Derived-definitions-and-properties eq
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq
  using (_≃_; ⟨_,_⟩; Is-equivalence) renaming (_∘_ to _⊚_)
import Equivalence.Contractible-preimages eq as CP
import Equivalence.Half-adjoint eq as HA
open import Function-universe eq as F hiding (id; _∘_)
open import Groupoid eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Injection eq using (Injective)
open import Logical-equivalence hiding (id; _∘_; inverse)
import Nat eq as Nat
open import Prelude hiding (swap)
open import Surjection eq using (_↠_)

------------------------------------------------------------------------
-- The univalence axiom

-- If two sets are equal, then they are equivalent.

≡⇒≃ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
≡⇒≃ = ≡⇒↝ equivalence

-- The univalence axiom states that ≡⇒≃ is an equivalence.

record Univalence′ {ℓ} (A B : Type ℓ) : Type (lsuc ℓ) where
  no-eta-equality
  pattern
  field
    univalence : Is-equivalence (≡⇒≃ {A = A} {B = B})

Univalence : ∀ ℓ → Type (lsuc ℓ)
Univalence ℓ = {A B : Type ℓ} → Univalence′ A B

-- An immediate consequence is that equalities are equivalent to
-- equivalences.

≡≃≃ : ∀ {ℓ} {A B : Type ℓ} → Univalence′ A B → (A ≡ B) ≃ (A ≃ B)
≡≃≃ univ = ⟨ ≡⇒≃ , Univalence′.univalence univ ⟩

-- In the case of sets equalities are equivalent to bijections (if we
-- add the assumption of extensionality).

≡≃↔ : ∀ {ℓ} {A B : Type ℓ} →
      Univalence′ A B →
      Extensionality ℓ ℓ →
      Is-set A →
      (A ≡ B) ≃ (A ↔ B)
≡≃↔ {A = A} {B} univ ext A-set =
  (A ≡ B)  ↝⟨ ≡≃≃ univ ⟩
  (A ≃ B)  ↔⟨ inverse $ Eq.↔↔≃ ext A-set ⟩□
  (A ↔ B)  □

-- Some abbreviations.

≡⇒→ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
≡⇒→ = _≃_.to ∘ ≡⇒≃

≡⇒← : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
≡⇒← = _≃_.from ∘ ≡⇒≃

≃⇒≡ : ∀ {ℓ} {A B : Type ℓ} → Univalence′ A B → A ≃ B → A ≡ B
≃⇒≡ univ = _≃_.from (≡≃≃ univ)

-- Univalence′ can be expressed without the record type.

Univalence′≃Is-equivalence-≡⇒≃ :
  ∀ {ℓ} {A B : Type ℓ} →
  Univalence′ A B ≃ Is-equivalence (≡⇒≃ {A = A} {B = B})
Univalence′≃Is-equivalence-≡⇒≃ =
  Eq.↔→≃
    Univalence′.univalence
    (λ eq → record { univalence = eq })
    refl
    (λ { (record { univalence = _ }) → refl _ })

------------------------------------------------------------------------
-- Propositional extensionality

-- Propositional extensionality.
--
-- Basically as defined by Chapman, Uustalu and Veltri in "Quotienting
-- the Delay Monad by Weak Bisimilarity".

Propositional-extensionality : (ℓ : Level) → Type (lsuc ℓ)
Propositional-extensionality ℓ =
  {A B : Type ℓ} → Is-proposition A → Is-proposition B → A ⇔ B → A ≡ B

-- Propositional extensionality is equivalent to univalence restricted
-- to propositions (assuming extensionality).
--
-- I took the statement of this result from Chapman, Uustalu and
-- Veltri's "Quotienting the Delay Monad by Weak Bisimilarity", and
-- Nicolai Kraus helped me with the proof.

Propositional-extensionality-is-univalence-for-propositions :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) (lsuc ℓ) →

  Propositional-extensionality ℓ
    ≃
  ({A B : Type ℓ} →
   Is-proposition A → Is-proposition B → Univalence′ A B)

Propositional-extensionality-is-univalence-for-propositions {ℓ} ext =
  Propositional-extensionality ℓ                          ↝⟨ lemma ⟩

  ({A B : Type ℓ} →
   Is-proposition A → Is-proposition B →
   Is-equivalence (≡⇒≃ {A = A} {B = B}))                  ↝⟨ (implicit-∀-cong ext $
                                                              implicit-∀-cong ext $
                                                              ∀-cong ext′ λ _ →
                                                              ∀-cong ext′ λ _ →
                                                              inverse Univalence′≃Is-equivalence-≡⇒≃) ⟩□
  ({A B : Type ℓ} →
   Is-proposition A → Is-proposition B → Univalence′ A B) □
  where
  ext′ : Extensionality ℓ (lsuc ℓ)
  ext′ = lower-extensionality _ lzero ext

  ext″ : Extensionality ℓ ℓ
  ext″ = lower-extensionality _ _ ext

  ⇔≃≡ :
    Propositional-extensionality ℓ →
    {A B : Type ℓ} →
    Is-proposition A → Is-proposition B →
    (A ⇔ B) ≃ (A ≡ B)
  ⇔≃≡ prop-ext {A} {B} A-prop B-prop =
    A ⇔ B                        ↝⟨ proj₂ (Eq.propositional-identity≃≡
                                             (λ (A B : Proposition ℓ) → proj₁ A ⇔ proj₁ B)
                                             (λ { (A , A-prop) (B , B-prop) →
                                                  ⇔-closure ext″ 1 A-prop B-prop })
                                             (λ _ → F.id)
                                             (λ { (A , A-prop) (B , B-prop) A⇔B →
                                                  Σ-≡,≡→≡ (prop-ext A-prop B-prop A⇔B)
                                                          (H-level-propositional ext″ 1 _ _) }))
                                          ext ⟩
    (A , A-prop) ≡ (B , B-prop)  ↔⟨ inverse $ ignore-propositional-component
                                                (H-level-propositional ext″ 1) ⟩□
    A ≡ B                        □

  ≡-closure :
    Propositional-extensionality ℓ →
    {A B : Type ℓ} →
    Is-proposition A → Is-proposition B → Is-proposition (A ≡ B)
  ≡-closure prop-ext A-prop B-prop =
    H-level.respects-surjection
      (_≃_.surjection (⇔≃≡ prop-ext A-prop B-prop))
      1
      (⇔-closure ext″ 1 A-prop B-prop)

  lemma =
    Eq.⇔→≃
      ([inhabited⇒+]⇒+ 0 λ prop-ext →
       implicit-Π-closure ext 1 λ _ →
       implicit-Π-closure ext 1 λ _ →
       Π-closure ext′ 1 λ A-prop →
       Π-closure ext′ 1 λ B-prop →
       Π-closure ext′ 1 λ _ →
       ≡-closure (prop-ext {_}) A-prop B-prop)
      (implicit-Π-closure ext 1 λ _ →
       implicit-Π-closure ext 1 λ _ →
       Π-closure ext′ 1 λ _ →
       Π-closure ext′ 1 λ _ →
       Eq.propositional ext _)
      (λ prop-ext A-prop B-prop →
         _⇔_.from HA.Is-equivalence⇔Is-equivalence-CP $ λ A≃B →
         ( prop-ext A-prop B-prop (_≃_.logical-equivalence A≃B)
         , Eq.left-closure ext″ 0 A-prop _ _
         ) , λ _ → Σ-≡,≡→≡
               (≡-closure prop-ext A-prop B-prop _ _)
               (mono₁ 1 (Eq.left-closure ext″ 0 A-prop) _ _))
      (λ univ {A B} A-prop B-prop →
         A ⇔ B  ↔⟨ Eq.⇔↔≃ ext″ A-prop B-prop ⟩
         A ≃ B  ↔⟨ inverse ⟨ _ , univ A-prop B-prop ⟩ ⟩□
         A ≡ B  □)

------------------------------------------------------------------------
-- An alternative formulation of univalence

-- First some supporting lemmas.

-- A variant of a part of Theorem 5.8.2 from the HoTT book.

flip-subst-is-equivalence↔∃-is-contractible :
  ∀ {k a p} {A : Type a} {P : A → Type p} →
  Extensionality? k (a ⊔ p) (a ⊔ p) →
  {x : A} {p : P x} →
  (∀ y → Is-equivalence (flip (subst {y = y} P) p))
    ↝[ k ]
  Contractible (∃ P)
flip-subst-is-equivalence↔∃-is-contractible {p = p′} {P = P}
                                            ext {x} {p} =
  generalise-ext?-prop
    lemma
    (λ ext → Π-closure (lower-extensionality p′ lzero ext) 1 λ _ →
             Eq.propositional ext _)
    Contractible-propositional
    ext
  where
  lemma :
    (∀ y → Is-equivalence (flip (subst {y = y} P) p))
      ⇔
    Contractible (∃ P)
  lemma = record
    { to = λ eq →                         $⟨ other-singleton-contractible x ⟩
        Contractible (Other-singleton x)  ↝⟨ id ⟩
        Contractible (∃ (x ≡_))           ↝⟨ H-level.respects-surjection (∃-cong λ y → _≃_.surjection ⟨ _ , eq y ⟩) 0 ⟩□
        Contractible (∃ P)                □
    ; from = λ { ((y , q) , u) z →
        _≃_.is-equivalence (Eq.↔⇒≃ (record
          { surjection = record
            { logical-equivalence = record
              { from = λ r →
                  x  ≡⟨ cong proj₁ $ sym $ u (x , p) ⟩
                  y  ≡⟨ cong proj₁ $ u (z , r) ⟩∎
                  z  ∎
              }
            ; right-inverse-of = λ r →
                subst P (trans (cong proj₁ (sym (u (x , p))))
                               (cong proj₁ (u (z , r)))) p         ≡⟨ sym $ subst-subst _ _ _ _ ⟩

                subst P (cong proj₁ (u (z , r)))
                  (subst P (cong proj₁ (sym (u (x , p)))) p)       ≡⟨ cong (subst P _) $ cong (λ p → subst P p _) $ sym $ proj₁-Σ-≡,≡←≡ _ ⟩

                subst P (cong proj₁ (u (z , r)))
                  (subst P (proj₁ (Σ-≡,≡←≡ (sym (u (x , p))))) p)  ≡⟨ cong (subst P _) $ proj₂ $ Σ-≡,≡←≡ (sym (u (x , p))) ⟩

                subst P (cong proj₁ (u (z , r))) q                 ≡⟨ cong (λ p → subst P p _) $ sym $ proj₁-Σ-≡,≡←≡ _ ⟩

                subst P (proj₁ (Σ-≡,≡←≡ (u (z , r)))) q            ≡⟨ proj₂ $ Σ-≡,≡←≡ (u (z , r)) ⟩∎

                r                                                  ∎
            }
          ; left-inverse-of = elim¹
              (λ {z} x≡z → trans (cong proj₁ (sym (u (x , p))))
                                 (cong proj₁ (u (z , subst P x≡z p))) ≡
                           x≡z)
              (trans (cong proj₁ (sym (u (x , p))))
                     (cong proj₁ (u (x , subst P (refl x) p)))  ≡⟨ cong₂ trans (cong-sym _ _)
                                                                               (cong (λ p → cong proj₁ (u (x , p))) $ subst-refl _ _) ⟩
               trans (sym (cong proj₁ (u (x , p))))
                     (cong proj₁ (u (x , p)))                   ≡⟨ trans-symˡ _ ⟩∎

               refl x                                           ∎)
          })) }
    }

-- If f is an equivalence, then f ∘ sym is also an equivalence.

∘-sym-preserves-equivalences :
  ∀ {k a b} {A : Type a} {B : Type b} {x y : A} {f : x ≡ y → B} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  Is-equivalence f ↝[ k ] Is-equivalence (f ∘ sym)
∘-sym-preserves-equivalences {A = A} {B} ext =
  Is-equivalence≃Is-equivalence-∘ʳ ext
    (_≃_.is-equivalence $ Eq.↔⇒≃ ≡-comm)

-- An alternative formulation of univalence, due to Martin Escardo
-- (see the following post to the Homotopy Type Theory group from
-- 2018-04-05:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ).

Other-univalence : ∀ ℓ → Type (lsuc ℓ)
Other-univalence ℓ =
  {B : Type ℓ} → Contractible (∃ λ (A : Type ℓ) → A ≃ B)

-- Univalence and Other-univalence are pointwise isomorphic (assuming
-- extensionality).

Univalence↔Other-univalence :
  ∀ {k ℓ} →
  Extensionality? k (lsuc ℓ) (lsuc ℓ) →
  Univalence ℓ ↝[ k ] Other-univalence ℓ
Univalence↔Other-univalence {k} {ℓ} ext =
  Univalence ℓ                                                          ↝⟨ implicit-∀-cong ext $ implicit-∀-cong ext $
                                                                           from-equivalence Univalence′≃Is-equivalence-≡⇒≃ ⟩
  ({A B : Type ℓ} → Is-equivalence (≡⇒≃ {A = A} {B = B}))               ↔⟨ Bijection.implicit-Π↔Π ⟩
  ((A {B} : Type ℓ) → Is-equivalence (≡⇒≃ {A = A} {B = B}))             ↝⟨ (∀-cong ext λ _ → from-bijection Bijection.implicit-Π↔Π) ⟩
  ((A B : Type ℓ) → Is-equivalence (≡⇒≃ {A = A} {B = B}))               ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∘-sym-preserves-equivalences ext) ⟩
  ((A B : Type ℓ) → Is-equivalence (≡⇒≃ {A = A} {B = B} ∘ sym))         ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ B →
                                                                            Is-equivalence-cong ext (λ B≡A →
      ≡⇒≃ (sym B≡A)                                                           ≡⟨ ≡⇒↝-in-terms-of-subst-sym _ _ ⟩
      subst (_≃ B) (sym (sym B≡A)) Eq.id                                      ≡⟨ cong (flip (subst _) _) $ sym-sym _ ⟩∎
      subst (_≃ B) B≡A Eq.id                                                  ∎)) ⟩

  ((A B : Type ℓ) → Is-equivalence (flip (subst {y = A} (_≃ B)) F.id))  ↔⟨ Π-comm ⟩
  ((B A : Type ℓ) → Is-equivalence (flip (subst {y = A} (_≃ B)) F.id))  ↝⟨ (∀-cong ext λ _ → flip-subst-is-equivalence↔∃-is-contractible ext) ⟩
  ((B : Type ℓ) → Contractible (∃ λ (A : Type ℓ) → A ≃ B))              ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
  ({B : Type ℓ} → Contractible (∃ λ (A : Type ℓ) → A ≃ B))              □

------------------------------------------------------------------------
-- Some simple lemmas

abstract

  -- "Evaluation rule" for ≡⇒≃.

  ≡⇒≃-refl : ∀ {a} {A : Type a} →
             ≡⇒≃ (refl A) ≡ Eq.id
  ≡⇒≃-refl = ≡⇒↝-refl

  -- "Evaluation rule" for ≡⇒→.

  ≡⇒→-refl : ∀ {a} {A : Type a} →
             ≡⇒→ (refl A) ≡ id
  ≡⇒→-refl = cong _≃_.to ≡⇒≃-refl

  -- "Evaluation rule" for ≡⇒←.

  ≡⇒←-refl : ∀ {a} {A : Type a} →
             ≡⇒← (refl A) ≡ id
  ≡⇒←-refl = cong _≃_.from ≡⇒≃-refl

  -- "Evaluation rule" (?) for ≃⇒≡.

  ≃⇒≡-id : ∀ {a} {A : Type a}
           (univ : Univalence′ A A) →
           ≃⇒≡ univ Eq.id ≡ refl A
  ≃⇒≡-id univ =
    ≃⇒≡ univ Eq.id           ≡⟨ sym $ cong (≃⇒≡ univ) ≡⇒≃-refl ⟩
    ≃⇒≡ univ (≡⇒≃ (refl _))  ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    refl _                   ∎

  -- A simplification lemma for ≃⇒≡.

  ≡⇒→-≃⇒≡ : ∀ k {ℓ} {A B : Type ℓ} {eq : A ≃ B}
            (univ : Univalence′ A B) →
            to-implication (≡⇒↝ k (≃⇒≡ univ eq)) ≡ _≃_.to eq
  ≡⇒→-≃⇒≡ k {eq = eq} univ =
    to-implication (≡⇒↝ k (≃⇒≡ univ eq))  ≡⟨ to-implication-≡⇒↝ k _ ⟩
    ≡⇒↝ implication (≃⇒≡ univ eq)         ≡⟨ sym $ to-implication-≡⇒↝ equivalence _ ⟩
    ≡⇒→ (≃⇒≡ univ eq)                     ≡⟨ cong _≃_.to (_≃_.right-inverse-of (≡≃≃ univ) _) ⟩∎
    _≃_.to eq                             ∎

------------------------------------------------------------------------
-- Another alternative formulation of univalence

-- Univalence′ A B is pointwise equivalent to CP.Univalence′ A B
-- (assuming extensionality).

Univalence′≃Univalence′-CP :
  ∀ {ℓ} {A B : Type ℓ} →
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Univalence′ A B ≃ CP.Univalence′ A B
Univalence′≃Univalence′-CP {ℓ = ℓ} {A = A} {B = B} ext =
  Univalence′ A B                         ↝⟨ Univalence′≃Is-equivalence-≡⇒≃ ⟩

  Is-equivalence ≡⇒≃                      ↝⟨ Is-equivalence-cong ext $
                                             elim
                                               (λ A≡B → ≡⇒≃ A≡B ≡ _≃_.from ≃≃≃ (CP.≡⇒≃ A≡B))
                                               (λ C →
      ≡⇒≃ (refl _)                                ≡⟨ ≡⇒≃-refl ⟩
      Eq.id                                       ≡⟨ Eq.lift-equality ext′ (refl _) ⟩
      _≃_.from ≃≃≃ CP.id                          ≡⟨ cong (_≃_.from ≃≃≃) $ sym CP.≡⇒≃-refl ⟩∎
      _≃_.from ≃≃≃ (CP.≡⇒≃ (refl _))              ∎) ⟩

  Is-equivalence (_≃_.from ≃≃≃ ∘ CP.≡⇒≃)  ↝⟨ Eq.⇔→≃
                                               (Eq.propositional ext _)
                                               (Eq.propositional ext _)
                                               (Eq.Two-out-of-three.g-g∘f (Eq.two-out-of-three _ _)
                                                  (_≃_.is-equivalence (inverse ≃≃≃)))
                                               (flip (Eq.Two-out-of-three.f-g (Eq.two-out-of-three _ _))
                                                  (_≃_.is-equivalence (inverse ≃≃≃))) ⟩

  Is-equivalence CP.≡⇒≃                   ↝⟨ Is-equivalence≃Is-equivalence-CP ext ⟩□

  CP.Is-equivalence CP.≡⇒≃                □
  where
  ext′ : Extensionality ℓ ℓ
  ext′ = lower-extensionality _ _ ext

  ≃≃≃ : {A B : Type ℓ} → (A ≃ B) ≃ (A CP.≃ B)
  ≃≃≃ = ≃≃≃-CP ext′

-- Univalence ℓ is pointwise equivalent to CP.Univalence ℓ (assuming
-- extensionality).

Univalence≃Univalence-CP :
  ∀ {ℓ} →
  Extensionality (lsuc ℓ) (lsuc ℓ) →
  Univalence ℓ ≃ CP.Univalence ℓ
Univalence≃Univalence-CP {ℓ = ℓ} ext =
  implicit-∀-cong ext $ implicit-∀-cong ext $
  Univalence′≃Univalence′-CP ext

------------------------------------------------------------------------
-- A consequence: Type is not a set

-- The univalence axiom implies that Type is not a set. (This was
-- pointed out to me by Thierry Coquand.)

module _ (univ : Univalence′ Bool Bool) where

  -- First note that the univalence axiom implies that there is an
  -- inhabitant of Bool ≡ Bool that is not equal to refl.

  swap-as-an-equality : Bool ≡ Bool
  swap-as-an-equality = ≃⇒≡ univ (Eq.↔⇒≃ swap)

  abstract

    swap≢refl : swap-as-an-equality ≢ refl Bool
    swap≢refl =
      swap-as-an-equality ≡ refl _            ↝⟨ cong ≡⇒→ ⟩
      ≡⇒→ swap-as-an-equality ≡ ≡⇒→ (refl _)  ↝⟨ subst (uncurry _≡_) (cong₂ _,_ (≡⇒→-≃⇒≡ equivalence univ) ≡⇒→-refl) ⟩
      not ≡ id                                ↝⟨ cong (_$ false) ⟩
      true ≡ false                            ↝⟨ Bool.true≢false ⟩□
      ⊥                                       □

    -- This implies that Type is not a set.

    ¬-Type-set : ¬ Is-set Type
    ¬-Type-set =
      Is-set Type                      ↝⟨ (λ h → h _ _) ⟩
      swap-as-an-equality ≡ refl Bool  ↝⟨ swap≢refl ⟩□
      ⊥                                □

abstract

  -- The result can be generalised to arbitrary universe levels.

  ¬-Type-set-↑ : ∀ {ℓ} →
                 Univalence′ (↑ ℓ Bool) (↑ ℓ Bool) →
                 ¬ Is-set (Type ℓ)
  ¬-Type-set-↑ {ℓ} univ =
    Is-set (Type ℓ)                          ↝⟨ (λ h → h _ _) ⟩
    swap-as-an-equality-↑ ≡ refl (↑ ℓ Bool)  ↝⟨ swap-↑≢refl ⟩□
    ⊥                                        □
    where
    swap-as-an-equality-↑ : ↑ ℓ Bool ≡ ↑ ℓ Bool
    swap-as-an-equality-↑ =
      ≃⇒≡ univ $
      Eq.↔⇒≃ $
      (Bijection.inverse Bijection.↑↔
         Bijection.∘
       swap
         Bijection.∘
       Bijection.↑↔)

    swap-↑≢refl : swap-as-an-equality-↑ ≢ refl (↑ ℓ Bool)
    swap-↑≢refl =
      swap-as-an-equality-↑ ≡ refl _            ↝⟨ cong ≡⇒→ ⟩
      ≡⇒→ swap-as-an-equality-↑ ≡ ≡⇒→ (refl _)  ↝⟨ subst (uncurry _≡_) (cong₂ _,_ (≡⇒→-≃⇒≡ equivalence univ) ≡⇒→-refl) ⟩
      lift ∘ not ∘ lower ≡ id                   ↝⟨ cong (lower ∘ (_$ lift false)) ⟩
      true ≡ false                              ↝⟨ Bool.true≢false ⟩□
      ⊥                                         □

------------------------------------------------------------------------
-- A consequence: some equality types have infinitely many inhabitants

abstract

  -- Some equality types have infinitely many inhabitants (assuming
  -- univalence).

  equality-can-have-infinitely-many-inhabitants :
    Univalence′ ℕ ℕ →
    ∃ λ (A : Type) → ∃ λ (B : Type) →
    ∃ λ (p : ℕ → A ≡ B) → Injective p
  equality-can-have-infinitely-many-inhabitants univ =
    (ℕ , ℕ , cast ∘ p , cast-preserves-injections p p-injective)
    where
    cast : ℕ ≃ ℕ → ℕ ≡ ℕ
    cast = ≃⇒≡ univ

    cast-preserves-injections :
      {A : Type} (f : A → ℕ ≃ ℕ) →
      Injective f → Injective (cast ∘ f)
    cast-preserves-injections f inj {x = x} {y = y} cast-f-x≡cast-f-y =
      inj (f x               ≡⟨ sym $ _≃_.right-inverse-of (≡≃≃ univ) (f x) ⟩
           ≡⇒≃ (cast (f x))  ≡⟨ cong ≡⇒≃ cast-f-x≡cast-f-y ⟩
           ≡⇒≃ (cast (f y))  ≡⟨ _≃_.right-inverse-of (≡≃≃ univ) (f y) ⟩∎
           f y               ∎)

    swap_and-0 : ℕ → ℕ → ℕ
    swap i and-0 zero    = i
    swap i and-0 (suc n) with i Nat.≟ suc n
    ... | yes i≡1+n = zero
    ... | no  i≢1+n = suc n

    swap∘swap : ∀ i n → swap i and-0 (swap i and-0 n) ≡ n
    swap∘swap zero    zero    = refl zero
    swap∘swap (suc i) zero    with i Nat.≟ i
    ... | yes _   = refl 0
    ... | no  i≢i = ⊥-elim $ i≢i (refl i)
    swap∘swap i       (suc n) with i Nat.≟ suc n
    ... | yes i≡1+n = i≡1+n
    ... | no  i≢1+n with i Nat.≟ suc n
    ...   | yes i≡1+n = ⊥-elim $ i≢1+n i≡1+n
    ...   | no  _     = refl (suc n)

    p : ℕ → ℕ ≃ ℕ
    p i = Eq.↔⇒≃ record
      { surjection = record
        { logical-equivalence = record { to   = swap i and-0
                                       ; from = swap i and-0
                                       }
        ; right-inverse-of    = swap∘swap i
        }
      ; left-inverse-of = swap∘swap i
      }

    p-injective : Injective p
    p-injective {x = i₁} {y = i₂} p-i₁≡p-i₂ =
      i₁               ≡⟨ refl i₁ ⟩
      swap i₁ and-0 0  ≡⟨ cong (λ f → f 0) swap-i₁≡swap-i₂ ⟩
      swap i₂ and-0 0  ≡⟨ refl i₂ ⟩∎
      i₂               ∎
      where
      swap-i₁≡swap-i₂ : swap i₁ and-0 ≡ swap i₂ and-0
      swap-i₁≡swap-i₂ = cong _≃_.to p-i₁≡p-i₂

------------------------------------------------------------------------
-- A consequence: extensionality for functions

-- The transport theorem.

transport-theorem :
  ∀ {p₁ p₂} (P : Type p₁ → Type p₂) →
  (resp : ∀ {A B} → A ≃ B → P A → P B) →
  (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
  ∀ {A B} (univ : Univalence′ A B) →
  (A≃B : A ≃ B) (p : P A) →
  resp A≃B p ≡ subst P (≃⇒≡ univ A≃B) p
transport-theorem P resp resp-id univ A≃B p =
  resp A≃B p              ≡⟨ sym $ cong (λ q → resp q p) (right-inverse-of A≃B) ⟩
  resp (to (from A≃B)) p  ≡⟨ elim (λ {A B} A≡B → ∀ p →
                                     resp (≡⇒≃ A≡B) p ≡ subst P A≡B p)
                                  (λ A p →
                                     resp (≡⇒≃ (refl A)) p  ≡⟨ trans (cong (λ q → resp q p) ≡⇒↝-refl) (resp-id p) ⟩
                                     p                      ≡⟨ sym $ subst-refl P p ⟩∎
                                     subst P (refl A) p     ∎) _ _ ⟩∎
  subst P (from A≃B) p    ∎
  where open _≃_ (≡≃≃ univ)

abstract

  -- If the univalence axiom holds, then any "resp" function that
  -- preserves identity is an equivalence family.

  resp-is-equivalence :
    ∀ {p₁ p₂} (P : Type p₁ → Type p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    ∀ {A B} (univ : Univalence′ A B) →
    (A≃B : A ≃ B) → Is-equivalence (resp A≃B)
  resp-is-equivalence P resp resp-id univ A≃B =
    Eq.respects-extensional-equality
      (λ p → sym $ transport-theorem P resp resp-id univ A≃B p)
      (Eq.subst-is-equivalence P (≃⇒≡ univ A≃B))

  -- If f is an equivalence, then (non-dependent) precomposition with
  -- f is also an equivalence (assuming univalence).

  precomposition-is-equivalence :
    ∀ {ℓ c} {A B : Type ℓ} {C : Type c} →
    Univalence′ B A → (A≃B : A ≃ B) →
    Is-equivalence (λ (g : B → C) → g ∘ _≃_.to A≃B)
  precomposition-is-equivalence {ℓ} {c} {C = C} univ A≃B =
    resp-is-equivalence P resp refl univ (Eq.inverse A≃B)
    where
    P : Type ℓ → Type (ℓ ⊔ c)
    P X = X → C

    resp : ∀ {A B} → A ≃ B → P A → P B
    resp A≃B p = p ∘ _≃_.from A≃B

-- If h is an equivalence, then one can cancel (non-dependent)
-- precompositions with h (assuming univalence).

precompositions-cancel :
  ∀ {ℓ c} {A B : Type ℓ} {C : Type c} →
  Univalence′ B A → (A≃B : A ≃ B) {f g : B → C} →
  let open _≃_ A≃B in
  f ∘ to ≡ g ∘ to → f ≡ g
precompositions-cancel univ A≃B {f} {g} f∘to≡g∘to =
  f            ≡⟨ sym $ left-inverse-of f ⟩
  from (to f)  ≡⟨ cong from f∘to≡g∘to ⟩
  from (to g)  ≡⟨ left-inverse-of g ⟩∎
  g            ∎
  where open _≃_ (⟨ _ , precomposition-is-equivalence univ A≃B ⟩)

-- Pairs of equal elements.

_²/≡ : ∀ {ℓ} → Type ℓ → Type ℓ
A ²/≡ = ∃ λ (x : A) → ∃ λ (y : A) → y ≡ x

-- The set of such pairs is isomorphic to the underlying type.

-²/≡↔- : ∀ {a} {A : Type a} → (A ²/≡) ↔ A
-²/≡↔- {A = A} =
  (∃ λ (x : A) → ∃ λ (y : A) → y ≡ x)  ↝⟨ ∃-cong (λ _ → _⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩
  A × ⊤                                ↝⟨ ×-right-identity ⟩□
  A                                    □

abstract

  -- The univalence axiom implies non-dependent functional
  -- extensionality.

  extensionality :
    ∀ {a b} {A : Type a} {B : Type b} →
    Univalence′ (B ²/≡) B →
    {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  extensionality {A = A} {B} univ {f} {g} f≡g =
    f          ≡⟨ refl f ⟩
    f′ ∘ pair  ≡⟨ cong (λ (h : B ²/≡ → B) → h ∘ pair) f′≡g′ ⟩
    g′ ∘ pair  ≡⟨ refl g ⟩∎
    g          ∎
    where
    f′ : B ²/≡ → B
    f′ = proj₁ ∘ proj₂

    g′ : B ²/≡ → B
    g′ = proj₁

    f′≡g′ : f′ ≡ g′
    f′≡g′ = precompositions-cancel
              univ
              (Eq.↔⇒≃ $ Bijection.inverse -²/≡↔-)
              (refl id)

    pair : A → B ²/≡
    pair x = (g x , f x , f≡g x)

  -- The univalence axiom implies that contractibility is closed under
  -- Π A.

  Π-closure-contractible :
    ∀ {b} → Univalence′ (Type b ²/≡) (Type b) →
    ∀ {a} {A : Type a} {B : A → Type b} →
    (∀ x → Univalence′ (↑ b ⊤) (B x)) →
    (∀ x → Contractible (B x)) → Contractible ((x : A) → B x)
  Π-closure-contractible {b} univ₁ {A = A} {B} univ₂ contr =
    subst Contractible A→⊤≡[x:A]→Bx →⊤-contractible
    where
    const-⊤≡B : const (↑ b ⊤) ≡ B
    const-⊤≡B = extensionality univ₁ λ x →
      _≃_.from (≡≃≃ (univ₂ x)) $ Eq.↔⇒≃ $
        Bijection.contractible-isomorphic
          (↑-closure 0 ⊤-contractible) (contr x)

    A→⊤≡[x:A]→Bx : (A → ↑ b ⊤) ≡ ((x : A) → B x)
    A→⊤≡[x:A]→Bx = cong (λ X → (x : A) → X x) const-⊤≡B

    →⊤-contractible : Contractible (A → ↑ b ⊤)
    →⊤-contractible = (_ , λ _ → refl _)

  -- Thus we also get extensionality for dependent functions.

  dependent-extensionality′ :
    ∀ {b} → Univalence′ (Type b ²/≡) (Type b) →
    ∀ {a} {A : Type a} →
    (∀ {B : A → Type b} x → Univalence′ (↑ b ⊤) (B x)) →
    {B : A → Type b} → Extensionality′ A B
  dependent-extensionality′ univ₁ univ₂ =
    _⇔_.to Π-closure-contractible⇔extensionality
      (Π-closure-contractible univ₁ univ₂)

  dependent-extensionality :
    ∀ {b} →
    Univalence (lsuc b) →
    Univalence b →
    ∀ {a} → Extensionality a b
  apply-ext (dependent-extensionality univ₁ univ₂) =
    dependent-extensionality′ univ₁ (λ _ → univ₂)

------------------------------------------------------------------------
-- Pow and Fam

-- Slightly different variants of Pow and Fam are described in
-- "Specifying interactions with dependent types" by Peter Hancock and
-- Anton Setzer (in APPSEM Workshop on Subtyping & Dependent Types in
-- Programming, DTP'00). The fact that Pow and Fam are logically
-- equivalent is proved in "Programming Interfaces and Basic Topology"
-- by Peter Hancock and Pierre Hyvernat (Annals of Pure and Applied
-- Logic, 2006). The results may be older than this.

-- Pow.

Pow : ∀ ℓ {a} → Type a → Type (lsuc (a ⊔ ℓ))
Pow ℓ {a} A = A → Type (a ⊔ ℓ)

-- Fam.

Fam : ∀ ℓ {a} → Type a → Type (lsuc (a ⊔ ℓ))
Fam ℓ {a} A = ∃ λ (I : Type (a ⊔ ℓ)) → I → A

-- Pow and Fam are pointwise logically equivalent.

Pow⇔Fam : ∀ ℓ {a} {A : Type a} →
          Pow ℓ A ⇔ Fam ℓ A
Pow⇔Fam _ = record
  { to   = λ P → ∃ P , proj₁
  ; from = λ { (I , f) a → ∃ λ i → f i ≡ a }
  }

-- Pow and Fam are pointwise isomorphic (assuming extensionality and
-- univalence).

Pow↔Fam : ∀ ℓ {a} {A : Type a} →
          Extensionality a (lsuc (a ⊔ ℓ)) →
          Univalence (a ⊔ ℓ) →
          Pow ℓ A ↔ Fam ℓ A
Pow↔Fam ℓ {A = A} ext univ = record
  { surjection = record
    { logical-equivalence = Pow⇔Fam ℓ
    ; right-inverse-of    = λ { (I , f) →
        let lemma₁ =
              (∃ λ a → ∃ λ i → f i ≡ a)  ↔⟨ ∃-comm ⟩
              (∃ λ i → ∃ λ a → f i ≡ a)  ↔⟨ ∃-cong (λ _ → _⇔_.to contractible⇔↔⊤ (other-singleton-contractible _)) ⟩
              I × ⊤                      ↔⟨ ×-right-identity ⟩□
              I                          □

            lemma₂ =
              subst (λ I → I → A) (≃⇒≡ univ lemma₁) proj₁  ≡⟨ sym $ transport-theorem (λ I → I → A) (λ eq → _∘ _≃_.from eq) refl univ _ _ ⟩
              proj₁ ∘ _≃_.from lemma₁                      ≡⟨ refl _ ⟩∎
              f                                            ∎
        in
        (∃ λ a → ∃ λ i → f i ≡ a) , proj₁  ≡⟨ Σ-≡,≡→≡ (≃⇒≡ univ lemma₁) lemma₂ ⟩∎
        I                         , f      ∎ }
    }
  ; left-inverse-of = λ P →
      let lemma = λ a →
            (∃ λ (i : ∃ P) → proj₁ i ≡ a)  ↔⟨ inverse Σ-assoc ⟩
            (∃ λ a′ → P a′ × a′ ≡ a)       ↔⟨ inverse $ ∃-intro _ _ ⟩□
            P a                            □
      in
      (λ a → ∃ λ (i : ∃ P) → proj₁ i ≡ a)  ≡⟨ apply-ext ext (λ a → ≃⇒≡ univ (lemma a)) ⟩∎
      P                                    ∎
  }

-- An isomorphism that follows from Pow↔Fam.
--
-- This isomorphism was suggested to me by Paolo Capriotti.

→↔Σ≃Σ :
  ∀ ℓ {a b} {A : Type a} {B : Type b} →
  Extensionality (a ⊔ b ⊔ ℓ) (lsuc (a ⊔ b ⊔ ℓ)) →
  Univalence (a ⊔ b ⊔ ℓ) →
  (A → B) ↔ ∃ λ (P : B → Type (a ⊔ b ⊔ ℓ)) → A ≃ Σ B P
→↔Σ≃Σ ℓ {a} {b} {A} {B} ext univ =
  (A → B)                                                    ↝⟨ →-cong₁ (lower-extensionality lzero _ ext) (inverse Bijection.↑↔) ⟩
  (↑ (b ⊔ ℓ) A → B)                                          ↝⟨ inverse ×-left-identity ⟩
  ⊤ × (↑ _ A → B)                                            ↝⟨ inverse $ _⇔_.to contractible⇔↔⊤ (singleton-contractible _) ×-cong F.id ⟩
  (∃ λ (A′ : Type ℓ′) → A′ ≡ ↑ _ A) × (↑ _ A → B)            ↝⟨ inverse Σ-assoc ⟩
  (∃ λ (A′ : Type ℓ′) → A′ ≡ ↑ _ A × (↑ _ A → B))            ↝⟨ (∃-cong λ _ → ∃-cong λ eq → →-cong₁ (lower-extensionality lzero _ ext) (≡⇒≃ (sym eq))) ⟩
  (∃ λ (A′ : Type ℓ′) → A′ ≡ ↑ _ A × (A′ → B))               ↝⟨ (∃-cong λ _ → ×-comm) ⟩
  (∃ λ (A′ : Type ℓ′) → (A′ → B) × A′ ≡ ↑ _ A)               ↝⟨ Σ-assoc ⟩
  (∃ λ (p : ∃ λ (A′ : Type ℓ′) → A′ → B) → proj₁ p ≡ ↑ _ A)  ↝⟨ inverse $ Σ-cong (Pow↔Fam (a ⊔ ℓ) (lower-extensionality ℓ′ lzero ext) univ) (λ _ → F.id) ⟩
  (∃ λ (P : B → Type ℓ′) → ∃ P ≡ ↑ _ A)                      ↔⟨ (∃-cong λ _ → ≡≃≃ univ) ⟩
  (∃ λ (P : B → Type ℓ′) → ∃ P ≃ ↑ _ A)                      ↝⟨ (∃-cong λ _ → Groupoid.⁻¹-bijection (Eq.groupoid (lower-extensionality ℓ′ _ ext))) ⟩
  (∃ λ (P : B → Type ℓ′) → ↑ _ A ≃ ∃ P)                      ↔⟨ (∃-cong λ _ →
                                                                 Eq.≃-preserves (lower-extensionality lzero _ ext) (Eq.↔⇒≃ Bijection.↑↔) F.id) ⟩□
  (∃ λ (P : B → Type ℓ′) → A ≃ ∃ P)                          □
  where
  ℓ′ = a ⊔ b ⊔ ℓ

------------------------------------------------------------------------
-- More lemmas

abstract

  -- The univalence axiom is propositional (assuming extensionality).

  Univalence′-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) (lsuc ℓ) →
    {A B : Type ℓ} → Is-proposition (Univalence′ A B)
  Univalence′-propositional ext {A = A} {B = B} =          $⟨ Eq.propositional ext ≡⇒≃ ⟩
    Is-proposition (Is-equivalence (≡⇒≃ {A = A} {B = B}))  ↝⟨ H-level-cong _ 1 (inverse Univalence′≃Is-equivalence-≡⇒≃) ⦂ (_ → _) ⟩□
    Is-proposition (Univalence′ A B)                       □

  Univalence-propositional :
    ∀ {ℓ} → Extensionality (lsuc ℓ) (lsuc ℓ) →
    Is-proposition (Univalence ℓ)
  Univalence-propositional ext =
    implicit-Π-closure ext 1 λ _ →
    implicit-Π-closure ext 1 λ _ →
    Univalence′-propositional ext

  -- ≡⇒≃ commutes with sym/Eq.inverse (assuming extensionality).

  ≡⇒≃-sym :
    ∀ {ℓ} → Extensionality ℓ ℓ →
    {A B : Type ℓ} (A≡B : A ≡ B) →
    ≡⇒≃ (sym A≡B) ≡ Eq.inverse (≡⇒≃ A≡B)
  ≡⇒≃-sym ext = elim¹

    (λ eq → ≡⇒≃ (sym eq) ≡ Eq.inverse (≡⇒≃ eq))

    (≡⇒≃ (sym (refl _))         ≡⟨ cong ≡⇒≃ sym-refl ⟩
     ≡⇒≃ (refl _)               ≡⟨ ≡⇒≃-refl ⟩
     Eq.id                      ≡⟨ sym $ Groupoid.identity (Eq.groupoid ext) ⟩
     Eq.inverse Eq.id           ≡⟨ cong Eq.inverse $ sym ≡⇒≃-refl ⟩∎
     Eq.inverse (≡⇒≃ (refl _))  ∎)

  -- ≃⇒≡ univ commutes with Eq.inverse/sym (assuming extensionality).

  ≃⇒≡-inverse :
    ∀ {ℓ} (univ : Univalence ℓ) → Extensionality ℓ ℓ →
    {A B : Type ℓ} (A≃B : A ≃ B) →
    ≃⇒≡ univ (Eq.inverse A≃B) ≡ sym (≃⇒≡ univ A≃B)
  ≃⇒≡-inverse univ ext A≃B =
    ≃⇒≡ univ (Eq.inverse A≃B)                   ≡⟨ sym $ cong (λ p → ≃⇒≡ univ (Eq.inverse p)) (_≃_.right-inverse-of (≡≃≃ univ) _) ⟩
    ≃⇒≡ univ (Eq.inverse (≡⇒≃ (≃⇒≡ univ A≃B)))  ≡⟨ cong (≃⇒≡ univ) $ sym $ ≡⇒≃-sym ext _ ⟩
    ≃⇒≡ univ (≡⇒≃ (sym (≃⇒≡ univ A≃B)))         ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    sym (≃⇒≡ univ A≃B)                          ∎

  -- ≡⇒≃ commutes with trans/_⊚_ (assuming extensionality).

  ≡⇒≃-trans :
    ∀ {ℓ} → Extensionality ℓ ℓ →
    {A B C : Type ℓ} (A≡B : A ≡ B) (B≡C : B ≡ C) →
    ≡⇒≃ (trans A≡B B≡C) ≡ ≡⇒≃ B≡C ⊚ ≡⇒≃ A≡B
  ≡⇒≃-trans ext A≡B = elim¹

    (λ eq → ≡⇒≃ (trans A≡B eq) ≡ ≡⇒≃ eq ⊚ ≡⇒≃ A≡B)

    (≡⇒≃ (trans A≡B (refl _))  ≡⟨ cong ≡⇒≃ $ trans-reflʳ _ ⟩
     ≡⇒≃ A≡B                   ≡⟨ sym $ Groupoid.left-identity (Eq.groupoid ext) _ ⟩
     Eq.id ⊚ ≡⇒≃ A≡B           ≡⟨ sym $ cong (λ eq → eq ⊚ ≡⇒≃ A≡B) ≡⇒≃-refl ⟩∎
     ≡⇒≃ (refl _) ⊚ ≡⇒≃ A≡B    ∎)

  -- ≃⇒≡ univ commutes with _⊚_/flip trans (assuming extensionality).

  ≃⇒≡-∘ :
    ∀ {ℓ} (univ : Univalence ℓ) → Extensionality ℓ ℓ →
    {A B C : Type ℓ} (A≃B : A ≃ B) (B≃C : B ≃ C) →
    ≃⇒≡ univ (B≃C ⊚ A≃B) ≡ trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)
  ≃⇒≡-∘ univ ext A≃B B≃C =
    ≃⇒≡ univ (B≃C ⊚ A≃B)                                  ≡⟨ sym $ cong₂ (λ p q → ≃⇒≡ univ (p ⊚ q)) (_≃_.right-inverse-of (≡≃≃ univ) _)
                                                                                                    (_≃_.right-inverse-of (≡≃≃ univ) _) ⟩
    ≃⇒≡ univ (≡⇒≃ (≃⇒≡ univ B≃C) ⊚ ≡⇒≃ (≃⇒≡ univ A≃B))    ≡⟨ cong (≃⇒≡ univ) $ sym $ ≡⇒≃-trans ext _ _ ⟩
    ≃⇒≡ univ (≡⇒≃ (trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)))  ≡⟨ _≃_.left-inverse-of (≡≃≃ univ) _ ⟩∎
    trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)                   ∎

  -- A variant of the transport theorem.

  transport-theorem′ :
    ∀ {a p r} {A : Type a}
    (P : A → Type p) (R : A → A → Type r)
    (≡↠R : ∀ {x y} → (x ≡ y) ↠ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (∀ x p → resp (_↠_.to ≡↠R (refl x)) p ≡ p) →
    ∀ {x y} (r : R x y) (p : P x) →
    resp r p ≡ subst P (_↠_.from ≡↠R r) p
  transport-theorem′ P R ≡↠R resp hyp r p =
    resp r p              ≡⟨ sym $ cong (λ r → resp r p) (right-inverse-of r) ⟩
    resp (to (from r)) p  ≡⟨ elim (λ {x y} x≡y → ∀ p →
                                     resp (_↠_.to ≡↠R x≡y) p ≡ subst P x≡y p)
                                  (λ x p →
                                     resp (_↠_.to ≡↠R (refl x)) p  ≡⟨ hyp x p ⟩
                                     p                             ≡⟨ sym $ subst-refl P p ⟩∎
                                     subst P (refl x) p            ∎) _ _ ⟩∎
    subst P (from r) p    ∎
    where open _↠_ ≡↠R

  -- Simplification (?) lemma for transport-theorem′.

  transport-theorem′-refl :
    ∀ {a p r} {A : Type a}
    (P : A → Type p) (R : A → A → Type r)
    (≡≃R : ∀ {x y} → (x ≡ y) ≃ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (resp-refl : ∀ x p → resp (_≃_.to ≡≃R (refl x)) p ≡ p) →
    ∀ {x} (p : P x) →
    transport-theorem′ P R (_≃_.surjection ≡≃R) resp resp-refl
                       (_≃_.to ≡≃R (refl x)) p ≡
    trans (trans (resp-refl x p) (sym $ subst-refl P p))
          (sym $ cong (λ eq → subst P eq p)
                      (_≃_.left-inverse-of ≡≃R (refl x)))
  transport-theorem′-refl P R ≡≃R resp resp-refl {x} p =

    let body = λ x p → trans (resp-refl x p) (sym $ subst-refl P p)

        lemma =
          trans (sym $ cong (λ r → resp (to r) p) $ refl (refl x))
                (elim (λ {x y} x≡y →
                         ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                      (λ x p → trans (resp-refl x p)
                                     (sym $ subst-refl P p))
                      (refl x) p)                                        ≡⟨ cong₂ (λ q r → trans q (r p))
                                                                                  (sym $ cong-sym (λ r → resp (to r) p) _)
                                                                                  (elim-refl (λ {x y} x≡y → ∀ p →
                                                                                                resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p) _) ⟩
          trans (cong (λ r → resp (to r) p) $ sym $ refl (refl x))
                (body x p)                                               ≡⟨ cong (λ q → trans (cong (λ r → resp (to r) p) q) (body x p))
                                                                                 sym-refl ⟩
          trans (cong (λ r → resp (to r) p) $ refl (refl x)) (body x p)  ≡⟨ cong (λ q → trans q (body x p)) $
                                                                                 cong-refl (λ r → resp (to r) p) ⟩
          trans (refl (resp (to (refl x)) p)) (body x p)                 ≡⟨ trans-reflˡ _ ⟩

          body x p                                                       ≡⟨ sym $ trans-reflʳ _ ⟩

          trans (body x p) (refl (subst P (refl x) p))                   ≡⟨ cong (trans (body x p)) $ sym $
                                                                                 cong-refl (λ eq → subst P eq p) ⟩
          trans (body x p)
                (cong (λ eq → subst P eq p) (refl (refl x)))             ≡⟨ cong (trans (body x p) ∘ cong (λ eq → subst P eq p)) $
                                                                                 sym sym-refl ⟩
          trans (body x p)
                (cong (λ eq → subst P eq p) (sym (refl (refl x))))       ≡⟨ cong (trans (body x p)) $ cong-sym (λ eq → subst P eq p) _ ⟩∎

          trans (body x p)
                (sym $ cong (λ eq → subst P eq p) (refl (refl x)))       ∎
    in

    trans (sym $ cong (λ r → resp r p) $ right-inverse-of (to (refl x)))
          (elim (λ {x y} x≡y →
                   ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                body (from (to (refl x))) p)                              ≡⟨ cong (λ eq → trans (sym $ cong (λ r → resp r p) eq)
                                                                                                (elim (λ {x y} x≡y → ∀ p →
                                                                                                         resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                                                                                                      body (from (to (refl x))) p)) $
                                                                                  sym $ left-right-lemma (refl x) ⟩
    trans (sym $ cong (λ r → resp r p) $ cong to $
             left-inverse-of (refl x))
          (elim (λ {x y} x≡y →
                   ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                body (from (to (refl x))) p)                              ≡⟨ cong (λ eq → trans (sym eq)
                                                                                                (elim (λ {x y} x≡y → ∀ p →
                                                                                                         resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                                                                                                      body (from (to (refl x))) p)) $
                                                                                  cong-∘ (λ r → resp r p) to _ ⟩
    trans (sym $ cong (λ r → resp (to r) p) $ left-inverse-of (refl x))
          (elim (λ {x y} x≡y →
                   ∀ p → resp (_≃_.to ≡≃R x≡y) p ≡ subst P x≡y p)
                body (from (to (refl x))) p)                              ≡⟨ elim₁ (λ {q} eq → trans (sym $ cong (λ r → resp (to r) p) eq)
                                                                                                     (elim (λ {x y} x≡y → ∀ p →
                                                                                                              resp (_≃_.to ≡≃R x≡y) p ≡
                                                                                                              subst P x≡y p)
                                                                                                           body q p) ≡
                                                                                               trans (body x p)
                                                                                                     (sym $ cong (λ eq → subst P eq p) eq))
                                                                                   lemma
                                                                                   (left-inverse-of (refl x)) ⟩∎

    trans (body x p)
          (sym $ cong (λ eq → subst P eq p) (left-inverse-of (refl x)))   ∎

    where open _≃_ ≡≃R

  -- Simplification (?) lemma for transport-theorem.

  transport-theorem-≡⇒≃-refl :
    ∀ {p₁ p₂} (P : Type p₁ → Type p₂)
    (resp : ∀ {A B} → A ≃ B → P A → P B)
    (resp-id : ∀ {A} (p : P A) → resp Eq.id p ≡ p)
    (univ : Univalence p₁) {A} (p : P A) →
    transport-theorem P resp resp-id univ (≡⇒≃ (refl A)) p ≡
    trans (trans (trans (cong (λ eq → resp eq p) ≡⇒≃-refl)
                    (resp-id p))
             (sym $ subst-refl P p))
      (sym $ cong (λ eq → subst P eq p)
                  (_≃_.left-inverse-of (≡≃≃ univ) (refl A)))
  transport-theorem-≡⇒≃-refl P resp resp-id univ {A} p =
    transport-theorem′-refl P _≃_ (≡≃≃ univ) resp
      (λ _ p → trans (cong (λ eq → resp eq p) ≡⇒≃-refl) (resp-id p)) p

  -- A variant of resp-is-equivalence.

  resp-is-equivalence′ :
    ∀ {a p r} {A : Type a}
    (P : A → Type p) (R : A → A → Type r)
    (≡↠R : ∀ {x y} → (x ≡ y) ↠ R x y)
    (resp : ∀ {x y} → R x y → P x → P y) →
    (∀ x p → resp (_↠_.to ≡↠R (refl x)) p ≡ p) →
    ∀ {x y} (r : R x y) → Is-equivalence (resp r)
  resp-is-equivalence′ P R ≡↠R resp hyp r =
    Eq.respects-extensional-equality
      (λ p → sym $ transport-theorem′ P R ≡↠R resp hyp r p)
      (Eq.subst-is-equivalence P (_↠_.from ≡↠R r))

  -- A lemma relating ≃⇒≡, →-cong and cong₂.

  ≃⇒≡-→-cong :
    ∀ {ℓ} {A₁ A₂ B₁ B₂ : Type ℓ}
    (ext : Extensionality ℓ ℓ) →
    (univ : Univalence ℓ)
    (A₁≃A₂ : A₁ ≃ A₂) (B₁≃B₂ : B₁ ≃ B₂) →
    ≃⇒≡ univ (→-cong ext A₁≃A₂ B₁≃B₂) ≡
      cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂) (≃⇒≡ univ B₁≃B₂)
  ≃⇒≡-→-cong {A₂ = A₂} {B₁} ext univ A₁≃A₂ B₁≃B₂ =
    ≃⇒≡ univ (→-cong ext A₁≃A₂ B₁≃B₂)                        ≡⟨ cong (≃⇒≡ univ) (Eq.lift-equality ext lemma) ⟩

    ≃⇒≡ univ (≡⇒≃ (cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂)
                                         (≃⇒≡ univ B₁≃B₂)))  ≡⟨ left-inverse-of (≡≃≃ univ) _ ⟩∎

    cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂) (≃⇒≡ univ B₁≃B₂)  ∎
    where
    open _≃_

    lemma :
      (λ f → to B₁≃B₂ ∘ f ∘ from A₁≃A₂) ≡
      to (≡⇒≃ (cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂)
                                     (≃⇒≡ univ B₁≃B₂)))
    lemma =
      (λ f → to B₁≃B₂ ∘ f ∘ from A₁≃A₂)                  ≡⟨ apply-ext ext (λ _ → transport-theorem (λ B → A₂ → B) (λ A≃B g → _≃_.to A≃B ∘ g)
                                                                                                   refl univ B₁≃B₂ _) ⟩
      subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂) ∘
      (λ f → f ∘ from A₁≃A₂)                             ≡⟨ cong (_∘_ (subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂))) (apply-ext ext λ f →
                                                              transport-theorem (λ A → A → B₁) (λ A≃B g → g ∘ _≃_.from A≃B) refl univ A₁≃A₂ f) ⟩
      subst (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂) ∘
      subst (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)              ≡⟨ cong₂ (λ g h f → g (h f))
                                                              (apply-ext ext $ subst-in-terms-of-≡⇒↝ equivalence _ (λ B → A₂ → B))
                                                              (apply-ext ext $ subst-in-terms-of-≡⇒↝ equivalence _ (λ A → A → B₁)) ⟩
      to (≡⇒≃ (cong (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂))) ∘
      to (≡⇒≃ (cong (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)))    ≡⟨⟩

      to (≡⇒≃ (cong (λ B → A₂ → B) (≃⇒≡ univ B₁≃B₂)) ⊚
          ≡⇒≃ (cong (λ A → A → B₁) (≃⇒≡ univ A₁≃A₂)))    ≡⟨ cong to $ sym $ ≡⇒≃-trans ext _ _ ⟩∎

      to (≡⇒≃ (cong₂ (λ A B → A → B) (≃⇒≡ univ A₁≃A₂)
                                     (≃⇒≡ univ B₁≃B₂)))  ∎

  -- One can sometimes push cong through ≃⇒≡ (assuming
  -- extensionality).

  cong-≃⇒≡ :
    ∀ {ℓ p} {A B : Type ℓ} {A≃B : A ≃ B} →
    Extensionality p p →
    (univ₁ : Univalence ℓ)
    (univ₂ : Univalence p)
    (P : Type ℓ → Type p)
    (P-cong : ∀ {A B} → A ≃ B → P A ≃ P B) →
    (∀ {A} (p : P A) → _≃_.to (P-cong Eq.id) p ≡ p) →
    cong P (≃⇒≡ univ₁ A≃B) ≡ ≃⇒≡ univ₂ (P-cong A≃B)
  cong-≃⇒≡ {A≃B = A≃B} ext univ₁ univ₂ P P-cong P-cong-id =
    cong P (≃⇒≡ univ₁ A≃B)                    ≡⟨ sym $ _≃_.left-inverse-of (≡≃≃ univ₂) _ ⟩
    ≃⇒≡ univ₂ (≡⇒≃ (cong P (≃⇒≡ univ₁ A≃B)))  ≡⟨ cong (≃⇒≡ univ₂) $ Eq.lift-equality ext lemma ⟩∎
    ≃⇒≡ univ₂ (P-cong A≃B)                    ∎
    where
    lemma : ≡⇒→ (cong P (≃⇒≡ univ₁ A≃B)) ≡ _≃_.to (P-cong A≃B)
    lemma = apply-ext ext λ x →
      ≡⇒→ (cong P (≃⇒≡ univ₁ A≃B)) x  ≡⟨ sym $ subst-in-terms-of-≡⇒↝ equivalence _ P x ⟩
      subst P (≃⇒≡ univ₁ A≃B) x       ≡⟨ sym $ transport-theorem P (_≃_.to ∘ P-cong) P-cong-id univ₁ A≃B x ⟩∎
      _≃_.to (P-cong A≃B) x           ∎

  -- Any "resp" function that preserves identity also preserves
  -- compositions (assuming univalence and extensionality).

  resp-preserves-compositions :
    ∀ {p₁ p₂} (P : Type p₁ → Type p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    Univalence p₁ → Extensionality p₁ p₁ →
    ∀ {A B C} (A≃B : A ≃ B) (B≃C : B ≃ C) p →
    resp (B≃C ⊚ A≃B) p ≡ (resp B≃C ∘ resp A≃B) p
  resp-preserves-compositions P resp resp-id univ ext A≃B B≃C p =
    resp (B≃C ⊚ A≃B) p                                 ≡⟨ transport-theorem P resp resp-id univ _ _ ⟩
    subst P (≃⇒≡ univ (B≃C ⊚ A≃B)) p                   ≡⟨ cong (λ eq → subst P eq p) $ ≃⇒≡-∘ univ ext A≃B B≃C ⟩
    subst P (trans (≃⇒≡ univ A≃B) (≃⇒≡ univ B≃C)) p    ≡⟨ sym $ subst-subst P _ _ _ ⟩
    subst P (≃⇒≡ univ B≃C) (subst P (≃⇒≡ univ A≃B) p)  ≡⟨ sym $ transport-theorem P resp resp-id univ _ _ ⟩
    resp B≃C (subst P (≃⇒≡ univ A≃B) p)                ≡⟨ sym $ cong (resp _) $ transport-theorem P resp resp-id univ _ _ ⟩∎
    resp B≃C (resp A≃B p)                              ∎

  -- Any "resp" function that preserves identity also preserves
  -- inverses (assuming univalence and extensionality).

  resp-preserves-inverses :
    ∀ {p₁ p₂} (P : Type p₁ → Type p₂) →
    (resp : ∀ {A B} → A ≃ B → P A → P B) →
    (∀ {A} (p : P A) → resp Eq.id p ≡ p) →
    Univalence p₁ → Extensionality p₁ p₁ →
    ∀ {A B} (A≃B : A ≃ B) p q →
    resp A≃B p ≡ q → resp (inverse A≃B) q ≡ p
  resp-preserves-inverses P resp resp-id univ ext A≃B p q eq =
    let lemma =
          q                                     ≡⟨ sym eq ⟩
          resp A≃B p                            ≡⟨ transport-theorem P resp resp-id univ _ _ ⟩
          subst P (≃⇒≡ univ A≃B) p              ≡⟨ cong (λ eq → subst P eq p) $ sym $ sym-sym _ ⟩∎
          subst P (sym (sym (≃⇒≡ univ A≃B))) p  ∎
    in

    resp (inverse A≃B) q                                                 ≡⟨ transport-theorem P resp resp-id univ _ _ ⟩
    subst P (≃⇒≡ univ (inverse A≃B)) q                                   ≡⟨ cong (λ eq → subst P eq q) $ ≃⇒≡-inverse univ ext A≃B ⟩
    subst P (sym (≃⇒≡ univ A≃B)) q                                       ≡⟨ cong (subst P (sym (≃⇒≡ univ A≃B))) lemma ⟩
    subst P (sym (≃⇒≡ univ A≃B)) (subst P (sym (sym (≃⇒≡ univ A≃B))) p)  ≡⟨ subst-subst-sym P _ _ ⟩∎
    p                                                                    ∎

-- Equality preserves equivalences (assuming extensionality and
-- univalence).

≡-preserves-≃ :
  ∀ {ℓ₁ ℓ₂}
    {A₁ : Type ℓ₁} {A₂ : Type ℓ₂} {B₁ : Type ℓ₁} {B₂ : Type ℓ₂} →
  Extensionality (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
  Univalence′ A₁ B₁ →
  Univalence′ A₂ B₂ →
  A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ ≡ B₁) ≃ (A₂ ≡ B₂)
≡-preserves-≃ {ℓ₁} {ℓ₂} {A₁} {A₂} {B₁} {B₂}
              ext univ₁ univ₂ A₁≃A₂ B₁≃B₂ = Eq.↔⇒≃ (record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  })
  where
  to = λ A₁≡B₁ → ≃⇒≡ univ₂ (
    A₂  ↝⟨ inverse A₁≃A₂ ⟩
    A₁  ↝⟨ ≡⇒≃ A₁≡B₁ ⟩
    B₁  ↝⟨ B₁≃B₂ ⟩□
    B₂  □)

  from = λ A₂≡B₂ → ≃⇒≡ univ₁ (
    A₁  ↝⟨ A₁≃A₂ ⟩
    A₂  ↝⟨ ≡⇒≃ A₂≡B₂ ⟩
    B₂  ↝⟨ inverse B₁≃B₂ ⟩□
    B₁  □)

  abstract

    to∘from : ∀ eq → to (from eq) ≡ eq
    to∘from A₂≡B₂ =
      let ext₂ = lower-extensionality ℓ₁ ℓ₁ ext in

      _≃_.to (Eq.≃-≡ (≡≃≃ univ₂)) (Eq.lift-equality ext₂ (

        ≡⇒→ (≃⇒≡ univ₂ ((B₁≃B₂ ⊚ ≡⇒≃ (≃⇒≡ univ₁ ((inverse B₁≃B₂ ⊚
                             ≡⇒≃ A₂≡B₂) ⊚ A₁≃A₂))) ⊚ inverse A₁≃A₂))  ≡⟨ cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ₂) _ ⟩

        (_≃_.to B₁≃B₂ ∘
         ≡⇒→ (≃⇒≡ univ₁ ((inverse B₁≃B₂ ⊚ ≡⇒≃ A₂≡B₂) ⊚ A₁≃A₂)) ∘
         _≃_.from A₁≃A₂)                                              ≡⟨ cong (λ eq → _≃_.to B₁≃B₂ ∘ _≃_.to eq ∘ _≃_.from A₁≃A₂) $
                                                                           _≃_.right-inverse-of (≡≃≃ univ₁) _ ⟩
        ((_≃_.to B₁≃B₂ ∘ _≃_.from B₁≃B₂) ∘ ≡⇒→ A₂≡B₂ ∘
         (_≃_.to A₁≃A₂ ∘ _≃_.from A₁≃A₂))                             ≡⟨ cong₂ (λ f g → f ∘ ≡⇒→ A₂≡B₂ ∘ g)
                                                                               (apply-ext ext₂ $ _≃_.right-inverse-of B₁≃B₂)
                                                                               (apply-ext ext₂ $ _≃_.right-inverse-of A₁≃A₂) ⟩∎
        ≡⇒→ A₂≡B₂                                                     ∎))

    from∘to : ∀ eq → from (to eq) ≡ eq
    from∘to A₁≡B₁ =
      let ext₁ = lower-extensionality ℓ₂ ℓ₂ ext in

      _≃_.to (Eq.≃-≡ (≡≃≃ univ₁)) (Eq.lift-equality ext₁ (

        ≡⇒→ (≃⇒≡ univ₁ ((inverse B₁≃B₂ ⊚ ≡⇒≃ (≃⇒≡ univ₂ ((B₁≃B₂ ⊚
                             ≡⇒≃ A₁≡B₁) ⊚ inverse A₁≃A₂))) ⊚ A₁≃A₂))  ≡⟨ cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ₁) _ ⟩

        (_≃_.from B₁≃B₂ ∘
         ≡⇒→ (≃⇒≡ univ₂ ((B₁≃B₂ ⊚ ≡⇒≃ A₁≡B₁) ⊚ inverse A₁≃A₂)) ∘
         _≃_.to A₁≃A₂)                                                ≡⟨ cong (λ eq → _≃_.from B₁≃B₂ ∘ _≃_.to eq ∘ _≃_.to A₁≃A₂) $
                                                                           _≃_.right-inverse-of (≡≃≃ univ₂) _ ⟩
        ((_≃_.from B₁≃B₂ ∘ _≃_.to B₁≃B₂) ∘ ≡⇒→ A₁≡B₁ ∘
         (_≃_.from A₁≃A₂ ∘ _≃_.to A₁≃A₂))                             ≡⟨ cong₂ (λ f g → f ∘ ≡⇒→ A₁≡B₁ ∘ g)
                                                                               (apply-ext ext₁ $ _≃_.left-inverse-of B₁≃B₂)
                                                                               (apply-ext ext₁ $ _≃_.left-inverse-of A₁≃A₂) ⟩∎
        ≡⇒→ A₁≡B₁                                                     ∎))

-- Singletons expressed using equivalences instead of equalities,
-- where the types are required to live in the same universe, are
-- contractible (assuming univalence).

singleton-with-≃-contractible :
  ∀ {b} {B : Type b} →
  Univalence b →
  Contractible (∃ λ (A : Type b) → A ≃ B)
singleton-with-≃-contractible univ =
  H-level.respects-surjection
    (∃-cong λ _ → _≃_.surjection (≡≃≃ univ))
    0
    (singleton-contractible _)

other-singleton-with-≃-contractible :
  ∀ {a} {A : Type a} →
  Univalence a →
  Contractible (∃ λ (B : Type a) → A ≃ B)
other-singleton-with-≃-contractible univ =
  H-level.respects-surjection
    (∃-cong λ _ → _≃_.surjection (≡≃≃ univ))
    0
    (other-singleton-contractible _)

-- Singletons expressed using equivalences instead of equalities are
-- isomorphic to the unit type (assuming extensionality and
-- univalence).

singleton-with-≃-↔-⊤ :
  ∀ {a b} {B : Type b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Univalence (a ⊔ b) →
  (∃ λ (A : Type (a ⊔ b)) → A ≃ B) ↔ ⊤
singleton-with-≃-↔-⊤ {a} {B = B} ext univ =
  (∃ λ A → A ≃ B)      ↝⟨ inverse (∃-cong λ _ → Eq.≃-preserves-bijections ext F.id Bijection.↑↔) ⟩
  (∃ λ A → A ≃ ↑ a B)  ↔⟨ inverse (∃-cong λ _ → ≡≃≃ univ) ⟩
  (∃ λ A → A ≡ ↑ a B)  ↝⟨ _⇔_.to contractible⇔↔⊤ (singleton-contractible _) ⟩□
  ⊤                    □

other-singleton-with-≃-↔-⊤ :
  ∀ {a b} {A : Type a} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Univalence (a ⊔ b) →
  (∃ λ (B : Type (a ⊔ b)) → A ≃ B) ↔ ⊤
other-singleton-with-≃-↔-⊤ {b = b} {A} ext univ =
  (∃ λ B → A ≃ B)  ↝⟨ (∃-cong λ _ → Eq.inverse-isomorphism ext) ⟩
  (∃ λ B → B ≃ A)  ↝⟨ singleton-with-≃-↔-⊤ {a = b} ext univ ⟩□
  ⊤                □

-- Variants of the two lemmas above.

singleton-with-Π-≃-≃-⊤ :
  ∀ {a q} {A : Type a} {Q : A → Type q} →
  Extensionality a (lsuc q) →
  Univalence q →
  (∃ λ (P : A → Type q) → ∀ x → P x ≃ Q x) ≃ ⊤
singleton-with-Π-≃-≃-⊤ {a = a} {q = q} {A = A} {Q = Q} ext univ =
  (∃ λ (P : A → Type q) → ∀ x → P x ≃ Q x)  ↝⟨ (inverse $ ∃-cong λ _ → ∀-cong ext λ _ → ≡≃≃ univ) ⟩
  (∃ λ (P : A → Type q) → ∀ x → P x ≡ Q x)  ↝⟨ (∃-cong λ _ → Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (P : A → Type q) → P ≡ Q)            ↔⟨ _⇔_.to contractible⇔↔⊤ (singleton-contractible _) ⟩□
  ⊤                                         □

other-singleton-with-Π-≃-≃-⊤ :
  ∀ {a p} {A : Type a} {P : A → Type p} →
  Extensionality a (lsuc p) →
  Univalence p →
  (∃ λ (Q : A → Type p) → ∀ x → P x ≃ Q x) ≃ ⊤
other-singleton-with-Π-≃-≃-⊤ {a = a} {p = p} {A = A} {P = P} ext univ =
  (∃ λ (Q : A → Type p) → ∀ x → P x ≃ Q x)  ↝⟨ (inverse $ ∃-cong λ _ → ∀-cong ext λ _ → ≡≃≃ univ) ⟩
  (∃ λ (Q : A → Type p) → ∀ x → P x ≡ Q x)  ↝⟨ (∃-cong λ _ → Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (Q : A → Type p) → P ≡ Q)            ↔⟨ _⇔_.to contractible⇔↔⊤ (other-singleton-contractible _) ⟩□
  ⊤                                         □

-- ∃ Contractible is isomorphic to the unit type (assuming
-- extensionality and univalence).

∃Contractible↔⊤ :
  ∀ {a} →
  Extensionality a a →
  Univalence a →
  (∃ λ (A : Type a) → Contractible A) ↔ ⊤
∃Contractible↔⊤ ext univ =
  (∃ λ A → Contractible A)  ↝⟨ (∃-cong λ _ → contractible↔≃⊤ ext) ⟩
  (∃ λ A → A ≃ ⊤)           ↝⟨ singleton-with-≃-↔-⊤ ext univ ⟩
  ⊤                         □

-- If two types have a certain h-level, then the type of equalities
-- between these types also has the given h-level (assuming
-- extensionality and univalence).

H-level-H-level-≡ :
  ∀ {a} {A₁ A₂ : Type a} →
  Extensionality a a →
  Univalence′ A₁ A₂ →
  ∀ n → H-level n A₁ → H-level n A₂ → H-level n (A₁ ≡ A₂)
H-level-H-level-≡ {A₁ = A₁} {A₂} ext univ n = curry (
  H-level n A₁ × H-level n A₂  ↝⟨ uncurry (Eq.h-level-closure ext n) ⟩
  H-level n (A₁ ≃ A₂)          ↝⟨ H-level.respects-surjection (_≃_.surjection $ inverse $ ≡≃≃ univ) n ⟩
  H-level n (A₁ ≡ A₂)          □)

-- If a type has a certain positive h-level, then the types of
-- equalities between this type and other types also has the given
-- h-level (assuming extensionality and univalence).

H-level-H-level-≡ˡ :
  ∀ {a} {A₁ A₂ : Type a} →
  Extensionality a a →
  Univalence′ A₁ A₂ →
  ∀ n → H-level (1 + n) A₁ → H-level (1 + n) (A₁ ≡ A₂)
H-level-H-level-≡ˡ {A₁ = A₁} {A₂} ext univ n =
  H-level (1 + n) A₁         ↝⟨ Eq.left-closure ext n ⟩
  H-level (1 + n) (A₁ ≃ A₂)  ↝⟨ H-level.respects-surjection (_≃_.surjection $ inverse $ ≡≃≃ univ) (1 + n) ⟩
  H-level (1 + n) (A₁ ≡ A₂)  □

H-level-H-level-≡ʳ :
  ∀ {a} {A₁ A₂ : Type a} →
  Extensionality a a →
  Univalence′ A₁ A₂ →
  ∀ n → H-level (1 + n) A₂ → H-level (1 + n) (A₁ ≡ A₂)
H-level-H-level-≡ʳ {A₁ = A₁} {A₂} ext univ n =
  H-level (1 + n) A₂         ↝⟨ Eq.right-closure ext n ⟩
  H-level (1 + n) (A₁ ≃ A₂)  ↝⟨ H-level.respects-surjection (_≃_.surjection $ inverse $ ≡≃≃ univ) (1 + n) ⟩
  H-level (1 + n) (A₁ ≡ A₂)  □

-- ∃ λ A → H-level n A has h-level 1 + n (assuming extensionality and
-- univalence).

∃-H-level-H-level-1+ :
  ∀ {a} →
  Extensionality a a →
  Univalence a →
  ∀ n → H-level (1 + n) (∃ λ (A : Type a) → H-level n A)
∃-H-level-H-level-1+ ext univ n = ≡↔+ _ _ λ { (A₁ , h₁) (A₂ , h₂) →
                                     $⟨ h₁ , h₂ ⟩
  H-level n A₁ × H-level n A₂        ↝⟨ uncurry (H-level-H-level-≡ ext univ n) ⟩
  H-level n (A₁ ≡ A₂)                ↝⟨ H-level.respects-surjection
                                          (_↔_.surjection $ ignore-propositional-component
                                                              (H-level-propositional ext _)) n ⟩□
  H-level n ((A₁ , h₁) ≡ (A₂ , h₂))  □ }

-- ∃ λ A → Is-proposition A is a set (assuming extensionality and
-- propositional extensionality).

Is-set-∃-Is-proposition :
  ∀ {a} →
  Extensionality (lsuc a) (lsuc a) →
  Propositional-extensionality a →
  Is-set (∃ λ (A : Type a) → Is-proposition A)
Is-set-∃-Is-proposition {a} ext prop-ext
                        {x = A₁ , A₁-prop} {y = A₂ , A₂-prop} =
                                                    $⟨ _≃_.to (Propositional-extensionality-is-univalence-for-propositions ext)
                                                            prop-ext A₁-prop A₂-prop ⟩
  Univalence′ A₁ A₂                                 ↝⟨ (λ univ → H-level-H-level-≡ ext′ univ 1 A₁-prop A₂-prop) ⟩
  Is-proposition (A₁ ≡ A₂)                          ↝⟨ H-level.respects-surjection
                                                         (_↔_.surjection $ ignore-propositional-component
                                                                             (H-level-propositional ext′ 1)) 1 ⟩□
  Is-proposition ((A₁ , A₁-prop) ≡ (A₂ , A₂-prop))  □
  where
  ext′ = lower-extensionality _ _ ext

-- ∃ λ A → H-level n A does not in general have h-level n.
--
-- (Kraus and Sattler show that, for all n,
-- ∃ λ (A : Set (# n)) → H-level (2 + n) A does not have h-level
-- 2 + n, assuming univalence. See "Higher Homotopies in a Hierarchy
-- of Univalent Universes".)

¬-∃-H-level-H-level :
  ∀ {a} →
  ∃ λ n → ¬ H-level n (∃ λ (A : Type a) → H-level n A)
¬-∃-H-level-H-level =
  1 ,
  ( Is-proposition (∃ λ A → Is-proposition A)               ↔⟨⟩
    ((p q : ∃ λ A → Is-proposition A) → p ≡ q)              ↝⟨ (λ f p q → cong proj₁ (f p q)) ⟩
    ((p q : ∃ λ A → Is-proposition A) → proj₁ p ≡ proj₁ q)  ↝⟨ (_$ (⊥ , ⊥-propositional)) ∘
                                                               (_$ (↑ _ ⊤ , ↑-closure 1 (mono₁ 0 ⊤-contractible))) ⟩
    ↑ _ ⊤ ≡ ⊥                                               ↝⟨ flip (subst id) _ ⟩
    ⊥                                                       ↝⟨ ⊥-elim ⟩□
    ⊥₀                                                      □)

-- A certain type of uninhabited types is isomorphic to the unit type
-- (assuming extensionality and univalence).

∃¬↔⊤ :
  ∀ {a} →
  Extensionality a a →
  Univalence a →
  (∃ λ (A : Type a) → ¬ A) ↔ ⊤
∃¬↔⊤ ext univ =
  (∃ λ A → ¬ A)     ↔⟨ inverse (∃-cong λ _ → ≃⊥≃¬ ext) ⟩
  (∃ λ A → A ≃ ⊥₀)  ↔⟨ singleton-with-≃-↔-⊤ ext univ ⟩
  ⊤                 □

-- The following three proofs are taken from or variants of proofs in
-- "Higher Homotopies in a Hierarchy of Univalent Universes" by Kraus
-- and Sattler (Section 3).

-- There is a function which, despite having the same type, is not
-- equal to a certain instance of reflexivity (assuming extensionality
-- and univalence).

∃≢refl :
  Extensionality (# 1) (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Type₁) → ∃ λ (f : (x : A) → x ≡ x) → f ≢ refl
∃≢refl ext univ =
    (∃ λ (A : Type) → A ≡ A)
  , _↔_.from iso f
  , (_↔_.from iso f ≡ refl                                      ↝⟨ cong (_↔_.to iso) ⟩

     _↔_.to iso (_↔_.from iso f) ≡ _↔_.to iso refl              ↝⟨ (λ eq → f                            ≡⟨ sym (_↔_.right-inverse-of iso f) ⟩
                                                                           _↔_.to iso (_↔_.from iso f)  ≡⟨ eq ⟩∎
                                                                           _↔_.to iso refl              ∎) ⟩
     f ≡ _↔_.to iso refl                                        ↝⟨ cong (λ f → proj₁ (f Bool (swap-as-an-equality univ))) ⟩

     swap-as-an-equality univ ≡ proj₁ (_↔_.to iso refl Bool _)  ↝⟨ (λ eq → swap-as-an-equality univ        ≡⟨ eq ⟩
                                                                           proj₁ (_↔_.to iso refl Bool _)  ≡⟨ cong proj₁ Σ-≡,≡←≡-refl ⟩∎
                                                                           refl Bool                       ∎) ⟩

     swap-as-an-equality univ ≡ refl Bool                       ↝⟨ swap≢refl univ ⟩□

     ⊥                                                          □)
  where
  f = λ A p → p , refl (trans p p)

  iso =
    ((p : ∃ λ A → A ≡ A) → p ≡ p)                      ↝⟨ currying ⟩

    (∀ A (p : A ≡ A) → (A , p) ≡ (A , p))              ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                             inverse $ Bijection.Σ-≡,≡↔≡ {a = # 1}) ⟩
    ((A : Type) (p : A ≡ A) →
       ∃ λ (q : A ≡ A) → subst (λ A → A ≡ A) q p ≡ p)  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                             ∃-cong λ _ → ≡⇒↝ _ [subst≡]≡[trans≡trans]) ⟩□
    ((A : Type) (p : A ≡ A) →
       ∃ λ (q : A ≡ A) → trans p q ≡ trans q p)        □

-- The type (a : A) → a ≡ a is not necessarily a proposition (assuming
-- extensionality and univalence).

¬-type-of-refl-propositional :
  Extensionality (# 1) (# 1) →
  Univalence (# 0) →
  ∃ λ (A : Type₁) → ¬ Is-proposition ((a : A) → a ≡ a)
¬-type-of-refl-propositional ext univ =
  let A , f , f≢refl = ∃≢refl ext univ in
  A ,
  (Is-proposition (∀ x → x ≡ x)  ↝⟨ (λ irr → irr _ _) ⟩
   f ≡ refl                      ↝⟨ f≢refl ⟩□
   ⊥                             □)

-- Type₁ does not have h-level 3 (assuming extensionality and
-- univalence).

¬-Type₁-groupoid :
  Extensionality (# 1) (# 1) →
  Univalence (# 1) →
  Univalence (# 0) →
  ¬ H-level 3 Type₁
¬-Type₁-groupoid ext univ₁ univ₀ =
  let L = _ in

  H-level 3 Type₁                       ↝⟨ (λ h → h) ⟩
  Is-set (L ≡ L)                        ↝⟨ H-level.respects-surjection (_≃_.surjection $ ≡≃≃ univ₁) 2 ⟩
  Is-set (L ≃ L)                        ↝⟨ (λ h → h) ⟩
  Is-proposition (F.id ≡ F.id)          ↝⟨ H-level.respects-surjection (_≃_.surjection $ inverse $ Eq.≃-≡ $ Eq.↔⇒≃ Eq.≃-as-Σ) 1 ⟩
  Is-proposition ((id , _) ≡ (id , _))  ↝⟨ H-level.respects-surjection
                                             (_↔_.surjection $ inverse $ ignore-propositional-component (Eq.propositional ext id)) 1 ⟩
  Is-proposition (id ≡ id)              ↝⟨ H-level.respects-surjection (_≃_.surjection $ inverse $ Eq.extensionality-isomorphism ext) 1 ⟩
  Is-proposition ((l : L) → l ≡ l)      ↝⟨ proj₂ $ ¬-type-of-refl-propositional ext univ₀ ⟩□
  ⊥                                     □

-- For propositional types there is a split surjection from equality
-- to logical equivalence (assuming univalence).

≡↠⇔ : ∀ {ℓ} {A B : Type ℓ} →
      Univalence′ A B →
      Is-proposition A → Is-proposition B →
      (A ≡ B) ↠ (A ⇔ B)
≡↠⇔ {A = A} {B} univ A-prop B-prop =
  A ≡ B  ↔⟨ ≡≃≃ univ ⟩
  A ≃ B  ↝⟨ Eq.≃↠⇔ A-prop B-prop ⟩□
  A ⇔ B  □

-- For propositional types logical equivalence is isomorphic to
-- equality (assuming extensionality and univalence).

⇔↔≡ : ∀ {ℓ} {A B : Type ℓ} →
      Extensionality ℓ ℓ →
      Univalence′ A B →
      Is-proposition A → Is-proposition B →
      (A ⇔ B) ↔ (A ≡ B)
⇔↔≡ {A = A} {B} ext univ A-prop B-prop =
  A ⇔ B  ↝⟨ Eq.⇔↔≃ ext A-prop B-prop ⟩
  A ≃ B  ↔⟨ inverse $ ≡≃≃ univ ⟩□
  A ≡ B  □

-- A variant of the previous statement.

⇔↔≡′ : ∀ {ℓ} {A B : Proposition ℓ} →
       Extensionality ℓ ℓ →
       Univalence′ (proj₁ A) (proj₁ B) →
       (proj₁ A ⇔ proj₁ B) ↔ (A ≡ B)
⇔↔≡′ {A = A} {B} ext univ =
  proj₁ A ⇔ proj₁ B  ↝⟨ ⇔↔≡ ext univ (proj₂ A) (proj₂ B) ⟩
  proj₁ A ≡ proj₁ B  ↝⟨ ignore-propositional-component (H-level-propositional ext 1) ⟩□
  A ≡ B              □

-- A variant of the previous statement.

⇔↔≡″ : ∀ {ℓ} {A B : Proposition ℓ} →
       Extensionality (lsuc ℓ) (lsuc ℓ) →
       Propositional-extensionality ℓ →
       (proj₁ A ⇔ proj₁ B) ↔ (A ≡ B)
⇔↔≡″ {ℓ} {A} {B} ext =
  Propositional-extensionality ℓ   ↝⟨ (λ prop-ext → _≃_.to (Propositional-extensionality-is-univalence-for-propositions ext)
                                                           prop-ext (proj₂ A) (proj₂ B)) ⟩
  Univalence′ (proj₁ A) (proj₁ B)  ↝⟨ ⇔↔≡′ (lower-extensionality _ _ ext) ⟩□
  (proj₁ A ⇔ proj₁ B) ↔ (A ≡ B)    □

------------------------------------------------------------------------
-- Variants of J for equivalences

-- Two variants of the J rule for equivalences, along with
-- "computation" rules.
--
-- The types of the eliminators are similar to the statement of
-- Corollary 5.8.5 from the HoTT book (where the motive takes two type
-- arguments). The type and code of ≃-elim₁ are based on code from the
-- cubical library written by Matthew Yacavone, which was possibly
-- based on code written by Anders Mörtberg.

≃-elim₁ :
  ∀ {ℓ p} {A B : Type ℓ} →
  Univalence ℓ →
  (P : {A : Type ℓ} → A ≃ B → Type p) →
  P (Eq.id {A = B}) →
  (A≃B : A ≃ B) → P A≃B
≃-elim₁ univ P p A≃B =
  subst
    (λ (_ , A≃B) → P A≃B)
    (mono₁ 0 (singleton-with-≃-contractible univ) _ _)
    p

≃-elim₁-id :
  ∀ {ℓ p} {B : Type ℓ}
  (univ : Univalence ℓ)
  (P : {A : Type ℓ} → A ≃ B → Type p)
  (p : P (Eq.id {A = B})) →
  ≃-elim₁ univ P p Eq.id ≡ p
≃-elim₁-id univ P p =
  subst
    (λ (_ , A≃B) → P A≃B)
    (mono₁ 0 (singleton-with-≃-contractible univ) _ _)
    p                                                   ≡⟨ cong (λ eq → subst (λ (_ , A≃B) → P A≃B) eq _) $
                                                           mono₁ 1 (mono₁ 0 (singleton-with-≃-contractible univ)) _ _ ⟩

  subst (λ (_ , A≃B) → P A≃B) (refl _) p                ≡⟨ subst-refl _ _ ⟩∎

  p                                                     ∎

≃-elim¹ :
  ∀ {ℓ p} {A B : Type ℓ} →
  Univalence ℓ →
  (P : {B : Type ℓ} → A ≃ B → Type p) →
  P (Eq.id {A = A}) →
  (A≃B : A ≃ B) → P A≃B
≃-elim¹ univ P p A≃B =
  subst
    (λ (_ , A≃B) → P A≃B)
    (mono₁ 0 (other-singleton-with-≃-contractible univ) _ _)
    p

≃-elim¹-id :
  ∀ {ℓ p} {A : Type ℓ}
  (univ : Univalence ℓ)
  (P : {B : Type ℓ} → A ≃ B → Type p)
  (p : P (Eq.id {A = A})) →
  ≃-elim¹ univ P p Eq.id ≡ p
≃-elim¹-id univ P p =
  subst
    (λ (_ , A≃B) → P A≃B)
    (mono₁ 0 (other-singleton-with-≃-contractible univ) _ _)
    p                                                         ≡⟨ cong (λ eq → subst (λ (_ , A≃B) → P A≃B) eq _) $
                                                                 mono₁ 1 (mono₁ 0 (other-singleton-with-≃-contractible univ)) _ _ ⟩

  subst (λ (_ , A≃B) → P A≃B) (refl _) p                      ≡⟨ subst-refl _ _ ⟩∎

  p                                                           ∎
