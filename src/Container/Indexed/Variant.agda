------------------------------------------------------------------------
-- Another definition of indexed containers
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Container.Indexed.Variant
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

import Bijection eq as B
open import Container.Indexed eq as C
  using (_⇾_; id⇾; _∘⇾_; _∘⇾′_; Position; index)
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (_∘_)
open import H-level.Closure eq
open import Tactic.Sigma-cong eq
open import Univalence-axiom eq

private
  variable
    a ℓ p p₁ p₂ pos q : Level
    A I O             : Type a
    P Q R             : A → Type p
    ext f i k o s     : A

------------------------------------------------------------------------
-- Containers

-- Doubly indexed containers.

record Container₂
         (I : Type i) (O : Type o) s p :
         Type (i ⊔ o ⊔ lsuc (s ⊔ p)) where
  constructor _◁_
  field
    Shape    : O → Type s
    Position : ∀ {o} → Shape o → I → Type p

open Container₂ public

-- Singly indexed containers.

Container : Type i → ∀ s p → Type (i ⊔ lsuc (s ⊔ p))
Container I = Container₂ I I

private
  variable
    C : Container₂ I O s p

-- Container₂ can be expressed as a Σ-type.

Container≃Σ :
  Container₂ I O s p ≃
  (∃ λ (S : O → Type s) → ∀ {o} → S o → I → Type p)
Container≃Σ = Eq.↔→≃ (λ (S ◁ P) → S , P) (uncurry _◁_) refl refl

------------------------------------------------------------------------
-- Polynomial functors

-- The polynomial functor associated to a container.

⟦_⟧ :
  {I : Type i} {O : Type o} →
  Container₂ I O s p → (I → Type ℓ) → O → Type (ℓ ⊔ i ⊔ s ⊔ p)
⟦ S ◁ P ⟧ Q o = ∃ λ (s : S o) → P s ⇾ Q

-- A map function.

map : (C : Container₂ I O s p) → P ⇾ Q → ⟦ C ⟧ P ⇾ ⟦ C ⟧ Q
map C f _ (s , g) = s , f ∘⇾ g

-- Functor laws.

map-id : map C (id⇾ {P = P}) ≡ id⇾
map-id = refl _

map-∘ :
  (f : Q ⇾ R) (g : P ⇾ Q) →
  map C (f ∘⇾ g) ≡ map C f ∘⇾ map C g
map-∘ _ _ = refl _

-- A preservation lemma.

⟦⟧-cong :
  {I : Type i} {P₁ : I → Type p₁} {P₂ : I → Type p₂} →
  Extensionality? k (i ⊔ p) (p ⊔ p₁ ⊔ p₂) →
  (C : Container₂ I O s p) →
  (∀ i → P₁ i ↝[ k ] P₂ i) →
  (∀ o → ⟦ C ⟧ P₁ o ↝[ k ] ⟦ C ⟧ P₂ o)
⟦⟧-cong {i} {k} {p} {P₁ = Q₁} {P₂ = Q₂} ext (S ◁ P) Q₁↝Q₂ o =
  (∃ λ (s : S o) → P s ⇾ Q₁)  ↝⟨ (∃-cong λ _ →
                                  ∀-cong (lower-extensionality? k p lzero ext) λ _ →
                                  ∀-cong (lower-extensionality? k i p ext) λ _ →
                                  Q₁↝Q₂ _) ⟩□
  (∃ λ (s : S o) → P s ⇾ Q₂)  □

-- The forward direction of ⟦⟧-cong is an instance of map (at least
-- when k is equivalence).

_ : _≃_.to (⟦⟧-cong ext C f o) ≡ map C (_≃_.to ∘ f) o
_ = refl _

-- The shapes of a container are pointwise equivalent to the
-- polynomial functor of the container applied to the constant
-- function yielding the unit type.
--
-- (This lemma was suggested to me by an anonymous reviewer of a
-- paper.)

Shape≃⟦⟧⊤ :
  (C : Container₂ I O s p) →
  Shape C o ≃ ⟦ C ⟧ (λ _ → ⊤) o
Shape≃⟦⟧⊤ {o} (S ◁ P) =
  S o                                ↔⟨ inverse $ drop-⊤-right (λ _ → →-right-zero F.∘ inverse currying) ⟩□
  (∃ λ (s : S o) → ∀ i → P s i → ⊤)  □

-- A rearrangement lemma for cong, map and apply-ext.

cong-map-ext :
  {I : Type i} {O : Type o} {C : Container₂ I O s pos}
  {P : I → Type p} {Q : I → Type q}
  {f g : P ⇾ Q} {f≡g : ∀ i x → f i x ≡ g i x}
  (ext₁ : Extensionality i (p ⊔ q))
  (ext₂ : Extensionality p q)
  (ext₃ : Extensionality o (i ⊔ s ⊔ pos ⊔ p ⊔ q))
  (ext₄ : Extensionality (i ⊔ s ⊔ pos ⊔ p) (i ⊔ s ⊔ pos ⊔ q)) →
  (ext₅ : Extensionality i (pos ⊔ q)) →
  (ext₆ : Extensionality pos q) →
  cong (map C) (apply-ext ext₁ (apply-ext ext₂ ∘ f≡g)) ≡
  (apply-ext ext₃ λ _ → apply-ext ext₄ λ (s , h) →
   cong (s ,_) $ apply-ext ext₅ $ apply-ext ext₆ ∘ f≡g ∘⇾′ h)
cong-map-ext {C} {P} {f≡g} ext₁ ext₂ ext₃ ext₄ ext₅ ext₆ =
  cong (λ f _ (s , h) → s , f ∘⇾ h)
    (apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))               ≡⟨ sym $ ext-cong ext₃ ⟩

  (apply-ext ext₃ λ i →
   cong (λ f ((s , h) : ⟦ C ⟧ P i) → s , f ∘⇾ h) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))                 ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                              sym $ ext-cong ext₄) ⟩
  (apply-ext ext₃ λ i → apply-ext ext₄ λ (s , h) →
   cong (λ f → s , f ∘⇾ h) $
   apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))                 ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                              cong (apply-ext ext₄) $ apply-ext ext₄ λ (s , _) →
                                                              sym $ cong-∘ (s ,_) _ _) ⟩
  (apply-ext ext₃ λ i →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   cong (_∘⇾ h) $ apply-ext ext₁ (apply-ext ext₂ ∘ f≡g))  ≡⟨ (cong (apply-ext ext₃) $ apply-ext ext₃ λ _ →
                                                              cong (apply-ext ext₄) $ apply-ext ext₄ λ _ →
                                                              cong (cong _) $
                                                              C.cong-pre-∘⇾-ext ext₅ ext₁ ext₆ ext₂) ⟩∎
  (apply-ext ext₃ λ i →
   apply-ext ext₄ λ (s , h) → cong (s ,_) $
   apply-ext ext₅ (apply-ext ext₆ ∘ f≡g ∘⇾′ h))           ∎

------------------------------------------------------------------------
-- Conversion lemmas

-- A conversion lemma for Container. Note that the last index is not
-- unrestricted.

Container⇔Container :
  ∀ {I : Type i} {O : Type o} p →
  Container₂ I O s (i ⊔ p) ⇔ C.Container₂ I O s (i ⊔ p)
Container⇔Container {i = iℓ} {s} {I} {O} p =
  Container₂ I O s (iℓ ⊔ p)                 ↔⟨ Container≃Σ ⟩

  (∃ λ (S : O → Type s) →
   ∀ {o} → S o → I → Type (iℓ ⊔ p))         ↔⟨ (∃-cong λ _ →
                                                B.implicit-Π↔Π) ⟩
  (∃ λ (S : O → Type s) →
   ∀ o (s : S o) → I → Type (iℓ ⊔ p))       ↝⟨ (∃-cong λ _ → ∀-cong _ λ _ → ∀-cong _ λ _ →
                                                Pow⇔Fam p) ⟩
  (∃ λ (S : O → Type s) →
   ∀ o (s : S o) →
   ∃ λ (P : Type (iℓ ⊔ p)) → P → I)         ↝⟨ (∃-cong λ _ →
                                                from-bijection ΠΣ-comm F.∘
                                                ∀-cong _ λ _ → from-bijection ΠΣ-comm) ⟩
  (∃ λ (S : O → Type s) →
   ∃ λ (P : ∀ o → S o → Type (iℓ ⊔ p)) →
   ∀ o (s : S o) → P o s → I)               ↝⟨ (∃-cong λ _ → inverse $
                                                Σ-cong-refl {k₂ = logical-equivalence} B.implicit-Π↔Π λ _ →
                                                (∀-cong _ λ _ →
                                                 from-bijection B.implicit-Π↔Π) F.∘
                                                from-bijection B.implicit-Π↔Π) ⟩
  (∃ λ (S : O → Type s) →
   ∃ λ (P : ∀ {o} → S o → Type (iℓ ⊔ p)) →
   ∀ {o} {s : S o} → P s → I)               ↔⟨ inverse C.Container≃Σ ⟩□

  C.Container₂ I O s (iℓ ⊔ p)               □

-- Another conversion lemma for Container.

Container≃Container :
  ∀ {I : Type i} {O : Type o} p →
  Extensionality (i ⊔ o ⊔ s) (lsuc i ⊔ s ⊔ lsuc p) →
  Univalence (i ⊔ p) →
  Container₂ I O s (i ⊔ p) ≃ C.Container₂ I O s (i ⊔ p)
Container≃Container {i} {o} {s} {I} {O} p ext univ =
  Container₂ I O s (i ⊔ p)                 ↝⟨ Container≃Σ ⟩

  (∃ λ (S : O → Type s) →
   ∀ {o} → S o → I → Type (i ⊔ p))         ↔⟨ (∃-cong λ _ →
                                               B.implicit-Π↔Π) ⟩
  (∃ λ (S : O → Type s) →
   ∀ o (s : S o) → I → Type (i ⊔ p))       ↔⟨ (∃-cong λ _ →
                                               ∀-cong (lower-extensionality l r ext) λ _ →
                                               ∀-cong (lower-extensionality l r ext) λ _ →
                                               Pow↔Fam p (lower-extensionality l r ext) univ) ⟩
  (∃ λ (S : O → Type s) →
   ∀ o (s : S o) →
   ∃ λ (P : Type (i ⊔ p)) → P → I)         ↔⟨ (∃-cong λ _ →
                                               ΠΣ-comm F.∘
                                               ∀-cong (lower-extensionality l r ext) λ _ → ΠΣ-comm) ⟩
  (∃ λ (S : O → Type s) →
   ∃ λ (P : ∀ o → S o → Type (i ⊔ p)) →
   ∀ o (s : S o) → P o s → I)              ↝⟨ (∃-cong λ _ → inverse $
                                               Σ-cong-refl {k₂ = logical-equivalence} B.implicit-Π↔Π λ _ →
                                               (∀-cong _ λ _ →
                                                from-bijection B.implicit-Π↔Π) F.∘
                                               from-bijection B.implicit-Π↔Π) ⟩
  (∃ λ (S : O → Type s) →
   ∃ λ (P : ∀ {o} → S o → Type (i ⊔ p)) →
   ∀ {o} {s : S o} → P s → I)              ↝⟨ inverse C.Container≃Σ ⟩□

  C.Container₂ I O s (i ⊔ p)               □
  where
  l = i ⊔ o ⊔ s
  r = lsuc i ⊔ s ⊔ lsuc p

-- The two conversion lemmas for Container are related.

_ :
  {I : Type i} {univ : Univalence (i ⊔ p)} →
  _≃_.logical-equivalence
    (Container≃Container {I = I} {O = O} p ext univ) ≡
  Container⇔Container p
_ = refl _

-- A conversion lemma for ⟦_⟧.

⟦⟧≃⟦⟧ :
  ∀ p →
  {I : Type i} (C : Container₂ I O s (i ⊔ p)) {P : I → Type ℓ} →
  ∀ o →
  C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P o ≃ ⟦ C ⟧ P o
⟦⟧≃⟦⟧ _ {I} C {P} o =
  (∃ λ (s : Shape C o) → ((i , _) : Σ I (Position C s)) → P i)  ↔⟨ (∃-cong λ _ → currying) ⟩□
  (∃ λ (s : Shape C o) → (i : I) → Position C s i → P i)        □

-- Another conversion lemma for ⟦_⟧.

⟦⟧≃⟦⟧′ :
  ∀ p →
  {I : Type i} (C : C.Container₂ I O s (i ⊔ p)) {P : I → Type ℓ} →
  ∀ o →
  ⟦ _⇔_.from (Container⇔Container p) C ⟧ P o ↝[ i ⊔ p ∣ i ⊔ p ⊔ ℓ ]
  C.⟦ C ⟧ P o
⟦⟧≃⟦⟧′ {i} {ℓ} p {I} C {P} _ {k} ext =
  ∃-cong λ s →

  ((i : I) → (∃ λ (p : C .Position s) → C .index p ≡ i) → P i)     ↝⟨ (∀-cong (lower-extensionality? k l r ext) λ _ →
                                                                       from-bijection currying) ⟩

  ((i : I) (p : C .Position s) → C .index p ≡ i → P i)             ↔⟨ Π-comm ⟩

  ((p : C .Position s) (i : I) → C .index p ≡ i → P i)             ↝⟨ (∀-cong (lower-extensionality? k l r ext) λ _ →
                                                                       ∀-cong (lower-extensionality? k l r ext) λ _ →
                                                                       ∀-cong (lower-extensionality? k l r ext) λ eq →
                                                                       ≡⇒↝ _ $ cong P (sym eq)) ⟩

  ((p : C .Position s) (i : I) → C .index p ≡ i → P (C .index p))  ↝⟨ (∀-cong (lower-extensionality? k l r ext) λ _ →
                                                                       from-bijection $ inverse currying) ⟩
  ((p : C .Position s) → (∃ λ (i : I) → C .index p ≡ i) →
   P (C .index p))                                                 ↝⟨ (∀-cong (lower-extensionality? k l r ext) λ _ →
                                                                       drop-⊤-left-Π (lower-extensionality? k l r ext) $
                                                                       _⇔_.to contractible⇔↔⊤ $
                                                                       other-singleton-contractible _) ⟩□
  ((p : C .Position s) → P (C .index p))                           □
  where
  l = i ⊔ p
  r = i ⊔ p ⊔ ℓ

-- The map functions commute with ⟦⟧≃⟦⟧ (in a certain sense).

_ :
  map C f ∘⇾ (_≃_.to ∘ ⟦⟧≃⟦⟧ p C) ≡
  (_≃_.to ∘ ⟦⟧≃⟦⟧ p C) ∘⇾ C.map (_⇔_.to (Container⇔Container p) C) f
_ = refl _

-- The map functions commute with ⟦⟧≃⟦⟧′ (in a certain sense, assuming
-- extensionality).

map≡map′ :
  {I : Type i} {O : Type o} {P : I → Type p} {Q : I → Type q} →
  ∀ p′ →
  Extensionality (i ⊔ o ⊔ p ⊔ s ⊔ p′) (i ⊔ p ⊔ q ⊔ s ⊔ p′) →
  (C : C.Container₂ I O s (i ⊔ p′)) {f : P ⇾ Q} →
  C.map C f ∘⇾ (λ o → ⟦⟧≃⟦⟧′ p′ C o _) ≡
  (λ o → ⟦⟧≃⟦⟧′ p′ C o _) ∘⇾ map (_⇔_.from (Container⇔Container p′) C) f
map≡map′ {i} {o} {p} {q} {s} {P} {Q} p′ ext C {f} =
  apply-ext (lower-extensionality l r ext) λ _ →
  apply-ext (lower-extensionality l r ext) λ (_ , g) →
  cong (_ ,_) $
  apply-ext (lower-extensionality l r ext) λ p →
  let i = C .index p in

  f i (≡⇒↝ _ (cong P (sym (refl _))) (g i (p , refl _)))  ≡⟨ cong (λ eq → f i (≡⇒↝ _ eq (g i (p , refl _)))) $
                                                             trans (cong (cong P) sym-refl) $
                                                             cong-refl _ ⟩
  f i (≡⇒↝ _ (refl _) (g i (p , refl _)))                 ≡⟨ cong (f i) $ cong (_$ g i (p , refl _))
                                                             ≡⇒↝-refl ⟩
  f i (g i (p , refl _))                                  ≡⟨ cong (_$ f i (g i (p , refl _))) $ sym
                                                             ≡⇒↝-refl ⟩
  ≡⇒↝ _ (refl _) (f i (g i (p , refl _)))                 ≡⟨ cong (λ eq → ≡⇒↝ _ eq (f i (g i (p , refl _)))) $ sym $
                                                             trans (cong (cong Q) sym-refl) $
                                                             cong-refl _ ⟩∎
  ≡⇒↝ _ (cong Q (sym (refl _))) (f i (g i (p , refl _)))  ∎
  where
  l = i ⊔ o ⊔ p ⊔ s ⊔ p′
  r = i ⊔ p ⊔ q ⊔ s ⊔ p′
