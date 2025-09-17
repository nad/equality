------------------------------------------------------------------------
-- Algebras for indexed containers
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris, and partly based on "Non-wellfounded trees in
-- Homotopy Type Theory" by Ahrens, Capriotti and Spadotti.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Container.Indexed.Algebra
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (W)

open import Container.Indexed eq
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
open import Univalence-axiom eq

private
  variable
    a p q r s : Level
    A I O     : Type a
    i iℓ k x  : A
    C         : Container₂ I O s p

------------------------------------------------------------------------
-- Algebras

-- The type of algebras for a (singly indexed) container.

Algebra : {I : Type i} → Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Algebra {i} {s} {p} {I} C =
  ∃ λ (P : I → Type (i ⊔ s ⊔ p)) → ⟦ C ⟧ P ⇾ P

-- Algebra morphisms.

infix 4 _⇨_

_⇨_ :
  {I : Type i} {C : Container I s p} →
  Algebra C → Algebra C → Type (i ⊔ s ⊔ p)
(P , f) ⇨ (Q , g) = ∃ λ (h : P ⇾ Q) → h ∘⇾ f ≡ g ∘⇾ map _ h

private
  variable
    X Y Z : Algebra C

-- An identity morphism.

id⇨ : X ⇨ X
id⇨ = id⇾ , refl _

-- Composition for _⇨_.

infix 9 [_]_∘⇨_

[_]_∘⇨_ : ∀ Z → Y ⇨ Z → X ⇨ Y → X ⇨ Z
[_]_∘⇨_ {Y = _ , g} {X = _ , f} (_ , h) (f₁ , eq₁) (f₂ , eq₂) =
    f₁ ∘⇾ f₂
  , ((f₁ ∘⇾ f₂) ∘⇾ f              ≡⟨⟩
     f₁ ∘⇾ (f₂ ∘⇾ f)              ≡⟨ cong (f₁ ∘⇾_) eq₂ ⟩
     f₁ ∘⇾ (g ∘⇾ map _ f₂)        ≡⟨⟩
     (f₁ ∘⇾ g) ∘⇾ map _ f₂        ≡⟨ cong (_∘⇾ map _ f₂) eq₁ ⟩
     (h ∘⇾ map _ f₁) ∘⇾ map _ f₂  ≡⟨⟩
     h ∘⇾ map _ (f₁ ∘⇾ f₂)        ∎)

------------------------------------------------------------------------
-- Initial algebras

-- The property of being an initial algebra.

Initial :
  {I : Type i} {C : Container I s p} →
  Algebra C → Type (lsuc (i ⊔ s ⊔ p))
Initial X = ∀ Y → Contractible (X ⇨ Y)

-- A perhaps more traditional definition of what it means to be
-- initial.

Initial′ :
  {I : Type i} {C : Container I s p} →
  Algebra C → Type (lsuc (i ⊔ s ⊔ p))
Initial′ X =
  ∀ Y → ∃ λ (m : X ⇨ Y) → (m′ : X ⇨ Y) → proj₁ m ≡ proj₁ m′

-- Initial X implies Initial′ X.

Initial→Initial′ : (X : Algebra C) → Initial X → Initial′ X
Initial→Initial′ _ =
  ∀-cong _ λ _ → ∃-cong λ _ → ∀-cong _ λ _ → cong proj₁

-- Initial is pointwise propositional (assumption extensionality).

Initial-propositional :
  {I : Type i} {C : Container I s p} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  (X : Algebra C) →
  Is-proposition (Initial X)
Initial-propositional ext _ =
  Π-closure ext 1 λ _ →
  Contractible-propositional (lower-extensionality _ lzero ext)

-- Initial algebras.

Initial-algebra :
  {I : Type i} →
  Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Initial-algebra C = ∃ λ (X : Algebra C) → Initial X

-- Initial algebras, defined using Initial′.

Initial-algebra′ :
  {I : Type i} →
  Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Initial-algebra′ C = ∃ λ (X : Algebra C) → Initial′ X

-- Initial-algebra C implies Initial-algebra′ C.

Initial-algebra→Initial-algebra′ :
  Initial-algebra C → Initial-algebra′ C
Initial-algebra→Initial-algebra′ =
  ∃-cong Initial→Initial′

-- Carriers of initial algebras (defined using Initial′) for a given
-- container are pointwise equivalent.

carriers-of-initial-algebras-equivalent′ :
  (((P₁ , _) , _) ((P₂ , _) , _) : Initial-algebra′ C) →
  ∀ i → P₁ i ≃ P₂ i
carriers-of-initial-algebras-equivalent′
  (X₁ , initial₁) (X₂ , initial₂) i =
  Eq.↔→≃ (proj₁ to i) (proj₁ from i) to∘from from∘to
  where
  to : X₁ ⇨ X₂
  to = proj₁ (initial₁ X₂)

  from : X₂ ⇨ X₁
  from = proj₁ (initial₂ X₁)

  to∘from : ∀ x → proj₁ ([ X₂ ] to ∘⇨ from) i x ≡ x
  to∘from x =
    proj₁ ([ X₂ ] to ∘⇨ from) i x    ≡⟨ cong (λ f → f i x) $ sym $ proj₂ (initial₂ X₂) $ [ X₂ ] to ∘⇨ from ⟩
    proj₁ (proj₁ (initial₂ X₂)) i x  ≡⟨ cong (λ f → f i x) $ proj₂ (initial₂ X₂) id⇨ ⟩
    proj₁ (id⇨ {X = X₂}) i x         ≡⟨⟩
    x                                ∎

  from∘to : ∀ x → proj₁ ([ X₁ ] from ∘⇨ to) i x ≡ x
  from∘to x =
    proj₁ ([ X₁ ] from ∘⇨ to) i x    ≡⟨ cong (λ f → f i x) $ sym $ proj₂ (initial₁ X₁) $ [ X₁ ] from ∘⇨ to ⟩
    proj₁ (proj₁ (initial₁ X₁)) i x  ≡⟨ cong (λ f → f i x) $ proj₂ (initial₁ X₁) id⇨ ⟩
    proj₁ (id⇨ {X = X₁}) i x         ≡⟨⟩
    x                                ∎

-- The previous lemma relates the "in" functions of the two initial
-- algebras in a certain way.

in-related′ :
  {C : Container I s p}
  (F₁@((_ , in₁) , _) F₂@((_ , in₂) , _) : Initial-algebra′ C) →
  (_≃_.to ∘ carriers-of-initial-algebras-equivalent′ F₁ F₂) ∘⇾ in₁
    ≡
  in₂ ∘⇾ map C (_≃_.to ∘ carriers-of-initial-algebras-equivalent′ F₁ F₂)
in-related′ (_ , initial₁) (X₂ , _) =
  proj₂ (proj₁ (initial₁ X₂))

-- Carriers of initial algebras for a given container are pointwise
-- equivalent.

carriers-of-initial-algebras-equivalent :
  (((P₁ , _) , _) ((P₂ , _) , _) : Initial-algebra C) →
  ∀ i → P₁ i ≃ P₂ i
carriers-of-initial-algebras-equivalent =
  carriers-of-initial-algebras-equivalent′ on
    Initial-algebra→Initial-algebra′

-- The previous lemma relates the "in" functions of the two initial
-- algebras in a certain way.

in-related :
  {C : Container I s p}
  (F₁@((_ , in₁) , _) F₂@((_ , in₂) , _) : Initial-algebra C) →
  (_≃_.to ∘ carriers-of-initial-algebras-equivalent F₁ F₂) ∘⇾ in₁
    ≡
  in₂ ∘⇾ map C (_≃_.to ∘ carriers-of-initial-algebras-equivalent F₁ F₂)
in-related = in-related′ on Initial-algebra→Initial-algebra′

-- If X and Y are initial algebras (with initiality defined using
-- Initial′), then—assuming extensionality—initiality of X (defined
-- using Initial) is equivalent to initiality of Y.

Initial′→Initial≃Initial :
  {I : Type i} {C : Container I s p}
  ((X , _) (Y , _) : Initial-algebra′ C) →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Initial X ↝[ lsuc (i ⊔ s ⊔ p) ∣ i ⊔ s ⊔ p ] Initial Y
Initial′→Initial≃Initial {i} {s} {p} {C}
  ((X₁ , in₁) , initial₁) ((X₂ , in₂) , initial₂) ext {k} ext′ =
  ∀-cong ext′ λ Y@(_ , f) →
  H-level-cong
    (lower-extensionality? k _ lzero ext′)
    0
    (Σ-cong (lemma₂ Y) λ g →

       g ∘⇾ in₁ ≡ f ∘⇾ map C g                    ↝⟨ inverse $ Eq.≃-≡ (lemma₃ Y) ⟩

       _≃_.to (lemma₃ Y) (g ∘⇾ in₁) ≡
       _≃_.to (lemma₃ Y) (f ∘⇾ map C g)           ↔⟨⟩

       g ∘⇾ in₁ ∘⇾ map C (_≃_.from ∘ lemma₁) ≡
       f ∘⇾ map C g ∘⇾ map C (_≃_.from ∘ lemma₁)  ↝⟨ ≡⇒↝ _ $ cong (λ h → g ∘⇾ h ≡ f ∘⇾ map C g ∘⇾ map C (_≃_.from ∘ lemma₁)) $ sym $
                                                     in-related′ ((X₂ , in₂) , initial₂) ((X₁ , in₁) , initial₁) ⟩
       g ∘⇾ (_≃_.from ∘ lemma₁) ∘⇾ in₂ ≡
       f ∘⇾ map C g ∘⇾ map C (_≃_.from ∘ lemma₁)  ↔⟨⟩

       _≃_.to (lemma₂ Y) g ∘⇾ in₂ ≡
       f ∘⇾ map C (_≃_.to (lemma₂ Y) g)           □)
  where
  ext₁ = lower-extensionality (s ⊔ p) lzero ext
  ext₂ = lower-extensionality (i ⊔ s) lzero ext

  lemma₁ : ∀ i → X₁ i ≃ X₂ i
  lemma₁ =
    carriers-of-initial-algebras-equivalent′
      ((X₁ , in₁) , initial₁)
      ((X₂ , in₂) , initial₂)

  lemma₂ : ((Y , _) : Algebra C) → (X₁ ⇾ Y) ≃ (X₂ ⇾ Y)
  lemma₂ _ =
    ∀-cong ext₁ λ _ →
    →-cong ext (lemma₁ _) F.id

  lemma₃ : ((Y , _) : Algebra C) → (⟦ C ⟧ X₁ ⇾ Y) ≃ (⟦ C ⟧ X₂ ⇾ Y)
  lemma₃ _ =
    ∀-cong ext₁ λ _ →
    →-cong ext (⟦⟧-cong ext₂ C lemma₁ _) F.id

-- If there is an initial C-algebra, and we have Initial′ X for some
-- C-algebra X, then we also have Initial X (assuming extensionality).

Initial′→Initial :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Initial-algebra C →
  ((X , _) : Initial-algebra′ C) →
  Initial X
Initial′→Initial ext F₁@(_ , initial₁) F₂ =
  Initial′→Initial≃Initial
    (Initial-algebra→Initial-algebra′ F₁) F₂
    ext _ initial₁

-- Initial-algebra is pointwise propositional, assuming extensionality
-- and univalence.
--
-- This lemma is based on Lemma 5 from "Non-wellfounded trees in
-- Homotopy Type Theory". (That work might in turn be based partly on
-- "Inductive Types in Homotopy Type Theory" by Awodey, Gambino and
-- Sojakova.)

Initial-algebra-propositional :
  {I : Type i} {C : Container I s p} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (lsuc (i ⊔ s ⊔ p)) →
  Univalence (i ⊔ s ⊔ p) →
  Is-proposition (Initial-algebra C)
Initial-algebra-propositional {I} {C}
  ext univ F₁@((P₁ , in₁) , _) F₂@(X₂@(P₂ , in₂) , _) =
  block λ b →
  Σ-≡,≡→≡ (Σ-≡,≡→≡ (lemma₁ b) (lemma₂ b))
    (Initial-propositional (lower-extensionality lzero _ ext) X₂ _ _)
  where
  ext₁ = lower-extensionality _ lzero ext

  lemma₀ : Block "lemma₀" → ∀ i → P₁ i ≃ P₂ i
  lemma₀ ⊠ = carriers-of-initial-algebras-equivalent F₁ F₂

  lemma₀-lemma :
    ∀ b x →
    ((_≃_.to ∘ lemma₀ b) ∘⇾ in₁) i (map C (_≃_.from ∘ lemma₀ b) i x) ≡
    in₂ i x
  lemma₀-lemma {i} ⊠ x =
    ((_≃_.to ∘ lemma₀ ⊠) ∘⇾ in₁) i (map C (_≃_.from ∘ lemma₀ ⊠) i x)  ≡⟨ cong (λ f → f _ (map C (_≃_.from ∘ lemma₀ ⊠) i x)) $
                                                                         in-related F₁ F₂ ⟩
    (in₂ ∘⇾ map C (_≃_.to ∘ lemma₀ ⊠))
      i (map C (_≃_.from ∘ lemma₀ ⊠) i x)                             ≡⟨⟩

    in₂ i (map C ((_≃_.to ∘ lemma₀ ⊠) ∘⇾ (_≃_.from ∘ lemma₀ ⊠)) i x)  ≡⟨ (cong (λ m → in₂ i (map C m i x)) $
                                                                          apply-ext (lower-extensionality _ _ ext) λ i →
                                                                          apply-ext (lower-extensionality _ _ ext) $
                                                                          _≃_.right-inverse-of (lemma₀ ⊠ i)) ⟩
    in₂ i (map {P = P₂} C id⇾ i x)                                    ≡⟨⟩

    in₂ i x                                                           ∎

  lemma₁ : Block "lemma₀" → P₁ ≡ P₂
  lemma₁ b =
    apply-ext ext₁ λ i →
    ≃⇒≡ univ (lemma₀ b i)

  lemma₁-lemma₁ = λ (@ω b i) →
    sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (subst-const _)   ≡⟨ cong sym Σ-≡,≡→≡-subst-const-refl ⟩
    sym $ cong₂ _,_ (sym (lemma₁ b)) (refl _)        ≡⟨ sym cong₂-sym ⟩
    cong₂ _,_ (sym (sym (lemma₁ b))) (sym (refl _))  ≡⟨ cong₂ (cong₂ _) (sym-sym _) sym-refl ⟩
    cong₂ _,_ (lemma₁ b) (refl i)                    ≡⟨ cong₂-reflʳ _ ⟩∎
    cong (_, i) (lemma₁ b)                           ∎

  lemma₁-lemma₂ = λ (@ω b i x) →
    subst (_$ i) (lemma₁ b) x                                    ≡⟨⟩
    subst (_$ i) (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i)) x  ≡⟨ subst-ext ext₁ ⟩
    subst id (≃⇒≡ univ (lemma₀ b i)) x                           ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩
    _≃_.to (≡⇒≃ (≃⇒≡ univ (lemma₀ b i))) x                       ≡⟨ cong (λ eq → _≃_.to eq _) $
                                                                    _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.to (lemma₀ b i) x                                        ∎

  lemma₁-lemma₃ = λ (@ω b _ _ f p) →
    subst (λ P → P (index C p)) (sym (lemma₁ b)) (f p)          ≡⟨⟩

    subst (λ P → P (index C p))
      (sym (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i))) (f p)  ≡⟨ cong (flip (subst _) _) $ sym $ ext-sym ext₁ ⟩

    subst (λ P → P (index C p))
      (apply-ext ext₁ λ i → sym (≃⇒≡ univ (lemma₀ b i))) (f p)  ≡⟨ subst-ext ext₁ ⟩

    subst id (sym (≃⇒≡ univ (lemma₀ b (index C p)))) (f p)      ≡⟨ subst-id-in-terms-of-inverse∘≡⇒↝ equivalence ⟩

    _≃_.from (≡⇒≃ (≃⇒≡ univ (lemma₀ b (index C p)))) (f p)      ≡⟨ cong (λ eq → _≃_.from eq _) $
                                                                   _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.from (lemma₀ b (index C p)) (f p)                       ∎

  lemma₁-lemma₄ = λ (@ω b i x@(s , f)) →
    subst (λ P → ⟦ C ⟧ P i) (sym (lemma₁ b)) x                           ≡⟨⟩

    subst (λ P → ∃ λ (s : Shape C i) → ∀ p → P (index C p))
      (sym (lemma₁ b)) x                                                 ≡⟨ push-subst-pair-× _ _ ⟩

    s ,
    subst (λ P → (p : Position C s) → P (index C p)) (sym (lemma₁ b)) f  ≡⟨ (cong (s ,_) $ apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                             push-subst-application _ _) ⟩

    s , (λ {x} → subst (λ P → P (index C x)) (sym (lemma₁ b))) ∘ f       ≡⟨ (cong (s ,_) $ apply-ext (lower-extensionality _ _ ext) $
                                                                             lemma₁-lemma₃ b i x f) ⟩
    s , (λ {x} → _≃_.from (lemma₀ b (index C x))) ∘ f                    ≡⟨⟩

    map C (_≃_.from ∘ lemma₀ b) i x                                      ∎

  lemma₂ = λ (@ω b) →
    apply-ext (lower-extensionality _ _ ext) λ i →
    apply-ext (lower-extensionality _ _ ext) λ x →

    subst (λ P → ⟦ C ⟧ P ⇾ P) (lemma₁ b) in₁ i x                   ≡⟨⟩

    subst (λ P → ∀ i → ⟦ C ⟧ P i → P i) (lemma₁ b) in₁ i x         ≡⟨ cong (_$ x) subst-∀ ⟩

    subst (uncurry λ P i → ⟦ C ⟧ P i → P i)
      (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (refl _))
      (in₁ (subst (λ _ → I) (sym (lemma₁ b)) i)) x                 ≡⟨ elim¹
                                                                        (λ {i′} eq →
                                                                           subst (uncurry λ P i → ⟦ C ⟧ P i → P i)
                                                                             (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (refl _))
                                                                             (in₁ (subst (λ _ → I) (sym (lemma₁ b)) i)) x ≡
                                                                           subst (uncurry λ P i → ⟦ C ⟧ P i → P i)
                                                                             (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) eq)
                                                                             (in₁ i′) x)
                                                                        (refl _)
                                                                        _ ⟩
    subst (uncurry λ P i → ⟦ C ⟧ P i → P i)
      (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (subst-const _))
      (in₁ i) x                                                    ≡⟨ cong (λ eq → subst (uncurry λ P i → ⟦ C ⟧ P i → P i) eq _ _) $
                                                                       lemma₁-lemma₁ b i ⟩
    subst (uncurry λ P i → ⟦ C ⟧ P i → P i)
      (cong (_, _) (lemma₁ b))
      (in₁ i) x                                                    ≡⟨ cong (_$ x) $ sym $ subst-∘ _ _ _ ⟩

    subst (λ P → ⟦ C ⟧ P i → P i) (lemma₁ b) (in₁ i) x             ≡⟨ subst-→ ⟩

    subst (_$ i) (lemma₁ b)
      (in₁ i (subst (λ P → ⟦ C ⟧ P i) (sym (lemma₁ b)) x))         ≡⟨ lemma₁-lemma₂ b i _ ⟩

    _≃_.to (lemma₀ b i)
      (in₁ i (subst (λ P → ⟦ C ⟧ P i) (sym (lemma₁ b)) x))         ≡⟨ cong (_≃_.to (lemma₀ b i) ∘ in₁ i) $ lemma₁-lemma₄ b i x ⟩

    _≃_.to (lemma₀ b i) (in₁ i (map C (_≃_.from ∘ lemma₀ b) i x))  ≡⟨ lemma₀-lemma b x ⟩∎

    in₂ i x                                                        ∎

------------------------------------------------------------------------
-- W-types

-- A W-type for a given container.

record W {I : Type iℓ} (C : Container I s p) (i : I) :
         Type (iℓ ⊔ s ⊔ p) where
  inductive
  pattern
  constructor in-W
  field
    out-W : ⟦ C ⟧ (W C) i

open W public

-- An η-law.

η : in-W (out-W x) ≡ x
η {x = in-W _} = refl _

-- W C is, in a certain sense, a fixpoint of ⟦ C ⟧.

W-fixpoint : ⟦ C ⟧ (W C) i ≃ W C i
W-fixpoint = Eq.↔→≃ in-W out-W (λ _ → η) refl

-- An algebra defined using W and out-W.

W-algebra : (C : Container I s p) → Algebra C
W-algebra C = W C , λ _ → in-W

-- "Fold" functions for W.

fold : ((P , _) : Algebra C) → W C ⇾ P
fold {C} X@(_ , f) _ (in-W (s , g)) =
  f _ (s , λ p → fold X (index C p) (g p))

-- "Fold" morphisms for W.

fold⇨ : (X : Algebra C) → W-algebra C ⇨ X
fold⇨ X = fold X , refl _

-- W-algebra C is an initial algebra (assuming extensionality).

W-initial :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Initial (W-algebra C)
W-initial {i} {s} {p} {C} ext X@(P , f) =
  fold⇨ X , unique
  where
  ext₁ : Extensionality p (i ⊔ s ⊔ p)
  ext₁ = lower-extensionality (i ⊔ s) lzero ext

  ext₂ : Extensionality i (i ⊔ s ⊔ p)
  ext₂ = lower-extensionality (s ⊔ p) lzero ext

  unique⇾ : ∀ ((g , _) : W-algebra C ⇨ X) i x → fold X i x ≡ g i x
  unique⇾ m@(g , eq) i (in-W x@(s , h)) =
    (f ∘⇾ map C (fold X)) i x                 ≡⟨⟩
    f i (s , λ p → fold X (index C p) (h p))  ≡⟨ (cong (f i ∘ (s ,_)) $ apply-ext ext₁ λ p → unique⇾ m _ (h p)) ⟩
    f i (s , λ p → g (index C p) (h p))       ≡⟨⟩
    (f ∘⇾ map C g) i x                        ≡⟨ cong (λ f → f i x) $ sym eq ⟩∎
    g i (in-W x)                              ∎

  unique : (m : W-algebra C ⇨ X) → fold⇨ X ≡ m
  unique m@(_ , eq) = Σ-≡,≡→≡
    lemma₁
    (subst (λ h → h ∘⇾ (λ _ → in-W) ≡ f ∘⇾ map C h) lemma₁ (refl _)    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

     trans (sym (cong (_∘⇾ (λ _ → in-W)) lemma₁))
       (trans (refl _) (cong ((f ∘⇾_) ∘ map C) lemma₁))                ≡⟨ cong (trans _) $
                                                                          trans-reflˡ _ ⟩
     trans (sym (cong (_∘⇾ (λ _ → in-W)) lemma₁))
       (cong ((f ∘⇾_) ∘ map C) lemma₁)                                 ≡⟨ cong₂ (trans ∘ sym)
                                                                            (cong-pre-∘⇾-ext ext₂ ext₂ ext ext)
                                                                            lemma₂ ⟩
     trans (sym lemma₁′)
       (trans lemma₁′
          (apply-ext ext₂ λ i → apply-ext ext λ x →
           cong (λ f → f i x) eq))                                     ≡⟨ trans-sym-[trans] _ _ ⟩

     (apply-ext ext₂ λ i → apply-ext ext λ x → cong (λ f → f i x) eq)  ≡⟨ trans (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ → ext-cong ext) $
                                                                          ext-cong ext₂ ⟩

     cong (λ f i x → f i x) eq                                         ≡⟨ sym $ cong-id _ ⟩∎

     eq                                                                ∎)
    where
    lemma₁  = apply-ext ext₂ λ i → apply-ext ext λ x → unique⇾ m i x
    lemma₁′ =
      apply-ext ext₂ λ i → apply-ext ext λ x → unique⇾ m i (in-W x)

    lemma₂ =
      cong ((f ∘⇾_) ∘ map C) lemma₁                                       ≡⟨ sym $ cong-∘ _ _ _ ⟩

      cong (f ∘⇾_) (cong (map C) lemma₁)                                  ≡⟨ cong (cong _) $ cong-map-ext ext₂ ext ext₂ ext ext₁ ⟩

      (cong (f ∘⇾_) $ apply-ext ext₂ $ apply-ext ext ∘ λ _ (s , h) →
       cong (s ,_) $ apply-ext ext₁ λ p → unique⇾ m (index C p) (h p))    ≡⟨ cong-post-∘⇾-ext ext₂ ext₂ ext ext ⟩

      apply-ext ext₂
        (apply-ext ext ∘ (λ i _ → cong (f i)) ∘⇾″ λ _ (s , h) →
         cong (s ,_) $ apply-ext ext₁ λ p → unique⇾ m (index C p) (h p))  ≡⟨⟩

      (apply-ext ext₂ λ i → apply-ext ext λ (s , h) →
       cong (f i) $ cong (s ,_) $
       apply-ext ext₁ λ p → unique⇾ m (index C p) (h p))                  ≡⟨ (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ →
                                                                              cong (apply-ext ext) $ apply-ext ext λ _ →
                                                                              trans (cong-∘ _ _ _) $
                                                                              trans (sym $ trans-[trans]-sym _ _) $
                                                                              cong (trans _) $
                                                                              trans (sym $ cong-sym _ _) $
                                                                              cong (cong _) $ sym-sym _) ⟩
      (apply-ext ext₂ λ i → apply-ext ext λ x →
       trans (unique⇾ m i (in-W x)) (cong (λ f → f i x) eq))              ≡⟨ trans (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ →
                                                                                    ext-trans ext) $
                                                                             ext-trans ext₂ ⟩∎
      (trans lemma₁′ $
       apply-ext ext₂ λ i → apply-ext ext λ x → cong (λ f → f i x) eq)    ∎

-- An initial algebra constructed using W.

W-initial-algebra :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Initial-algebra C
W-initial-algebra ext = W-algebra _ , W-initial ext

------------------------------------------------------------------------
-- Lemmas related to lift-positions

-- The definition of algebras is not affected by lift-positions (up to
-- pointwise equivalence, assuming extensionality).

Algebra≃Algebra-lift-positions :
  {I : Type i} {C : Container I s p} →
  Extensionality? ⌊ k ⌋-sym (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Algebra C ↝[ ⌊ k ⌋-sym ] Algebra (lift-positions C)
Algebra≃Algebra-lift-positions {s} {p} {k} {C} ext =
  (∃ λ P → ⟦                C ⟧ P ⇾ P)  ↝⟨ (∃-cong λ P →
                                            ∀-cong (lower-extensionality? ⌊ k ⌋-sym (s ⊔ p) lzero ext) λ _ →
                                            →-cong₁ ext $
                                            ⟦⟧≃⟦lift-positions⟧ C P) ⟩□
  (∃ λ P → ⟦ lift-positions C ⟧ P ⇾ P)  □

-- The definition of algebra morphisms is not affected by
-- lift-positions (in a certain sense, assuming extensionality).

⇨≃⇨-lift-positions :
  {I : Type i} {C : Container I s p}
  (ext : Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p)) →
  (X Y : Algebra C) →
  (X ⇨ Y) ≃
  (_≃_.to (Algebra≃Algebra-lift-positions ext) X ⇨
   _≃_.to (Algebra≃Algebra-lift-positions ext) Y)
⇨≃⇨-lift-positions {s} {p} {C} ext (P , f) (Q , g) =
  (∃ λ (h : P ⇾ Q) → h ∘⇾ f ≡ g ∘⇾ map _ h)      ↝⟨ (∃-cong λ _ → inverse $
                                                     Eq.≃-≡ $
                                                     ∀-cong (lower-extensionality (s ⊔ p) lzero ext) λ _ →
                                                     →-cong₁ ext $
                                                     ⟦⟧≃⟦lift-positions⟧ C P) ⟩□
  (∃ λ (h : P ⇾ Q) →
     (_∘ Σ-map id (_∘ lift)) ∘ (h ∘⇾ f) ≡
     (_∘ Σ-map id (_∘ lift)) ∘ (g ∘⇾ map _ h))  □

-- One definition of initiality is not affected by lift-positions (in
-- a certain sense, assuming extensionality).

Initial≃Initial-lift-positions :
  {I : Type i} {C : Container I s p} {X : Algebra C} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Initial {C = C} X ≃
  Initial {C = lift-positions C}
    (_⇔_.to (Algebra≃Algebra-lift-positions _) X)
Initial≃Initial-lift-positions ext =
  Π-cong ext
    (Algebra≃Algebra-lift-positions {k = equivalence} ext′) λ Y →
  H-level-cong ext′ 0 (⇨≃⇨-lift-positions ext′ _ Y)
  where
  ext′ = lower-extensionality _ lzero ext

-- The other definition of initiality is not affected by
-- lift-positions (in a certain sense, assuming extensionality).

Initial′≃Initial′-lift-positions :
  {I : Type i} {C : Container I s p} {X : Algebra C} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Initial′ {C = C} X ≃
  Initial′ {C = lift-positions C}
    (_⇔_.to (Algebra≃Algebra-lift-positions _) X)
Initial′≃Initial′-lift-positions ext =
  Π-cong ext
    (Algebra≃Algebra-lift-positions {k = equivalence} ext′) λ Y →
  Σ-cong (⇨≃⇨-lift-positions ext′ _ Y) λ _ →
  Π-cong ext′ (⇨≃⇨-lift-positions ext′ _ Y) λ _ →
  F.id
  where
  ext′ = lower-extensionality _ lzero ext

-- The definition of Initial-algebra is not affected by lift-positions
-- (in a certain sense, assuming extensionality).

Initial-algebra≃Initial-algebra-lift-positions :
  {I : Type i} {C : Container I s p} {X : Algebra C} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Initial-algebra C ≃
  Initial-algebra (lift-positions C)
Initial-algebra≃Initial-algebra-lift-positions ext =
  Σ-cong (Algebra≃Algebra-lift-positions {k = equivalence} ext′) λ _ →
  Initial≃Initial-lift-positions ext
  where
  ext′ = lower-extensionality _ lzero ext

-- The definition of Initial-algebra′ is not affected by
-- lift-positions (in a certain sense, assuming extensionality).

Initial-algebra′≃Initial-algebra′-lift-positions :
  {I : Type i} {C : Container I s p} {X : Algebra C} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Initial-algebra′ C ≃
  Initial-algebra′ (lift-positions C)
Initial-algebra′≃Initial-algebra′-lift-positions ext =
  Σ-cong (Algebra≃Algebra-lift-positions {k = equivalence} ext′) λ _ →
  Initial′≃Initial′-lift-positions ext
  where
  ext′ = lower-extensionality _ lzero ext

-- Lifting the position type family using lift-positions does not
-- affect the resulting W-type (up to pointwise equivalence, assuming
-- extensionality).

W≃W-lift-positions :
  ∀ {I : Type iℓ} {C : Container I s p} {i} →
  W C i ↝[ iℓ ⊔ p ∣ iℓ ⊔ s ⊔ p ] W (lift-positions C) i
W≃W-lift-positions {iℓ} {s} {p} {C} =
  generalise-ext?
    (record { to = to; from = from })
    (λ ext →
         to-from ext
       , from-to (lower-extensionality iℓ lzero ext))
  where
  to : W C i → W (lift-positions C) i
  to (in-W (s , f)) = in-W (s , λ (lift p) → to (f p))

  from : W (lift-positions C) i → W C i
  from (in-W (s , f)) = in-W (s , λ p → from (f (lift p)))

  to-from :
    Extensionality (iℓ ⊔ p) (iℓ ⊔ s ⊔ p) →
    (x : W (lift-positions C) i) → to (from x) ≡ x
  to-from ext (in-W (s , f)) =
    cong (in-W ∘ (s ,_)) $ apply-ext ext λ p → to-from ext (f p)

  from-to :
    Extensionality p (iℓ ⊔ s ⊔ p) →
    (x : W C i) → from (to x) ≡ x
  from-to ext (in-W (s , f)) =
    cong (in-W ∘ (s ,_)) $ apply-ext ext λ p → from-to ext (f p)

-- W-algebra C is related to W-algebra (lift-positions C) (assuming
-- extensionality and univalence).

≡W-algebra-lift-positions :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (lsuc (i ⊔ s ⊔ p)) →
  Univalence (i ⊔ s ⊔ p) →
  _⇔_.to (Algebra≃Algebra-lift-positions _) (W-algebra C) ≡
  W-algebra (lift-positions C)
≡W-algebra-lift-positions {i} {s} {p} {C} ext univ =
  Σ-≡,≡→≡
    (apply-ext ext′ lemma)
    (apply-ext (lower-extensionality (s ⊔ p) _ ext) λ i →
     apply-ext (lower-extensionality lzero   _ ext) λ x@(s , f) →

     let lemma′ =
           subst (λ P → ⟦ lift-positions C ⟧ P i)
             (sym (apply-ext ext′ lemma)) x                              ≡⟨ elim₁
                                                                              (λ eq →
                                                                                 subst (λ P → ⟦ lift-positions C ⟧ P i) (sym eq) x ≡
                                                                                 (s , _≃_.from (≡⇒≃ $ ext⁻¹ eq _) ∘ f))
                                                                              (
             subst (λ P → ⟦ lift-positions C ⟧ P i) (sym (refl _)) x           ≡⟨ trans (cong (flip (subst _) _) sym-refl) $
                                                                                  subst-refl _ _ ⟩

             x                                                                 ≡⟨ (cong (s ,_) $ apply-ext ext″ λ _ →
                                                                                   cong (λ eq → _≃_.from eq _) $ sym
                                                                                   ≡⇒≃-refl) ⟩

             s , _≃_.from (≡⇒≃ $ refl _) ∘ f                                   ≡⟨ (cong (s ,_) $ apply-ext ext″ λ _ →
                                                                                   cong (λ eq → _≃_.from (≡⇒≃ eq) (f _)) $ sym $
                                                                                   ext⁻¹-refl _) ⟩∎
             s ,
             _≃_.from (≡⇒≃ $ ext⁻¹ (refl (W (lift-positions C))) _) ∘ f        ∎)
                                                                              _ ⟩

           s , _≃_.from (≡⇒≃ $ ext⁻¹ (apply-ext ext′ lemma) _) ∘ f       ≡⟨ (cong (s ,_) $ apply-ext ext″ λ _ →
                                                                             cong (λ (eq : ∀ i → W C i ≡ W (lift-positions C) i) →
                                                                                     _≃_.from (≡⇒≃ (eq _)) (f _)) $
                                                                             _≃_.left-inverse-of (Eq.extensionality-isomorphism ext′) _) ⟩

           s , _≃_.from (≡⇒≃ $ lemma _) ∘ f                              ≡⟨ (cong (s ,_) $ apply-ext ext″ λ _ → cong (λ eq → _≃_.from eq (f _)) $
                                                                             _≃_.right-inverse-of (≡≃≃ univ) _) ⟩∎
           s , _⇔_.from (W≃W-lift-positions _) ∘ f                       ∎
     in

     subst (λ P → ⟦ lift-positions C ⟧ P ⇾ P)
       (apply-ext ext′ lemma)
       (λ _ (s , f) → in-W (s , f ∘ lift))
       i x                                                               ≡⟨ cong (_$ x) $ sym $
                                                                            push-subst-application _ _ ⟩
     subst (λ P → ⟦ lift-positions C ⟧ P i → P i)
       (apply-ext ext′ lemma)
       (λ (s , f) → in-W (s , f ∘ lift))
       x                                                                 ≡⟨ subst-→ ⟩

     subst (_$ i)
       (apply-ext ext′ lemma)
       (let s , f =
              subst (λ P → ⟦ lift-positions C ⟧ P i)
                (sym (apply-ext ext′ lemma)) x
        in in-W (s , f ∘ lift))                                          ≡⟨ cong (λ x → subst (_$ i) (apply-ext ext′ lemma)
                                                                                          (let s , f = x in in-W (s , f ∘ lift)))
                                                                            lemma′ ⟩
     subst (_$ i)
       (apply-ext ext′ lemma)
       (in-W (s , _⇔_.from (W≃W-lift-positions _) ∘ f ∘ lift))           ≡⟨ subst-ext ext′ ⟩

     subst id
       (lemma i)
       (in-W (s , _⇔_.from (W≃W-lift-positions _) ∘ f ∘ lift))           ≡⟨ trans (subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                            cong (λ eq →
                                                                                    _≃_.to eq
                                                                                      (in-W (s , _⇔_.from (W≃W-lift-positions _) ∘ f ∘ lift))) $
                                                                            _≃_.right-inverse-of (≡≃≃ univ) _ ⟩
     W≃W-lift-positions _
       (in-W (s , _⇔_.from (W≃W-lift-positions _) ∘ f ∘ lift))           ≡⟨⟩

     in-W
       (s , W≃W-lift-positions _ ∘ _⇔_.from (W≃W-lift-positions _) ∘ f)  ≡⟨ (cong (in-W ∘ (s ,_)) $
                                                                             apply-ext ext″ λ _ →
                                                                             _≃_.right-inverse-of (W≃W-lift-positions ext″) _) ⟩∎
     in-W x                                                              ∎)
  where
  ext′ : Extensionality i (lsuc (i ⊔ s ⊔ p))
  ext′ = lower-extensionality (s ⊔ p) lzero ext

  ext″ : Extensionality (i ⊔ p) (i ⊔ s ⊔ p)
  ext″ = lower-extensionality s _ ext

  lemma : ∀ i → W C i ≡ W (lift-positions C) i
  lemma _ = ≃⇒≡ univ (W≃W-lift-positions ext″)
