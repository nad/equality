------------------------------------------------------------------------
-- Algebras for the indexed containers in Container.Indexed.Variant
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris, and partly based on "Non-wellfounded trees in
-- Homotopy Type Theory" by Ahrens, Capriotti and Spadotti.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Indexed.Variant.Algebra
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (W)

open import Container.Indexed eq as C
  using (_⇾_; id⇾; _∘⇾_; _∘⇾′_; _∘⇾″_)
import Container.Indexed.Algebra eq as A
open import Container.Indexed.Variant eq
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
open import Univalence-axiom eq

private
  variable
    a iℓ p : Level
    A I O  : Type a
    i s x  : A
    C      : Container₂ I O s p

------------------------------------------------------------------------
-- Algebras

-- The type of algebras for a (singly indexed) container.

Algebra : {I : Type i} → Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Algebra {i = i} {s = s} {p = p} {I = I} C =
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

-- Initial is pointwise propositional (assuming extensionality).

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
carriers-of-initial-algebras-equivalent′ (X₁ , initial₁) (X₂ , initial₂) i =
  Eq.↔→≃ (proj₁ to i) (proj₁ from i) to∘from from∘to
  where
  to : X₁ ⇨ X₂
  to = proj₁ (initial₁ X₂)

  from : X₂ ⇨ X₁
  from = proj₁ (initial₂ X₁)

  to∘from : ∀ x → proj₁ ([ X₂ ] to ∘⇨ from) i x ≡ x
  to∘from x =
    proj₁ ([ X₂ ] to ∘⇨ from) i x  ≡⟨ cong (λ f → f i x) $ sym $ proj₂ (initial₂ X₂) $ [ X₂ ] to ∘⇨ from ⟩
    proj₁ (proj₁ (initial₂ X₂)) i x  ≡⟨ cong (λ f → f i x) $ proj₂ (initial₂ X₂) id⇨ ⟩
    proj₁ (id⇨ {X = X₂}) i x       ≡⟨⟩
    x                              ∎

  from∘to : ∀ x → proj₁ ([ X₁ ] from ∘⇨ to) i x ≡ x
  from∘to x =
    proj₁ ([ X₁ ] from ∘⇨ to) i x  ≡⟨ cong (λ f → f i x) $ sym $ proj₂ (initial₁ X₁) $ [ X₁ ] from ∘⇨ to ⟩
    proj₁ (proj₁ (initial₁ X₁)) i x  ≡⟨ cong (λ f → f i x) $ proj₂ (initial₁ X₁) id⇨ ⟩
    proj₁ (id⇨ {X = X₁}) i x       ≡⟨⟩
    x                              ∎

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
Initial′→Initial≃Initial {i = i} {s = s} {p = p} {C = C}
  ((X₁ , in₁) , initial₁) ((X₂ , in₂) , initial₂) ext {k = k} ext′ =
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
Initial-algebra-propositional {I = I} {C = C@(S ◁ P)}
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
  lemma₀-lemma {i = i} ⊠ x =
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

  lemma₁-lemma₁ = λ b i →
    sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (subst-const _)   ≡⟨ cong sym Σ-≡,≡→≡-subst-const-refl ⟩
    sym $ cong₂ _,_ (sym (lemma₁ b)) (refl _)        ≡⟨ sym cong₂-sym ⟩
    cong₂ _,_ (sym (sym (lemma₁ b))) (sym (refl _))  ≡⟨ cong₂ (cong₂ _) (sym-sym _) sym-refl ⟩
    cong₂ _,_ (lemma₁ b) (refl i)                    ≡⟨ cong₂-reflʳ _ ⟩∎
    cong (_, i) (lemma₁ b)                           ∎

  lemma₁-lemma₂ = λ b i x →
    subst (_$ i) (lemma₁ b) x                                    ≡⟨⟩
    subst (_$ i) (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i)) x  ≡⟨ subst-ext ext₁ ⟩
    subst id (≃⇒≡ univ (lemma₀ b i)) x                           ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩
    _≃_.to (≡⇒≃ (≃⇒≡ univ (lemma₀ b i))) x                       ≡⟨ cong (λ eq → _≃_.to eq _) $
                                                                    _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.to (lemma₀ b i) x                                        ∎

  lemma₁-lemma₃ = λ b i x →
    subst (_$ i) (sym (lemma₁ b)) x                                    ≡⟨⟩

    subst (_$ i) (sym (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i))) x  ≡⟨ cong (flip (subst _) _) $ sym $ ext-sym ext₁ ⟩

    subst (_$ i) (apply-ext ext₁ λ i → sym (≃⇒≡ univ (lemma₀ b i))) x  ≡⟨ subst-ext ext₁ ⟩

    subst id (sym (≃⇒≡ univ (lemma₀ b i))) x                           ≡⟨ subst-id-in-terms-of-inverse∘≡⇒↝ equivalence ⟩

    _≃_.from (≡⇒≃ (≃⇒≡ univ (lemma₀ b i))) x                           ≡⟨ cong (λ eq → _≃_.from eq _) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.from (lemma₀ b i) x                                            ∎

  lemma₁-lemma₄ = λ b i x@(s , f) →
    subst (λ P → ⟦ C ⟧ P i) (sym (lemma₁ b)) x                         ≡⟨⟩

    subst (λ P → ∃ λ (s : Shape C i) → Position C s ⇾ P)
      (sym (lemma₁ b)) x                                               ≡⟨ push-subst-pair-× _ _ ⟩

    s , subst (λ P → ∀ i → Position C s i → P i) (sym (lemma₁ b)) f    ≡⟨ (cong (s ,_) $ apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                           push-subst-application _ _) ⟩
    s ,
    (λ {i} → subst (λ P → Position C s i → P i) (sym (lemma₁ b))) ∘ f  ≡⟨ (cong (s ,_) $ apply-ext (lower-extensionality _ _ ext) λ _ →
                                                                           apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                           push-subst-application _ _) ⟩

    s , (λ i → subst (_$ i) (sym (lemma₁ b))) ∘⇾ f                     ≡⟨ (cong (s ,_) $ cong (_∘⇾ f) $
                                                                           apply-ext (lower-extensionality _ _ ext) λ i →
                                                                           apply-ext (lower-extensionality _ _ ext) λ x →
                                                                           lemma₁-lemma₃ b i x) ⟩
    s , (_≃_.from ∘ lemma₀ b) ∘⇾ f                                     ≡⟨⟩

    map C (_≃_.from ∘ lemma₀ b) i x                                    ∎

  lemma₂ = λ b →
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
fold X@(_ , f) _ (in-W (s , g)) =
  f _ (s , λ o p → fold X o (g o p))

-- "Fold" morphisms for W.

fold⇨ : (X : Algebra C) → W-algebra C ⇨ X
fold⇨ X = fold X , refl _

-- W-algebra C is an initial algebra (assuming extensionality).

W-initial :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Initial (W-algebra C)
W-initial {i = i} {s = s} {p = p} {C = C} ext X@(P , f) =
  fold⇨ X , unique
  where
  ext₁ : Extensionality p (i ⊔ s ⊔ p)
  ext₁ = lower-extensionality (i ⊔ s) lzero ext

  ext₂ : Extensionality i (i ⊔ s ⊔ p)
  ext₂ = lower-extensionality (s ⊔ p) lzero ext

  unique⇾ : ∀ ((g , _) : W-algebra C ⇨ X) i x → fold X i x ≡ g i x
  unique⇾ m@(g , eq) i (in-W x@(s , h)) =
    (f ∘⇾ map C (fold X)) i x  ≡⟨⟩
    f i (s , fold X ∘⇾ h)      ≡⟨ (cong (f i ∘ (s ,_)) $ apply-ext ext₂ λ i → apply-ext ext₁ λ p →
                                   unique⇾ m i (h i p)) ⟩
    f i (s , g ∘⇾ h)           ≡⟨⟩
    (f ∘⇾ map C g) i x         ≡⟨ cong (λ f → f i x) $ sym eq ⟩∎
    g i (in-W x)               ∎

  unique : (m : W-algebra C ⇨ X) → fold⇨ X ≡ m
  unique m@(_ , eq) = Σ-≡,≡→≡
    lemma₁
    (subst (λ h → h ∘⇾ (λ _ → in-W) ≡ f ∘⇾ map C h) lemma₁ (refl _)    ≡⟨ subst-in-terms-of-trans-and-cong ⟩

     trans (sym (cong (_∘⇾ (λ _ → in-W)) lemma₁))
       (trans (refl _) (cong ((f ∘⇾_) ∘ map C) lemma₁))                ≡⟨ cong (trans _) $
                                                                          trans-reflˡ _ ⟩
     trans (sym (cong (_∘⇾ (λ _ → in-W)) lemma₁))
       (cong ((f ∘⇾_) ∘ map C) lemma₁)                                 ≡⟨ cong₂ (trans ∘ sym)
                                                                            (C.cong-pre-∘⇾-ext ext₂ ext₂ ext ext)
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
      cong ((f ∘⇾_) ∘ map C) lemma₁                                      ≡⟨ sym $ cong-∘ _ _ _ ⟩

      cong (f ∘⇾_) (cong (map C) lemma₁)                                 ≡⟨ cong (cong _) $ cong-map-ext ext₂ ext ext₂ ext ext₂ ext₁ ⟩

      (cong (f ∘⇾_) $ apply-ext ext₂ λ _ → apply-ext ext λ (s , h) →
       cong (s ,_) $ apply-ext ext₂ $ apply-ext ext₁ ∘ unique⇾ m ∘⇾′ h)  ≡⟨ C.cong-post-∘⇾-ext {h = λ i _ → f i} ext₂ ext₂ ext ext ⟩

      (apply-ext ext₂ λ i → apply-ext ext λ (s , h) →
       cong (f i) $ cong (s ,_) $
       apply-ext ext₂ $ apply-ext ext₁ ∘ unique⇾ m ∘⇾′ h)                ≡⟨ (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ →
                                                                             cong (apply-ext ext) $ apply-ext ext λ _ →
                                                                             trans (cong-∘ _ _ _) $
                                                                             trans (sym $ trans-[trans]-sym _ _) $
                                                                             cong (trans _) $
                                                                             trans (sym $ cong-sym _ _) $
                                                                             cong (cong _) $ sym-sym _) ⟩
      (apply-ext ext₂ λ i → apply-ext ext λ x →
       trans (unique⇾ m i (in-W x)) (cong (λ f → f i x) eq))             ≡⟨ trans (cong (apply-ext ext₂) $ apply-ext ext₂ λ _ →
                                                                                   ext-trans ext) $
                                                                            ext-trans ext₂ ⟩∎
      (trans lemma₁′ $
       apply-ext ext₂ λ i → apply-ext ext λ x → cong (λ f → f i x) eq)   ∎

-- An initial algebra constructed using W.

W-initial-algebra :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Initial-algebra C
W-initial-algebra ext = W-algebra _ , W-initial ext

------------------------------------------------------------------------
-- Conversion lemmas

-- A conversion lemma for Algebra.

Algebra≃Algebra :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Algebra C ↝[ i ⊔ s ⊔ p ∣ i ⊔ s ⊔ p ]
  A.Algebra (_⇔_.to (Container⇔Container p) C)
Algebra≃Algebra {s = s} p C {k = k} ext =
  (∃ λ P → ⟦ C ⟧ P ⇾ P)                                   ↝⟨ (∃-cong λ _ →
                                                              ∀-cong (lower-extensionality? k (s ⊔ p) lzero ext) λ _ →
                                                              →-cong₁ ext $ inverse $
                                                              ⟦⟧≃⟦⟧ p C _) ⟩□
  (∃ λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P ⇾ P)  □

-- A conversion lemma for _⇨_.

⇨≃⇨ :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  (X Y : Algebra C) →
  (X ⇨ Y) ≃
  (Algebra≃Algebra p C _ X A.⇨ Algebra≃Algebra p C _ Y)
⇨≃⇨ {s = s} p C ext (P , f) (Q , g) =
  (∃ λ (h : P ⇾ Q) → h ∘⇾ f ≡ g ∘⇾ map _ h)   ↝⟨ (∃-cong λ h → inverse $ Eq.≃-≡ $
                                                  ∀-cong (lower-extensionality (s ⊔ p) lzero ext) λ _ →
                                                  →-cong₁ ext $ inverse $
                                                  ⟦⟧≃⟦⟧ p C _) ⟩□
  (∃ λ (h : P ⇾ Q) →
     h ∘⇾ f ∘⇾ (λ _ → Σ-map id curry) ≡
     g ∘⇾ map C h ∘⇾ (λ _ → Σ-map id curry))  □

-- A conversion lemma for Initial.

Initial≃Initial :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  (ext : Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p))
  (X : Algebra C) →
  Initial X ≃ A.Initial (_≃_.to (Algebra≃Algebra p C ext) X)
Initial≃Initial p C ext′ ext X =
  (∀ Y → Contractible (X ⇨ Y))                          ↝⟨ (Π-cong ext′ (Algebra≃Algebra p C {k = equivalence} ext) λ Y →
                                                            H-level-cong ext 0 $
                                                            ⇨≃⇨ p C ext X Y) ⟩□
  (∀ Y → Contractible (Algebra≃Algebra p C _ X A.⇨ Y))  □

-- A conversion lemma for Initial′.

Initial′≃Initial′ :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  (ext : Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p))
  (X : Algebra C) →
  Initial′ X ≃ A.Initial′ (_≃_.to (Algebra≃Algebra p C ext) X)
Initial′≃Initial′ p C ext′ ext X =
  (∀ Y → ∃ λ (m : X    ⇨ Y) → (m′ : X    ⇨ Y) → proj₁ m ≡ proj₁ m′)  ↝⟨ (Π-cong ext′ (Algebra≃Algebra p C {k = equivalence} ext) λ Y →
                                                                         Σ-cong (⇨≃⇨ p C ext X Y) λ _ →
                                                                         Π-cong ext (⇨≃⇨ p C ext X Y) λ _ →
                                                                         F.id) ⟩□
  (∀ Y → ∃ λ (m : X′ A.⇨ Y) → (m′ : X′ A.⇨ Y) → proj₁ m ≡ proj₁ m′)  □
  where
  X′ = _≃_.to (Algebra≃Algebra p C ext) X

-- A conversion lemma for Initial-algebra.

Initial-algebra≃Initial-algebra :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Initial-algebra C ≃
  A.Initial-algebra (_⇔_.to (Container⇔Container p) C)
Initial-algebra≃Initial-algebra p C ext =
  (∃ λ (X :   Algebra C ) →   Initial X)  ↝⟨ Σ-cong {k₁ = equivalence}
                                               (Algebra≃Algebra p C ext′)
                                               (Initial≃Initial p C ext ext′) ⟩□
  (∃ λ (X : A.Algebra C′) → A.Initial X)  □
  where
  C′   = _⇔_.to (Container⇔Container p) C
  ext′ = lower-extensionality _ lzero ext

-- A conversion lemma for Initial-algebra′.

Initial-algebra′≃Initial-algebra′ :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Initial-algebra′ C ≃
  A.Initial-algebra′ (_⇔_.to (Container⇔Container p) C)
Initial-algebra′≃Initial-algebra′ p C ext =
  (∃ λ (X :   Algebra C ) →   Initial′ X)  ↝⟨ Σ-cong {k₁ = equivalence}
                                                (Algebra≃Algebra p C ext′)
                                                (Initial′≃Initial′ p C ext ext′) ⟩□
  (∃ λ (X : A.Algebra C′) → A.Initial′ X)  □
  where
  C′   = _⇔_.to (Container⇔Container p) C
  ext′ = lower-extensionality _ lzero ext

-- A conversion lemma for W.

W≃W :
  ∀ p {I : Type iℓ} {C : Container I s (iℓ ⊔ p)} {i} →
  W C i ↝[ iℓ ⊔ p ∣ iℓ ⊔ s ⊔ p ]
  A.W (_⇔_.to (Container⇔Container p) C) i
W≃W {iℓ = iℓ} {s = s} p {C = C} =
  generalise-ext?
    (record { to = to; from = from })
    (λ ext → to-from ext , from-to ext)
  where
  to : W C i → A.W (_⇔_.to (Container⇔Container p) C) i
  to (in-W (s , f)) = A.in-W (s , λ (i , p) → to (f i p))

  from : A.W (_⇔_.to (Container⇔Container p) C) i → W C i
  from (A.in-W (s , f)) = in-W (s , λ i  p → from (f (i , p)))

  module _ (ext : Extensionality (iℓ ⊔ p) (iℓ ⊔ s ⊔ p)) where

    to-from :
      (x : A.W (_⇔_.to (Container⇔Container p) C) i) →
      to (from x) ≡ x
    to-from (A.in-W (s , f)) =
      cong (A.in-W ∘ (s ,_)) $ apply-ext ext λ p → to-from (f p)

    from-to : (x : W C i) → from (to x) ≡ x
    from-to (in-W (s , f)) =
      cong (in-W ∘ (s ,_)) $
      apply-ext (lower-extensionality p lzero ext) λ i →
      apply-ext ext λ p →
      from-to (f i p)

-- A conversion lemma for W-algebra.

W-algebra≡W-algebra :
  ∀ p {I : Type iℓ} {C : Container I s (iℓ ⊔ p)} →
  Extensionality (iℓ ⊔ s ⊔ p) (lsuc (iℓ ⊔ s ⊔ p)) →
  Univalence (iℓ ⊔ s ⊔ p) →
  Algebra≃Algebra p C _ (W-algebra C) ≡
  A.W-algebra (_⇔_.to (Container⇔Container p) C)
W-algebra≡W-algebra {s = s} p {C = C} ext univ =
  Σ-≡,≡→≡
    (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)
    (apply-ext (lower-extensionality (s ⊔ p) _ ext) λ i →
     apply-ext (lower-extensionality lzero   _ ext) λ x@(s , f) →

     let lemma′ =
           subst (λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P i)
             (sym (apply-ext ext₁ lemma)) x                            ≡⟨ elim₁
                                                                                (λ eq →
                                                                                   subst (λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P i)
                                                                                     (sym eq) x ≡
                                                                                   (s , _≃_.from (≡⇒≃ $ ext⁻¹ eq _) ∘ f))
                                                                                (
             subst (λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P i)
               (sym (refl _)) x                                                  ≡⟨ trans (cong (flip (subst _) _) sym-refl) $
                                                                                    subst-refl _ _ ⟩

             x                                                                   ≡⟨ (cong (s ,_) $ apply-ext ext₂ λ _ →
                                                                                     cong (λ eq → _≃_.from eq _) $ sym
                                                                                     ≡⇒≃-refl) ⟩

             s , _≃_.from (≡⇒≃ $ refl _) ∘ f                                     ≡⟨ (cong (s ,_) $ apply-ext ext₂ λ _ →
                                                                                     cong (λ eq → _≃_.from (≡⇒≃ eq) (f _)) $ sym $
                                                                                     ext⁻¹-refl _) ⟩∎
             (let F = A.W (_⇔_.to (Container⇔Container p) C) in
              s , _≃_.from (≡⇒≃ $ ext⁻¹ (refl F) _) ∘ f)                         ∎)
                                                                                _ ⟩

           s , _≃_.from (≡⇒≃ $ ext⁻¹ (apply-ext ext₁ lemma) _) ∘ f     ≡⟨ (cong (s ,_) $ apply-ext ext₂ λ pos →
                                                                           cong (λ (eq : ∀ i → W C i ≡ A.W (_⇔_.to (Container⇔Container p) C) i) →
                                                                                   _≃_.from (≡⇒≃ (eq _)) (f pos)) $
                                                                           _≃_.left-inverse-of (Eq.extensionality-isomorphism ext₁) _) ⟩

           s , _≃_.from (≡⇒≃ $ lemma _) ∘ f                            ≡⟨ (cong (s ,_) $ apply-ext ext₂ λ _ → cong (λ eq → _≃_.from eq (f _)) $
                                                                           _≃_.right-inverse-of (≡≃≃ univ) _) ⟩∎
           s , _⇔_.from (W≃W p _) ∘ f                                  ∎
     in

     subst (λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P ⇾ P)
       (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)
       (λ _ (s , f) → in-W (s , curry f))
       i x                                                              ≡⟨ cong (_$ x) $ sym $
                                                                           push-subst-application _ _ ⟩

     subst (λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P i → P i)
       (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)
       (λ (s , f) → in-W (s , curry f))
       x                                                                ≡⟨ subst-→ ⟩

     subst (_$ i)
       (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)
       (let s , f =
              subst (λ P → C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P i)
                (sym (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)) x
        in in-W (s , curry f))                                          ≡⟨ cong (λ (s , f) →
                                                                                   subst (_$ i) (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)
                                                                                     (in-W (s , curry f)))
                                                                           lemma′ ⟩
     subst (_$ i)
       (apply-ext ext₁ λ _ → ≃⇒≡ univ $ W≃W p ext₂)
       (in-W (s , curry (_⇔_.from (W≃W p _) ∘ f)))                      ≡⟨ subst-ext ext₁ ⟩

     subst id
       (≃⇒≡ univ $ W≃W p ext₂)
       (in-W (s , curry (_⇔_.from (W≃W p _) ∘ f)))                      ≡⟨ trans (subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                           cong (λ eq → _≃_.to eq (in-W (s , curry (_⇔_.from (W≃W p _) ∘ f)))) $
                                                                           _≃_.right-inverse-of (≡≃≃ univ) _ ⟩

     W≃W p _ (in-W (s , curry (_⇔_.from (W≃W p _) ∘ f)))                ≡⟨⟩

     A.in-W (s , W≃W p _ ∘ _⇔_.from (W≃W p _) ∘ f)                      ≡⟨ (cong (A.in-W ∘ (s ,_)) $ apply-ext ext₂ λ _ →
                                                                            _≃_.right-inverse-of (W≃W p ext₂) _) ⟩∎
     A.in-W x                                                           ∎)
  where
  ext₁ = lower-extensionality (s ⊔ p) lzero ext
  ext₂ = lower-extensionality s       _     ext

  lemma : ∀ i → W C i ≡ A.W (_⇔_.to (Container⇔Container p) C) i
  lemma _ = ≃⇒≡ univ $ W≃W p ext₂

-- A conversion lemma for W-initial.

W-initial≡W-initial :
  ∀ p {I : Type iℓ} {C : Container I s (iℓ ⊔ p)}
  (ext₁ : Extensionality (iℓ ⊔ s ⊔ p) (lsuc (iℓ ⊔ s ⊔ p)))
  (ext₂ : Extensionality (lsuc (iℓ ⊔ s ⊔ p)) (iℓ ⊔ s ⊔ p))
  (ext₃ : Extensionality (iℓ ⊔ s ⊔ p) (iℓ ⊔ s ⊔ p))
  (univ : Univalence (iℓ ⊔ s ⊔ p)) →
  subst A.Initial (W-algebra≡W-algebra p ext₁ univ)
    (_≃_.to (Initial≃Initial p C ext₂ ext₃ (W-algebra C))
       (W-initial ext₃)) ≡
  A.W-initial ext₃
W-initial≡W-initial _ _ ext₂ _ _ =
  A.Initial-propositional ext₂ _ _ _

-- A conversion lemma for W-initial-algebra.

W-initial-algebra≡W-initial-algebra :
  ∀ p {I : Type iℓ} {C : Container I s (iℓ ⊔ p)} →
  Extensionality (lsuc (iℓ ⊔ s ⊔ p)) (lsuc (iℓ ⊔ s ⊔ p)) →
  (ext₁ : Extensionality (lsuc (iℓ ⊔ s ⊔ p)) (iℓ ⊔ s ⊔ p))
  (ext₂ : Extensionality (iℓ ⊔ s ⊔ p) (iℓ ⊔ s ⊔ p)) →
  Univalence (iℓ ⊔ s ⊔ p) →
  _≃_.to (Initial-algebra≃Initial-algebra p C ext₁)
    (W-initial-algebra ext₂) ≡
  A.W-initial-algebra ext₂
W-initial-algebra≡W-initial-algebra _ ext _ _ univ =
  A.Initial-algebra-propositional ext univ _ _
