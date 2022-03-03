------------------------------------------------------------------------
-- Another definition of indexed containers
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris, and partly based on "Non-wellfounded trees in
-- Homotopy Type Theory" by Ahrens, Capriotti and Spadotti.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Indexed.Variant
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

import Bijection eq as B
open import Container.Indexed eq as C
  using (_⇾_; id⇾; _∘⇾_; Shape; Position; index)
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
open import Tactic.Sigma-cong eq
open import Univalence-axiom eq

private
  variable
    a ℓ p p₁ p₂ p′ q : Level
    A I O            : Type a
    P Q R            : A → Type p
    ext f i k o s    : A

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
⟦⟧-cong {i = i} {k = k} {p = p} {P₁ = Q₁} {P₂ = Q₂}
        ext (S ◁ P) Q₁↝Q₂ o =
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
Shape≃⟦⟧⊤ {o = o} (S ◁ P) =
  S o                                ↔⟨ inverse $ drop-⊤-right (λ _ → →-right-zero F.∘ inverse currying) ⟩□
  (∃ λ (s : S o) → ∀ i → P s i → ⊤)  □

------------------------------------------------------------------------
-- Coalgebras

-- The type of coalgebras for a (singly indexed) container.

Coalgebra : {I : Type i} → Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Coalgebra {i = i} {s = s} {p = p} {I = I} C =
  ∃ λ (P : I → Type (i ⊔ s ⊔ p)) → P ⇾ ⟦ C ⟧ P

-- Coalgebra morphisms.

infix 4 _⇨_

_⇨_ :
  {I : Type i} {C : Container I s p} →
  Coalgebra C → Coalgebra C → Type (i ⊔ s ⊔ p)
(P , f) ⇨ (Q , g) = ∃ λ (h : P ⇾ Q) → g ∘⇾ h ≡ map _ h ∘⇾ f

private
  variable
    X Y Z : Coalgebra C

-- An identity morphism.

id⇨ : X ⇨ X
id⇨ = id⇾ , refl _

-- Composition for _⇨_.

infix 9 [_]_∘⇨_

[_]_∘⇨_ : ∀ Z → Y ⇨ Z → X ⇨ Y → X ⇨ Z
[_]_∘⇨_ {Y = _ , g} {X = _ , f} (_ , h) (f₁ , eq₁) (f₂ , eq₂) =
    f₁ ∘⇾ f₂
  , (h ∘⇾ (f₁ ∘⇾ f₂)              ≡⟨⟩
     (h ∘⇾ f₁) ∘⇾ f₂              ≡⟨ cong (_∘⇾ f₂) eq₁ ⟩
     (map _ f₁ ∘⇾ g) ∘⇾ f₂        ≡⟨⟩
     map _ f₁ ∘⇾ (g ∘⇾ f₂)        ≡⟨ cong (map _ f₁ ∘⇾_) eq₂ ⟩
     map _ f₁ ∘⇾ (map _ f₂ ∘⇾ f)  ≡⟨⟩
     map _ (f₁ ∘⇾ f₂) ∘⇾ f        ∎)

-- The property of being a final coalgebra.

Final :
  {I : Type i} {C : Container I s p} →
  Coalgebra C → Type (lsuc (i ⊔ s ⊔ p))
Final X = ∀ Y → Contractible (Y ⇨ X)

-- A perhaps more traditional definition of what it means to be final.

Final′ :
  {I : Type i} {C : Container I s p} →
  Coalgebra C → Type (lsuc (i ⊔ s ⊔ p))
Final′ X =
  ∀ Y → ∃ λ (m : Y ⇨ X) → (m′ : Y ⇨ X) → proj₁ m ≡ proj₁ m′

-- Final X implies Final′ X.

Final→Final′ : (X : Coalgebra C) → Final X → Final′ X
Final→Final′ _ =
  ∀-cong _ λ _ → ∃-cong λ _ → ∀-cong _ λ _ → cong proj₁

-- Final is pointwise propositional (assumption extensionality).

Final-propositional :
  {I : Type i} {C : Container I s p} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  (X : Coalgebra C) →
  Is-proposition (Final X)
Final-propositional ext _ =
  Π-closure ext 1 λ _ →
  Contractible-propositional (lower-extensionality _ lzero ext)

-- Final coalgebras.

Final-coalgebra :
  {I : Type i} →
  Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Final-coalgebra C = ∃ λ (X : Coalgebra C) → Final X

-- Final coalgebras, defined using Final′.

Final-coalgebra′ :
  {I : Type i} →
  Container I s p → Type (lsuc (i ⊔ s ⊔ p))
Final-coalgebra′ C = ∃ λ (X : Coalgebra C) → Final′ X

-- Final-coalgebra C implies Final-coalgebra′ C.

Final-coalgebra→Final-coalgebra′ :
  Final-coalgebra C → Final-coalgebra′ C
Final-coalgebra→Final-coalgebra′ =
  ∃-cong Final→Final′

-- Carriers of final coalgebras (defined using Final′) for a given
-- container are pointwise equivalent.

carriers-of-final-coalgebras-equivalent′ :
  (((P₁ , _) , _) ((P₂ , _) , _) : Final-coalgebra′ C) →
  ∀ i → P₁ i ≃ P₂ i
carriers-of-final-coalgebras-equivalent′ (X₁ , final₁) (X₂ , final₂) i =
  Eq.↔→≃ (proj₁ to i) (proj₁ from i) to∘from from∘to
  where
  to : X₁ ⇨ X₂
  to = proj₁ (final₂ X₁)

  from : X₂ ⇨ X₁
  from = proj₁ (final₁ X₂)

  to∘from : ∀ x → proj₁ ([ X₂ ] to ∘⇨ from) i x ≡ x
  to∘from x =
    proj₁ ([ X₂ ] to ∘⇨ from) i x  ≡⟨ cong (λ f → f i x) $ sym $ proj₂ (final₂ X₂) $ [ X₂ ] to ∘⇨ from ⟩
    proj₁ (proj₁ (final₂ X₂)) i x  ≡⟨ cong (λ f → f i x) $ proj₂ (final₂ X₂) id⇨ ⟩
    proj₁ (id⇨ {X = X₂}) i x       ≡⟨⟩
    x                              ∎

  from∘to : ∀ x → proj₁ ([ X₁ ] from ∘⇨ to) i x ≡ x
  from∘to x =
    proj₁ ([ X₁ ] from ∘⇨ to) i x  ≡⟨ cong (λ f → f i x) $ sym $ proj₂ (final₁ X₁) $ [ X₁ ] from ∘⇨ to ⟩
    proj₁ (proj₁ (final₁ X₁)) i x  ≡⟨ cong (λ f → f i x) $ proj₂ (final₁ X₁) id⇨ ⟩
    proj₁ (id⇨ {X = X₁}) i x       ≡⟨⟩
    x                              ∎

-- The previous lemma relates the "out" functions of the two final
-- coalgebras in a certain way.

out-related′ :
  {C : Container I s p}
  (F₁@((_ , out₁) , _) F₂@((_ , out₂) , _) : Final-coalgebra′ C) →
  map C (_≃_.to ∘ carriers-of-final-coalgebras-equivalent′ F₁ F₂) ∘⇾
    out₁
    ≡
  out₂ ∘⇾ (_≃_.to ∘ carriers-of-final-coalgebras-equivalent′ F₁ F₂)
out-related′ (X₁ , _) (_ , final₂) =
  sym $ proj₂ (proj₁ (final₂ X₁))

-- Carriers of final coalgebras for a given container are pointwise
-- equivalent.

carriers-of-final-coalgebras-equivalent :
  (((P₁ , _) , _) ((P₂ , _) , _) : Final-coalgebra C) →
  ∀ i → P₁ i ≃ P₂ i
carriers-of-final-coalgebras-equivalent =
  carriers-of-final-coalgebras-equivalent′ on
    Final-coalgebra→Final-coalgebra′

-- The previous lemma relates the "out" functions of the two final
-- coalgebras in a certain way.

out-related :
  {C : Container I s p}
  (F₁@((_ , out₁) , _) F₂@((_ , out₂) , _) : Final-coalgebra C) →
  map C (_≃_.to ∘ carriers-of-final-coalgebras-equivalent F₁ F₂) ∘⇾ out₁
    ≡
  out₂ ∘⇾ (_≃_.to ∘ carriers-of-final-coalgebras-equivalent F₁ F₂)
out-related = out-related′ on Final-coalgebra→Final-coalgebra′

-- If X and Y are final coalgebras (with finality defined using
-- Final′), then—assuming extensionality—finality of X (defined using
-- Final) is equivalent to finality of Y.

Final′→Final≃Final :
  {I : Type i} {C : Container I s p}
  ((X , _) (Y , _) : Final-coalgebra′ C) →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Final X ↝[ lsuc (i ⊔ s ⊔ p) ∣ i ⊔ s ⊔ p ] Final Y
Final′→Final≃Final {i = i} {s = s} {p = p} {C = C}
  ((X₁ , out₁) , final₁) ((X₂ , out₂) , final₂) ext {k = k} ext′ =
  ∀-cong ext′ λ Y@(_ , f) →
  H-level-cong
    (lower-extensionality? k _ lzero ext′)
    0
    (Σ-cong (lemma₂ Y) λ g →

       out₁ ∘⇾ g ≡ map C g ∘⇾ f                 ↝⟨ inverse $ Eq.≃-≡ (lemma₃ Y) ⟩

       _≃_.to (lemma₃ Y) (out₁ ∘⇾ g) ≡
       _≃_.to (lemma₃ Y) (map C g ∘⇾ f)         ↔⟨⟩

       map C (_≃_.to ∘ lemma₁) ∘⇾ out₁ ∘⇾ g ≡
       map C (_≃_.to ∘ lemma₁) ∘⇾ map C g ∘⇾ f  ↝⟨ ≡⇒↝ _ $ cong (λ h → h ∘⇾ g ≡ map C (_≃_.to ∘ lemma₁) ∘⇾ map C g ∘⇾ f) $
                                                   out-related′ ((X₁ , out₁) , final₁) ((X₂ , out₂) , final₂) ⟩
       out₂ ∘⇾ (_≃_.to ∘ lemma₁) ∘⇾ g ≡
       map C (_≃_.to ∘ lemma₁) ∘⇾ map C g ∘⇾ f  ↔⟨⟩

       out₂ ∘⇾ _≃_.to (lemma₂ Y) g ≡
       map C (_≃_.to (lemma₂ Y) g) ∘⇾ f         □)
  where
  ext₁ = lower-extensionality (s ⊔ p) lzero ext
  ext₂ = lower-extensionality (i ⊔ s) lzero ext

  lemma₁ : ∀ i → X₁ i ≃ X₂ i
  lemma₁ =
    carriers-of-final-coalgebras-equivalent′
      ((X₁ , out₁) , final₁)
      ((X₂ , out₂) , final₂)

  lemma₂ : ((Y , _) : Coalgebra C) → (Y ⇾ X₁) ≃ (Y ⇾ X₂)
  lemma₂ _ =
    ∀-cong ext₁ λ _ →
    ∀-cong ext  λ _ →
    lemma₁ _

  lemma₃ : ((Y , _) : Coalgebra C) → (Y ⇾ ⟦ C ⟧ X₁) ≃ (Y ⇾ ⟦ C ⟧ X₂)
  lemma₃ _ =
    ∀-cong ext₁ λ _ →
    ∀-cong ext  λ _ →
    ⟦⟧-cong ext₂ C lemma₁ _

-- If there is a final C-coalgebra, and we have Final′ X for some
-- C-coalgebra X, then we also have Final X (assuming extensionality).

Final′→Final :
  {I : Type i} {C : Container I s p} →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  Final-coalgebra C →
  ((X , _) : Final-coalgebra′ C) →
  Final X
Final′→Final ext F₁@(_ , final₁) F₂ =
  Final′→Final≃Final
    (Final-coalgebra→Final-coalgebra′ F₁) F₂
    ext _ final₁

-- Final-coalgebra is pointwise propositional, assuming extensionality
-- and univalence.
--
-- This is a variant of Lemma 5 from "Non-wellfounded trees in
-- Homotopy Type Theory".

Final-coalgebra-propositional :
  {I : Type i} {C : Container I s p} →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (lsuc (i ⊔ s ⊔ p)) →
  Univalence (i ⊔ s ⊔ p) →
  Is-proposition (Final-coalgebra C)
Final-coalgebra-propositional {I = I} {C = C@(S ◁ P)}
  ext univ F₁@((P₁ , out₁) , _) F₂@(X₂@(P₂ , out₂) , _) =
  block λ b →
  Σ-≡,≡→≡ (Σ-≡,≡→≡ (lemma₁ b) (lemma₂ b))
    (Final-propositional (lower-extensionality lzero _ ext) X₂ _ _)
  where
  ext₁ = lower-extensionality _ lzero ext

  lemma₀ : Block "lemma₀" → ∀ i → P₁ i ≃ P₂ i
  lemma₀ ⊠ = carriers-of-final-coalgebras-equivalent F₁ F₂

  lemma₀-lemma :
    ∀ b x →
    map C (_≃_.to ∘ lemma₀ b) i (out₁ i (_≃_.from (lemma₀ b i) x)) ≡
    out₂ i x
  lemma₀-lemma {i = i} ⊠ x =
    map C (_≃_.to ∘ lemma₀ ⊠) i (out₁ i (_≃_.from (lemma₀ ⊠ i) x))  ≡⟨ cong (λ f → f _ (_≃_.from (lemma₀ ⊠ i) x)) $
                                                                       out-related F₁ F₂ ⟩
    out₂ i (_≃_.to (lemma₀ ⊠ i) (_≃_.from (lemma₀ ⊠ i) x))          ≡⟨ cong (out₂ _) $
                                                                       _≃_.right-inverse-of (lemma₀ ⊠ i) _ ⟩∎
    out₂ i x                                                        ∎

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
    subst (_$ i) (sym (lemma₁ b)) x                                    ≡⟨⟩
    subst (_$ i) (sym (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i))) x  ≡⟨ cong (flip (subst (_$ i)) _) $ sym $
                                                                          ext-sym ext₁ ⟩
    subst (_$ i) (apply-ext ext₁ λ i → sym (≃⇒≡ univ (lemma₀ b i))) x  ≡⟨ subst-ext ext₁ ⟩
    subst id (sym (≃⇒≡ univ (lemma₀ b i))) x                           ≡⟨ subst-id-in-terms-of-inverse∘≡⇒↝ equivalence ⟩
    _≃_.from (≡⇒≃ (≃⇒≡ univ (lemma₀ b i))) x                           ≡⟨ cong (λ eq → _≃_.from eq _) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.from (lemma₀ b i) x                                            ∎

  lemma₁-lemma₃ : ∀ b (f : P s ⇾ P₁) i p → _ ≡ _
  lemma₁-lemma₃ b f i p =
    subst (_$ i) (lemma₁ b) (f i p)                                    ≡⟨⟩
    subst (_$ i) (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i)) (f i p)  ≡⟨ subst-ext ext₁ ⟩
    subst id (≃⇒≡ univ (lemma₀ b i)) (f i p)                           ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩
    ≡⇒→ (≃⇒≡ univ (lemma₀ b i)) (f i p)                                ≡⟨ cong (λ eq → _≃_.to eq _) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.to (lemma₀ b i) (f i p)                                        ∎

  lemma₂ = λ b →
    apply-ext (lower-extensionality _ _ ext) λ i →
    apply-ext (lower-extensionality _ _ ext) λ x →

    subst (λ P → P ⇾ ⟦ C ⟧ P) (lemma₁ b) out₁ i x                   ≡⟨⟩

    subst (λ P → ∀ i → P i → ⟦ C ⟧ P i) (lemma₁ b) out₁ i x         ≡⟨ cong (_$ x) subst-∀ ⟩

    subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
      (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (refl _))
      (out₁ (subst (λ _ → I) (sym (lemma₁ b)) i)) x                 ≡⟨ elim¹
                                                                         (λ {i′} eq →
                                                                            subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
                                                                              (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (refl _))
                                                                              (out₁ (subst (λ _ → I) (sym (lemma₁ b)) i)) x ≡
                                                                            subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
                                                                              (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) eq)
                                                                              (out₁ i′) x)
                                                                         (refl _)
                                                                         _ ⟩
    subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
      (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (subst-const _))
      (out₁ i) x                                                    ≡⟨ cong (λ eq → subst (uncurry λ P i → P i → ⟦ C ⟧ P i) eq _ _) $
                                                                       lemma₁-lemma₁ b i ⟩
    subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
      (cong (_, _) (lemma₁ b))
      (out₁ i) x                                                    ≡⟨ cong (_$ x) $ sym $ subst-∘ _ _ _ ⟩

    subst (λ P → P i → ⟦ C ⟧ P i) (lemma₁ b) (out₁ i) x             ≡⟨ subst-→ ⟩

    subst (λ P → ⟦ C ⟧ P i) (lemma₁ b)
      (out₁ i (subst (_$ i) (sym (lemma₁ b)) x))                    ≡⟨ cong (subst (λ P → ⟦ C ⟧ P i) _) $ cong (out₁ _) $
                                                                       lemma₁-lemma₂ b i x ⟩
    subst (λ P → ⟦ C ⟧ P i) (lemma₁ b)
      (out₁ i (_≃_.from (lemma₀ b i) x))                            ≡⟨⟩

    subst (λ Q → ∃ λ (s : S i) → P s ⇾ Q) (lemma₁ b)
      (out₁ i (_≃_.from (lemma₀ b i) x))                            ≡⟨ push-subst-pair-× _ _ ⟩

    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , subst (λ Q → P s ⇾ Q) (lemma₁ b) f)                        ≡⟨ (let s , _ = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                        cong (s ,_) $
                                                                        apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                        push-subst-application _ _) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ i → subst (λ Q → P s i → Q i) (lemma₁ b) (f i))          ≡⟨ (let s , _ = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                        cong (s ,_) $
                                                                        apply-ext (lower-extensionality _ _ ext) λ _ →
                                                                        apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                        push-subst-application _ _) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ i p → subst (_$ i) (lemma₁ b) (f i p))                   ≡⟨ (let _ , f = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                        cong (_ ,_) $
                                                                        apply-ext (lower-extensionality _ _ ext) λ i →
                                                                        apply-ext (lower-extensionality _ _ ext) $
                                                                        lemma₁-lemma₃ b f i) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ i p → _≃_.to (lemma₀ b i) (f i p))                       ≡⟨⟩

    map C (_≃_.to ∘ lemma₀ b) i (out₁ i (_≃_.from (lemma₀ b i) x))  ≡⟨ lemma₀-lemma b x ⟩∎

    out₂ i x                                                        ∎

------------------------------------------------------------------------
-- Conversion lemmas

-- A conversion lemma for Container. Note that the last index is not
-- unrestricted.

Container⇔Container :
  ∀ {I : Type i} {O : Type o} p →
  Container₂ I O s (i ⊔ p) ⇔ C.Container₂ I O s (i ⊔ p)
Container⇔Container {i = iℓ} {s = s} {I = I} {O = O} p =
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
Container≃Container {i = i} {o = o} {s = s} {I = I} {O = O} p ext univ =
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
⟦⟧≃⟦⟧ _ {I = I} C {P = P} o =
  (∃ λ (s : Shape C o) → ((i , _) : Σ I (Position C s)) → P i)  ↔⟨ (∃-cong λ _ → currying) ⟩□
  (∃ λ (s : Shape C o) → (i : I) → Position C s i → P i)        □

-- Another conversion lemma for ⟦_⟧.

⟦⟧≃⟦⟧′ :
  ∀ p →
  {I : Type i} (C : C.Container₂ I O s (i ⊔ p)) {P : I → Type ℓ} →
  ∀ o →
  ⟦ _⇔_.from (Container⇔Container p) C ⟧ P o ↝[ i ⊔ p ∣ i ⊔ p ⊔ ℓ ]
  C.⟦ C ⟧ P o
⟦⟧≃⟦⟧′ {i = i} {ℓ = ℓ} p {I = I} C {P = P} _ {k = k} ext =
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
map≡map′ {i = i} {o = o} {p = p} {q = q} {s = s} {P = P} {Q = Q}
  p′ ext C {f = f} =
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

-- A conversion lemma for Coalgebra.

Coalgebra≃Coalgebra :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Coalgebra C ↝[ i ⊔ s ⊔ p ∣ i ⊔ s ⊔ p ]
  C.Coalgebra (_⇔_.to (Container⇔Container p) C)
Coalgebra≃Coalgebra {s = s} p C {k = k} ext =
  (∃ λ P → P ⇾ ⟦ C ⟧ P)                                   ↝⟨ (∃-cong λ _ →
                                                              ∀-cong (lower-extensionality? k (s ⊔ p) lzero ext) λ _ →
                                                              ∀-cong ext λ _ →
                                                              from-equivalence $ inverse $ ⟦⟧≃⟦⟧ p C _) ⟩□
  (∃ λ P → P ⇾ C.⟦ _⇔_.to (Container⇔Container p) C ⟧ P)  □

-- A conversion lemma for _⇨_.

⇨≃⇨ :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  (X Y : Coalgebra C) →
  (X ⇨ Y) ≃
  (Coalgebra≃Coalgebra p C _ X C.⇨ Coalgebra≃Coalgebra p C _ Y)
⇨≃⇨ {s = s} p C ext (P , f) (Q , g) =
  (∃ λ (h : P ⇾ Q) → g ∘⇾ h ≡ map _ h ∘⇾ f)     ↝⟨ (∃-cong λ h → inverse $ Eq.≃-≡ $
                                                    ∀-cong (lower-extensionality (s ⊔ p) lzero ext) λ _ →
                                                    ∀-cong ext λ _ →
                                                    inverse $ ⟦⟧≃⟦⟧ p C _) ⟩□
  (∃ λ (h : P ⇾ Q) →
     ((Σ-map id uncurry ∘_) ∘ g) ∘⇾ h ≡
     C.map _ h ∘⇾ ((Σ-map id uncurry ∘_) ∘ f))  □

-- A conversion lemma for Final.

Final≃Final :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  (ext : Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p))
  (X : Coalgebra C) →
  Final X ≃ C.Final (_≃_.to (Coalgebra≃Coalgebra p C ext) X)
Final≃Final p C ext′ ext X =
  (∀ Y → Contractible (Y ⇨ X))                              ↝⟨ (Π-cong ext′ (Coalgebra≃Coalgebra p C {k = equivalence} ext) λ Y →
                                                                H-level-cong ext 0 $
                                                                ⇨≃⇨ p C ext Y X) ⟩□
  (∀ Y → Contractible (Y C.⇨ Coalgebra≃Coalgebra p C _ X))  □

-- A conversion lemma for Final′.

Final′≃Final′ :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  (ext : Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p))
  (X : Coalgebra C) →
  Final′ X ≃ C.Final′ (_≃_.to (Coalgebra≃Coalgebra p C ext) X)
Final′≃Final′ p C ext′ ext X =
  (∀ Y → ∃ λ (m : Y   ⇨ X ) → (m′ : Y   ⇨ X ) → proj₁ m ≡ proj₁ m′)  ↝⟨ (Π-cong ext′ (Coalgebra≃Coalgebra p C {k = equivalence} ext) λ Y →
                                                                         Σ-cong (⇨≃⇨ p C ext Y X) λ _ →
                                                                         Π-cong ext (⇨≃⇨ p C ext Y X) λ _ →
                                                                         F.id) ⟩□
  (∀ Y → ∃ λ (m : Y C.⇨ X′) → (m′ : Y C.⇨ X′) → proj₁ m ≡ proj₁ m′)  □
  where
  X′ = _≃_.to (Coalgebra≃Coalgebra p C ext) X

-- A conversion lemma for Final-coalgebra.

Final-coalgebra≃Final-coalgebra :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Final-coalgebra C ≃
  C.Final-coalgebra (_⇔_.to (Container⇔Container p) C)
Final-coalgebra≃Final-coalgebra p C ext =
  (∃ λ (X :   Coalgebra C ) →   Final X)  ↝⟨ Σ-cong {k₁ = equivalence}
                                               (Coalgebra≃Coalgebra p C ext′)
                                               (Final≃Final p C ext ext′) ⟩□
  (∃ λ (X : C.Coalgebra C′) → C.Final X)  □
  where
  C′   = _⇔_.to (Container⇔Container p) C
  ext′ = lower-extensionality _ lzero ext

-- A conversion lemma for Final-coalgebra′.

Final-coalgebra′≃Final-coalgebra′ :
  ∀ p {I : Type i} (C : Container I s (i ⊔ p)) →
  Extensionality (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Final-coalgebra′ C ≃
  C.Final-coalgebra′ (_⇔_.to (Container⇔Container p) C)
Final-coalgebra′≃Final-coalgebra′ p C ext =
  (∃ λ (X :   Coalgebra C ) →   Final′ X)  ↝⟨ Σ-cong {k₁ = equivalence}
                                                (Coalgebra≃Coalgebra p C ext′)
                                                (Final′≃Final′ p C ext ext′) ⟩□
  (∃ λ (X : C.Coalgebra C′) → C.Final′ X)  □
  where
  C′   = _⇔_.to (Container⇔Container p) C
  ext′ = lower-extensionality _ lzero ext
