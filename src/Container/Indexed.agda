------------------------------------------------------------------------
-- Indexed containers
------------------------------------------------------------------------

-- Partly based on "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris, and partly based on "Non-wellfounded trees in
-- Homotopy Type Theory" by Ahrens, Capriotti and Spadotti.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Container.Indexed
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude

open import Equivalence eq as Eq using (_≃_)
open import Function-universe eq hiding (id; _∘_)
open import H-level.Closure eq
open import Univalence-axiom eq

private
  variable
    a iℓ p p₁ p₂ q : Level
    A I            : Type a
    P Q R          : A → Type p
    i k s          : A

------------------------------------------------------------------------
-- _⇾_

-- A kind of function space for indexed types.

infix 4 _⇾_

_⇾_ :
  {A : Type a} →
  (A → Type p) → (A → Type q) → Type (a ⊔ p ⊔ q)
P ⇾ Q = ∀ x → P x → Q x

-- An identity function.

id⇾ : P ⇾ P
id⇾ _ = id

-- Composition for _⇾_.

infixr 9 _∘⇾_

_∘⇾_ : Q ⇾ R → P ⇾ Q → P ⇾ R
f ∘⇾ g = λ i → f i ∘ g i

------------------------------------------------------------------------
-- Containers

-- Indexed containers.

record Container (I : Type iℓ) : Type (lsuc iℓ) where
  field
    Shape    : I → Type iℓ
    Position : Shape i → Type iℓ
    index    : Position s → I

open Container public

private
  variable
    C : Container I

------------------------------------------------------------------------
-- Polynomial functors

-- The polynomial functor associated to a container.

⟦_⟧ :
  {I : Type i} →
  Container I → (I → Type a) → I → Type (i ⊔ a)
⟦ C ⟧ P i = ∃ λ (s : Shape C i) → (p : Position C s) → P (index C p)

-- A map function.

map : (C : Container I) → P ⇾ Q → ⟦ C ⟧ P ⇾ ⟦ C ⟧ Q
map C f _ (s , g) = s , λ p → f (index C p) (g p)

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
  Extensionality? k i (p₁ ⊔ p₂) →
  (C : Container I) →
  (∀ i → P₁ i ↝[ k ] P₂ i) →
  (∀ i → ⟦ C ⟧ P₁ i ↝[ k ] ⟦ C ⟧ P₂ i)
⟦⟧-cong {P₁ = P₁} {P₂ = P₂} ext C P₁↝P₂ i =
  (∃ λ (s : Shape C i) → (p : Position C s) → P₁ (index C p))  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → P₁↝P₂ _) ⟩□
  (∃ λ (s : Shape C i) → (p : Position C s) → P₂ (index C p))  □

-- The shapes of a container are pointwise equivalent to the
-- polynomial functor of the container applied to the constant
-- function yielding the unit type.
--
-- (This lemma was suggested to me by an anonymous reviewer of a
-- paper.)

Shape≃⟦⟧⊤ :
  (C : Container I) →
  Shape C i ≃ ⟦ C ⟧ (λ _ → ⊤) i
Shape≃⟦⟧⊤ {i = i} C =
  Shape C i                                 ↔⟨ inverse $ drop-⊤-right (λ _ → →-right-zero) ⟩□
  (∃ λ (s : Shape C i) → Position C s → ⊤)  □

------------------------------------------------------------------------
-- Coalgebras

-- The type of coalgebras for a container.

Coalgebra : {I : Type i} → Container I → Type (lsuc i)
Coalgebra {i = i} {I = I} C =
  ∃ λ (P : I → Type i) → P ⇾ ⟦ C ⟧ P

-- Coalgebra morphisms.

infix 4 _⇨_

_⇨_ :
  {I : Type i} {C : Container I} →
  Coalgebra C → Coalgebra C → Type i
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
  {I : Type i} {C : Container I} →
  Coalgebra C → Type (lsuc i)
Final X = ∀ Y → Contractible (Y ⇨ X)

-- Final is pointwise propositional (assumption extensionality).

Final-propositional :
  {I : Type i} {C : Container I} →
  Extensionality (lsuc i) i →
  (X : Coalgebra C) →
  Is-proposition (Final X)
Final-propositional ext _ =
  Π-closure ext 1 λ _ →
  Contractible-propositional (lower-extensionality _ lzero ext)

-- Final coalgebras.

Final-coalgebra :
  {I : Type i} →
  Container I → Type (lsuc i)
Final-coalgebra C = ∃ λ (X : Coalgebra C) → Final X

-- Carriers of final coalgebras for a given container are pointwise
-- equivalent.

carriers-of-final-coalgebras-equivalent :
  (((P₁ , _) , _) ((P₂ , _) , _) : Final-coalgebra C) →
  ∀ i → P₁ i ≃ P₂ i
carriers-of-final-coalgebras-equivalent (X₁ , final₁) (X₂ , final₂) i =
  Eq.↔→≃ (proj₁ to i) (proj₁ from i) to∘from from∘to
  where
  to : X₁ ⇨ X₂
  to = proj₁ (final₂ X₁)

  from : X₂ ⇨ X₁
  from = proj₁ (final₁ X₂)

  to∘from : ∀ x → proj₁ ([ X₂ ] to ∘⇨ from) i x ≡ x
  to∘from x =
    proj₁ ([ X₂ ] to ∘⇨ from) i x  ≡⟨ cong (λ f → proj₁ f i x) $ sym $ proj₂ (final₂ X₂) $ [ X₂ ] to ∘⇨ from ⟩
    proj₁ (proj₁ (final₂ X₂)) i x  ≡⟨ cong (λ f → proj₁ f i x) $ proj₂ (final₂ X₂) id⇨ ⟩
    proj₁ (id⇨ {X = X₂}) i x       ≡⟨⟩
    x                              ∎

  from∘to : ∀ x → proj₁ ([ X₁ ] from ∘⇨ to) i x ≡ x
  from∘to x =
    proj₁ ([ X₁ ] from ∘⇨ to) i x  ≡⟨ cong (λ f → proj₁ f i x) $ sym $ proj₂ (final₁ X₁) $ [ X₁ ] from ∘⇨ to ⟩
    proj₁ (proj₁ (final₁ X₁)) i x  ≡⟨ cong (λ f → proj₁ f i x) $ proj₂ (final₁ X₁) id⇨ ⟩
    proj₁ (id⇨ {X = X₁}) i x       ≡⟨⟩
    x                              ∎

-- The previous lemma relates the "out" functions of the two final
-- coalgebras in a certain way.

out-related :
  {C : Container I}
  (F₁@((_ , out₁) , _) F₂@((_ , out₂) , _) : Final-coalgebra C) →
  map C (_≃_.to ∘ carriers-of-final-coalgebras-equivalent F₁ F₂) ∘⇾ out₁
    ≡
  out₂ ∘⇾ (_≃_.to ∘ carriers-of-final-coalgebras-equivalent F₁ F₂)
out-related (X₁ , _) (_ , final₂) =
  sym $ proj₂ (proj₁ (final₂ X₁))

-- Final-coalgebra is pointwise propositional, assuming extensionality
-- and univalence.
--
-- This is a variant of Lemma 5 from "Non-wellfounded trees in
-- Homotopy Type Theory".

Final-coalgebra-propositional :
  {I : Type i} {C : Container I} →
  Extensionality (lsuc i) (lsuc i) →
  Univalence i →
  Is-proposition (Final-coalgebra C)
Final-coalgebra-propositional
  {I = I} {C = C}
  ext univ F₁@((P₁ , out₁) , _) F₂@(X₂@(P₂ , out₂) , _) =
  block λ b →
  Σ-≡,≡→≡ (Σ-≡,≡→≡ (lemma₁ b) (lemma₂ b))
    (Final-propositional (lower-extensionality lzero _ ext) X₂ _ _)
  where
  ext₁′ = lower-extensionality _ lzero ext
  ext₁  = Eq.good-ext ext₁′

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
                                                                          Eq.good-ext-sym ext₁′ _ ⟩
    subst (_$ i) (apply-ext ext₁ λ i → sym (≃⇒≡ univ (lemma₀ b i))) x  ≡⟨ Eq.subst-good-ext ext₁′ _ _ ⟩
    subst id (sym (≃⇒≡ univ (lemma₀ b i))) x                           ≡⟨ subst-id-in-terms-of-inverse∘≡⇒↝ equivalence ⟩
    _≃_.from (≡⇒≃ (≃⇒≡ univ (lemma₀ b i))) x                           ≡⟨ cong (λ eq → _≃_.from eq _) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.from (lemma₀ b i) x                                            ∎

  lemma₁-lemma₃ = λ b i _ f p →
    subst (λ P → P (index C p)) (lemma₁ b) (f p)          ≡⟨⟩

    subst (λ P → P (index C p))
      (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i)) (f p)  ≡⟨ Eq.subst-good-ext ext₁′ _ _ ⟩

    subst id (≃⇒≡ univ (lemma₀ b (index C p))) (f p)      ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩

    ≡⇒→ (≃⇒≡ univ (lemma₀ b (index C p))) (f p)           ≡⟨ cong (λ eq → _≃_.to eq _) $
                                                             _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.to (lemma₀ b (index C p)) (f p)                   ∎

  lemma₂ = λ b →
    apply-ext (lower-extensionality _ _ ext) λ i →
    apply-ext (lower-extensionality _ _ ext) λ x →

    subst (λ P → P ⇾ ⟦ C ⟧ P) (lemma₁ b) out₁ i x                        ≡⟨⟩

    subst (λ P → ∀ i → P i → ⟦ C ⟧ P i) (lemma₁ b) out₁ i x              ≡⟨ cong (_$ x) subst-∀ ⟩

    subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
      (sym $ Σ-≡,≡→≡ (sym (lemma₁ b)) (refl _))
      (out₁ (subst (λ _ → I) (sym (lemma₁ b)) i)) x                      ≡⟨ elim¹
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
      (out₁ i) x                                                         ≡⟨ cong (λ eq → subst (uncurry λ P i → P i → ⟦ C ⟧ P i) eq _ _) $
                                                                            lemma₁-lemma₁ b i ⟩
    subst (uncurry λ P i → P i → ⟦ C ⟧ P i)
      (cong (_, _) (lemma₁ b))
      (out₁ i) x                                                         ≡⟨ cong (_$ x) $ sym $ subst-∘ _ _ _ ⟩

    subst (λ P → P i → ⟦ C ⟧ P i) (lemma₁ b) (out₁ i) x                  ≡⟨ subst-→ ⟩

    subst (λ P → ⟦ C ⟧ P i) (lemma₁ b)
      (out₁ i (subst (_$ i) (sym (lemma₁ b)) x))                         ≡⟨ cong (subst (λ P → ⟦ C ⟧ P i) _) $ cong (out₁ _) $
                                                                            lemma₁-lemma₂ b i x ⟩
    subst (λ P → ⟦ C ⟧ P i) (lemma₁ b)
      (out₁ i (_≃_.from (lemma₀ b i) x))                                 ≡⟨⟩

    subst (λ P → ∃ λ (s : Shape C i) → ∀ p → P (index C p))
      (lemma₁ b)
      (out₁ i (_≃_.from (lemma₀ b i) x))                                 ≡⟨ push-subst-pair-× _ _ ⟩

    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , subst (λ P → (p : Position C s) → P (index C p)) (lemma₁ b) f)  ≡⟨ (let s , _ = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                             cong (s ,_) $ apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                             push-subst-application _ _) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ p → subst (λ P → P (index C p)) (lemma₁ b) (f p))             ≡⟨ (let _ , f = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                             cong (_ ,_) $ apply-ext (lower-extensionality _ _ ext) $
                                                                             lemma₁-lemma₃ b i x f) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ p → _≃_.to (lemma₀ b (index C p)) (f p))                      ≡⟨⟩

    map C (_≃_.to ∘ lemma₀ b) i (out₁ i (_≃_.from (lemma₀ b i) x))       ≡⟨ lemma₀-lemma b x ⟩∎

    out₂ i x                                                             ∎
