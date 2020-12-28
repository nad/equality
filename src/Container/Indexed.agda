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
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
open import Univalence-axiom eq

private
  variable
    a ℓ p p₁ p₂ q : Level
    A I O         : Type a
    P Q R         : A → Type p
    ext f i k o s : A

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
  {I : Type i} {C : Container I s p} →
  Extensionality? k (lsuc (i ⊔ s ⊔ p)) (i ⊔ s ⊔ p) →
  Extensionality (i ⊔ s ⊔ p) (i ⊔ s ⊔ p) →
  ((X , _) (Y , _) : Final-coalgebra′ C) →
  Final X ↝[ k ] Final Y
Final′→Final≃Final {s = s} {p = p} {k = k} {C = C}
  ext′ ext ((X₁ , out₁) , final₁) ((X₂ , out₂) , final₂) =
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
  ext₂ = lower-extensionality s       lzero ext

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
  Final′→Final≃Final _ ext
    (Final-coalgebra→Final-coalgebra′ F₁) F₂
    final₁

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
Final-coalgebra-propositional
  {I = I} {C = C@(S ◁ P)}
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

  lemma₁-lemma₃ : ∀ b (f : P s ⇾ P₁) i p → _ ≡ _
  lemma₁-lemma₃ b f i p =
    subst (_$ i) (lemma₁ b) (f i p)                                    ≡⟨⟩
    subst (_$ i) (apply-ext ext₁ λ i → ≃⇒≡ univ (lemma₀ b i)) (f i p)  ≡⟨ Eq.subst-good-ext ext₁′ _ _ ⟩
    subst id (≃⇒≡ univ (lemma₀ b i)) (f i p)                           ≡⟨ subst-id-in-terms-of-≡⇒↝ equivalence ⟩
    ≡⇒→ (≃⇒≡ univ (lemma₀ b i)) (f i p)                                ≡⟨ cong (λ eq → _≃_.to eq _) $
                                                                          _≃_.right-inverse-of (≡≃≃ univ) _ ⟩∎
    _≃_.to (lemma₀ b i) (f i p)                                        ∎

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

    subst (λ Q → ∃ λ (s : S i) → P s ⇾ Q) (lemma₁ b)
      (out₁ i (_≃_.from (lemma₀ b i) x))                                 ≡⟨ push-subst-pair-× _ _ ⟩

    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , subst (λ Q → P s ⇾ Q) (lemma₁ b) f)                             ≡⟨ (let s , _ = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                             cong (s ,_) $
                                                                             apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                             push-subst-application _ _) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ i → subst (λ Q → P s i → Q i) (lemma₁ b) (f i))               ≡⟨ (let s , _ = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                             cong (s ,_) $
                                                                             apply-ext (lower-extensionality _ _ ext) λ _ →
                                                                             apply-ext (lower-extensionality _ _ ext) λ _ → sym $
                                                                             push-subst-application _ _) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ i p → subst (_$ i) (lemma₁ b) (f i p))                        ≡⟨ (let _ , f = out₁ i (_≃_.from (lemma₀ b i) x) in
                                                                             cong (_ ,_) $
                                                                             apply-ext (lower-extensionality _ _ ext) λ i →
                                                                             apply-ext (lower-extensionality _ _ ext) $
                                                                             lemma₁-lemma₃ b f i) ⟩
    (let s , f = out₁ i (_≃_.from (lemma₀ b i) x) in
     s , λ i p → _≃_.to (lemma₀ b i) (f i p))                            ≡⟨⟩

    map C (_≃_.to ∘ lemma₀ b) i (out₁ i (_≃_.from (lemma₀ b i) x))       ≡⟨ lemma₀-lemma b x ⟩∎

    out₂ i x                                                             ∎
