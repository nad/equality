------------------------------------------------------------------------
-- Some results that hold for left exact modalities
------------------------------------------------------------------------

-- Unless otherwise noted this code is based on "Modalities in
-- Homotopy Type Theory" by Rijke, Shulman and Spitters, and/or (some
-- version of) the corresponding Coq code. (Details may differ, and
-- perhaps there are some "obvious" results that do not have direct
-- counterparts in the work of Rijke, Shulman and Spitters, even
-- though there is no note about this.)

{-# OPTIONS --without-K --safe #-}

open import Equality
import Modality.Basics

module Modality.Left-exact
  {c⁺}
  (eq-J : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq-J)
  {a}
  (M : Modality a)
  (open Modality M hiding (η-[]◯-η≃◯))
  (lex : Left-exact-η-cong)
  where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_)
open import Prelude

import Bijection eq-J as Bijection
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.List eq-J
open import Extensionality eq-J
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Preimage eq-J as Preimage using (_⁻¹_)

private
  variable
    ℓ           : Level
    A B         : Type ℓ
    f p x y _<_ : A
    P Q         : A → Type p

------------------------------------------------------------------------
-- Some basic properties

-- The modality is left exact.

left-exact : Left-exact ◯
left-exact = _⇔_.from (Left-exact≃Left-exact-η-cong _) lex

-- There is an equivalence between ◯ (x ≡ y) and η x ≡ η y.

◯≡≃η≡η : ◯ (x ≡ y) ≃ (η x ≡ η y)
◯≡≃η≡η = Eq.⟨ η-cong , lex ⟩

-- The function η-cong has an inverse.

η-cong⁻¹ : η x ≡ η y → ◯ (x ≡ y)
η-cong⁻¹ = _≃_.from ◯≡≃η≡η

η-cong-η-cong⁻¹ : η-cong (η-cong⁻¹ p) ≡ p
η-cong-η-cong⁻¹ = _≃_.right-inverse-of ◯≡≃η≡η _

η-cong⁻¹-η-cong : η-cong⁻¹ (η-cong p) ≡ p
η-cong⁻¹-η-cong = _≃_.left-inverse-of ◯≡≃η≡η _

-- A "computation rule" for η-cong⁻¹.

η-cong⁻¹-η : η-cong⁻¹ (refl (η x)) ≡ η (refl x)
η-cong⁻¹-η {x = x} = _≃_.to-from ◯≡≃η≡η
  (η-cong (η (refl x))  ≡⟨ η-cong-η ⟩
   cong η (refl x)      ≡⟨ cong-refl _ ⟩∎
   refl (η x)           ∎)

------------------------------------------------------------------------
-- Separatedness

-- I did not take the lemma in this section from "Modalities in
-- Homotopy Type Theory" or the corresponding Coq code.

-- A is separated if and only if η is an embedding for A.

Separated≃Is-embedding-η :
  Separated A ↝[ a ∣ a ] Is-embedding (η ⦂ (A → ◯ A))
Separated≃Is-embedding-η {A = A} ext =
  (∀ x y → Modal (x ≡ y))                            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Modal≃Is-equivalence-η ext) ⟩
  (∀ x y → Is-equivalence (η {A = x ≡ y}))           ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                         Is-equivalence≃Is-equivalence-∘ˡ lex ext) ⟩
  (∀ x y → Is-equivalence (η-cong ∘ η {A = x ≡ y}))  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → Is-equivalence-cong ext λ _ → η-cong-η) ⟩□
  (∀ x y → Is-equivalence (cong {x = x} {y = y} η))  □

------------------------------------------------------------------------
-- H-levels

-- If A has a given h-level, then ◯ A has the same h-level.

H-level′→H-level′-◯ : ∀ n → H-level′ n A → H-level′ n (◯ A)
H-level′→H-level′-◯ {A = A} zero =
  Contractible A      →⟨ Contractible→Connected ⟩□
  Contractible (◯ A)  □
H-level′→H-level′-◯ {A = A} (suc n) =
  ((x y : A) → H-level′ n (x ≡ y))      →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                            H-level′→H-level′-◯ n) ⟩
  ((x y : A) → H-level′ n (◯ (x ≡ y)))  →⟨ (λ h →
                                              ◯-elim′ (λ _ → Stable-Π λ _ →
                                                             Stable-H-level′ n $
                                                             Modal→Modalⁿ n $
                                                             Separated-◯ _ _) λ x →
                                              ◯-elim′ (λ _ → Stable-H-level′ n $
                                                             Modal→Modalⁿ n $
                                                             Separated-◯ _ _) λ y →
                                              H-level′-cong _ n ◯≡≃η≡η (h x y)) ⟩□
  ((x y : ◯ A) → H-level′ n (x ≡ y))    □

-- If A has a given h-level, then ◯ A has the same h-level.
--
-- At least one version of the Coq code accompanying "Modalities in
-- Homotopy Type Theory" contains the following comment in
-- connection with the corresponding lemma:
--
--   "With a little more work, this can probably be proven without
--   [Funext]."
--
-- Note that this lemma does not make use of function
-- extensionality.

H-level→H-level-◯ : ∀ n → H-level n A → H-level n (◯ A)
H-level→H-level-◯ {A = A} n =
  H-level n A       ↝⟨ H-level↔H-level′ _ ⟩
  H-level′ n A      ↝⟨ H-level′→H-level′-◯ n ⟩
  H-level′ n (◯ A)  ↝⟨ _⇔_.from (H-level↔H-level′ _) ⟩□
  H-level n (◯ A)   □

------------------------------------------------------------------------
-- Connectedness

-- The function f is ◯-connected if and only if ◯-map f is an
-- equivalence.

Connected-→≃Is-equivalence-◯-map :
  ◯ -Connected-→ f ↝[ a ∣ a ] Is-equivalence (◯-map f)
Connected-→≃Is-equivalence-◯-map {f = f} =
  generalise-ext?-prop
    (record
       { to   = Connected→Is-equivalence-◯-map
       ; from =
           _⇔_.to
             (logically-equivalent
                (Equivalent-Left-exact .proj₁)
                (inj₁ F.id)
                (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁
                   F.id))))))))))
             left-exact
       })
    (flip Connected-→-propositional ◯)
    Is-equivalence-propositional

-- If f is ◯-connected and Σ-map {Q = Q} f (g _) is ◯-connected (for
-- g : ∀ x → P x → Q (f x)), then g x is ◯-connected for all x.

Connected-→-Σ-map→Π-Connected-→ :
  {g : ∀ x → P x → Q (f x)} →
  ◯ -Connected-→ f →
  ◯ -Connected-→ Σ-map {Q = Q} f (g _) →
  ∀ x → ◯ -Connected-→ g x
Connected-→-Σ-map→Π-Connected-→
  {P = P} {Q = Q} {f = f} {g = g} c-f c-f-g x q =
                                            $⟨ c-h x q (x , refl (f x)) ⟩
  ◯ -Connected (h x q ⁻¹ (x , refl (f x)))  →⟨ Connected-cong _ lemma ⟩□
  ◯ -Connected (g x ⁻¹ q)                   □
  where
  h : ∀ x (q : Q (f x)) →
      Σ-map {Q = Q} f (g _) ⁻¹ (f x , q) → f ⁻¹ f x
  h x _ ((x′ , _) , eq) =
      x′
    , (f x′  ≡⟨ proj₁ (Σ-≡,≡←≡ eq) ⟩∎
       f x   ∎)

  c-h : ∀ x q → ◯ -Connected-→ h x q
  c-h x q =
    _⇔_.to
      (logically-equivalent
         (Equivalent-Left-exact .proj₁)
         (inj₁ F.id) (inj₂ (inj₁ F.id)))
      left-exact
      (c-f-g _)
      (c-f _)

  lemma =
    h x q ⁻¹ (x , refl (f x))                                       ↔⟨⟩

    Σ-map proj₁ (proj₁ ∘ Σ-≡,≡←≡) ⁻¹ (x , refl (f x))               ↔⟨⟩

    Σ-map proj₁ proj₁ ∘ Σ-map id Σ-≡,≡←≡ ⁻¹ (x , refl (f x))        ↝⟨ ∘⁻¹≃ _ _ ⟩

    (∃ λ ((p , _) : Σ-map proj₁ proj₁ ⁻¹ (x , refl (f x))) →
     Σ-map id Σ-≡,≡←≡ ⁻¹ p)                                         ↔⟨ (drop-⊤-right λ _ →
                                                                        _⇔_.to contractible⇔↔⊤ $
                                                                        Preimage.bijection⁻¹-contractible
                                                                          (∃-cong λ _ → inverse Bijection.Σ-≡,≡↔≡) _) ⟩
    Σ-map proj₁ proj₁ ⁻¹ (x , refl (f x))                           ↔⟨⟩

    Σ-map proj₁ id ∘ Σ-map id proj₁ ⁻¹ (x , refl (f x))             ↝⟨ ∘⁻¹≃ _ _ ⟩

    (∃ λ ((p , _) : Σ-map proj₁ id ⁻¹ (x , refl (f x))) →
     Σ-map id proj₁ ⁻¹ p)                                           ↝⟨ (∃-cong λ _ → Σ-map-id-⁻¹≃⁻¹) ⟩

    (∃ λ (((p , eq) , _) : Σ-map proj₁ id ⁻¹ (x , refl (f x))) →
     proj₁ {B = λ eq → subst Q eq (uncurry g p) ≡ q} ⁻¹ eq)         ↝⟨ (Σ-cong Σ-map--id-⁻¹≃⁻¹ λ p →
                                                                        ≡⇒↝ _ $
                                                                        cong (λ ((p , eq) , _) →
                                                                                proj₁ {B = λ eq → subst Q eq (uncurry g p) ≡ q} ⁻¹ eq) $
                                                                        sym $ _≃_.left-inverse-of Σ-map--id-⁻¹≃⁻¹ p) ⟩
    (∃ λ (p@(p′ , _) : proj₁ ⁻¹ x) →
     proj₁ {B = λ eq → subst Q eq (uncurry g p′) ≡ q} ⁻¹
     proj₂ (proj₁ (_≃_.from Σ-map--id-⁻¹≃⁻¹ p)))                    ↝⟨ (∃-cong λ p → ≡⇒↝ _ $
                                                                        cong (proj₁ {B = λ eq → subst Q eq (uncurry g (proj₁ p)) ≡ q} ⁻¹_) $
                                                                        trans-reflʳ _) ⟩
    (∃ λ ((p , eq) : proj₁ ⁻¹ x) →
     proj₁ {B = λ eq → subst Q eq (uncurry g p) ≡ q} ⁻¹ cong f eq)  ↝⟨ (Σ-cong-contra (inverse proj₁-⁻¹≃) λ _ → F.id) ⟩

    (∃ λ (p : P x) →
     proj₁ {B = λ eq → subst Q eq (g x p) ≡ q} ⁻¹ cong f (refl _))  ↝⟨ (∃-cong λ _ → proj₁-⁻¹≃) ⟩

    (∃ λ (p : P x) → subst Q (cong f (refl _)) (g x p) ≡ q)         ↝⟨ (∃-cong λ _ → ≡⇒↝ _ $ cong (_≡ _) $
                                                                        trans (cong (flip (subst Q) _) $ cong-refl _) $
                                                                        subst-refl _ _) ⟩
    (∃ λ (p : P x) → g x p ≡ q)                                     ↔⟨⟩

    g x ⁻¹ q                                                        □

------------------------------------------------------------------------
-- Accessibility

-- If the modality is accessible, with (_ , P , _) as a witness of its
-- accessibility, then every modal family of type P x → Type a is, in
-- a certain sense, constant (assuming function extensionality).

Accessible→ :
  Extensionality a a →
  ((_ , P , _) : Accessible M) →
  ∀ x → (Q : P x → Type a) → (∀ y → Modal (Q y)) →
  ∃ λ (B : Type a) → Modal B × (∀ y → Q y ≃ B)
Accessible→ ext acc@(_ , P , _) x Q m =
                                                $⟨ (λ {_ _ _} → left-exact) ⟩

  Left-exact ◯                                  →⟨ (λ lex → Left-exact→Connected→Modal→≃ lex) ⟩

  (◯ -Connected (P x) → (∀ x → Modal (Q x)) →
   ∃ λ (B : Type a) → Modal B × ∀ y → Q y ≃ B)  →⟨ (λ hyp → hyp (Accessible→Connected ext acc) m) ⟩□

  (∃ λ (B : Type a) → Modal B × ∀ y → Q y ≃ B)  □

------------------------------------------------------------------------
-- Some commutation properties

-- I did not take the lemmas in this section from "Modalities in
-- Homotopy Type Theory" or the corresponding Coq code.

-- ◯ (Injective f) implies Injective (◯-map f).

◯-Injective→Injective : ◯ (Injective f) → Injective (◯-map f)
◯-Injective→Injective {f = f} =
  ◯ (∀ {x y} → f x ≡ f y → x ≡ y)                      →⟨ ◯-map (λ g _ _ → g) ⟩
  ◯ (∀ x y → f x ≡ f y → x ≡ y)                        →⟨ ◯Π→Π◯ ⟩
  (∀ x → ◯ (∀ y → f x ≡ f y → x ≡ y))                  →⟨ (∀-cong _ λ _ → ◯Π→Π◯) ⟩
  (∀ x y → ◯ (f x ≡ f y → x ≡ y))                      →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → ◯-map-◯) ⟩
  (∀ x y → ◯ (f x ≡ f y) → ◯ (x ≡ y))                  →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                           →-cong-→ (_≃_.from ◯≡≃η≡η) η-cong) ⟩
  (∀ x y → η (f x) ≡ η (f y) → η x ≡ η y)              →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                           →-cong-→ (≡⇒↝ _ $ cong₂ _≡_ ◯-map-η ◯-map-η) id) ⟩
  (∀ x y → ◯-map f (η x) ≡ ◯-map f (η y) → η x ≡ η y)  →⟨ (∀-cong _ λ _ → _⇔_.from $ Π◯⇔Πη s′) ⟩
  (∀ x y → ◯-map f (η x) ≡ ◯-map f y → η x ≡ y)        →⟨ (_⇔_.from $ Π◯⇔Πη λ _ → Stable-Π s′) ⟩
  (∀ x y → ◯-map f x ≡ ◯-map f y → x ≡ y)              →⟨ (λ g → g _ _) ⟩□
  (∀ {x y} → ◯-map f x ≡ ◯-map f y → x ≡ y)            □
  where
  s′ : ∀ {x} y → Stable (◯-map f x ≡ ◯-map f y → x ≡ y)
  s′ _ = Stable-Π λ _ → Modal→Stable $ Separated-◯ _ _

-- ◯ (A ↣ B) implies ◯ A ↣ ◯ B.

◯-cong-↣-◯ : ◯ (A ↣ B) → ◯ A ↣ ◯ B
◯-cong-↣-◯ =
  ◯↝→◯↝◯
    ↣↔∃-Injective
    ◯-Injective→Injective
    (Injective-cong _)
    (Stable-implicit-Π λ _ → Stable-implicit-Π λ _ → Stable-Π λ _ →
     Modal→Stable $ Separated-◯ _ _)

-- A lemma used in the implementations of ◯-Is-embedding→Is-embedding
-- and Modality.Has-choice.◯-Is-embedding≃Is-embedding.

◯-map-cong≡ :
  (p : ◯ (x ≡ y)) →
  ◯-map (cong f) p ≡
  (η-cong⁻¹ ∘
   _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
   cong (◯-map f) ∘
   η-cong) p
◯-map-cong≡ {f = f} =
  ◯-elim (λ _ → Separated-◯ _ _) $
  elim¹
    (λ p →
       ◯-map (cong f) (η p) ≡
       η-cong⁻¹
         (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η))
            (cong (◯-map f) (η-cong (η p)))))
    (◯-map (cong f) (η (refl _))                                         ≡⟨ trans ◯-map-η $
                                                                            cong η $ cong-refl _ ⟩

     η (refl _)                                                          ≡⟨ sym η-cong⁻¹-η ⟩

     η-cong⁻¹ (refl _)                                                   ≡⟨ cong η-cong⁻¹ $
                                                                            trans (sym $ trans-symˡ _) $
                                                                            cong (flip trans _) $
                                                                            sym $ trans-reflʳ _ ⟩

     η-cong⁻¹ (trans (trans (sym ◯-map-η) (refl _)) ◯-map-η)             ≡⟨ cong η-cong⁻¹ $
                                                                            trans trans-subst $
                                                                            cong (subst (_ ≡_) _) $
                                                                            sym subst-trans-sym ⟩
     η-cong⁻¹
       (subst (η _ ≡_) ◯-map-η (subst (_≡ ◯-map _ _) ◯-map-η (refl _)))  ≡⟨ cong η-cong⁻¹ $ sym $
                                                                            ≡⇒↝-cong₂≡subst-subst equivalence {P = _≡_} ⟩
     η-cong⁻¹
       (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) (refl _))             ≡⟨ cong η-cong⁻¹ $ cong (_≃_.to (≡⇒↝ _ _)) $
                                                                            trans (sym $ cong-refl _) $
                                                                            cong (cong (◯-map f)) $
                                                                            trans (sym $ cong-refl _) $
                                                                            sym η-cong-η ⟩∎
     η-cong⁻¹
       (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η))
          (cong (◯-map f) (η-cong (η (refl _)))))                        ∎)

-- ◯ (Is-embedding f) implies Is-embedding (◯-map f).

◯-Is-embedding→Is-embedding :
  ◯ (Is-embedding f) → Is-embedding (◯-map f)
◯-Is-embedding→Is-embedding {f = f} =
  ◯ (∀ x y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y)))             →⟨ ◯Π→Π◯ ⟩

  (∀ x → ◯ (∀ y → Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))       →⟨ (∀-cong _ λ _ → ◯Π→Π◯) ⟩

  (∀ x y → ◯ (Is-equivalence (cong f ⦂ (x ≡ y → f x ≡ f y))))           →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                                            ◯-Is-equivalence→Is-equivalence) ⟩

  (∀ x y → Is-equivalence (◯-map (cong f ⦂ (x ≡ y → f x ≡ f y))))       →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → Is-equivalence-cong _
                                                                            ◯-map-cong≡) ⟩
  (∀ x y →
     Is-equivalence
       (η-cong⁻¹ ∘
        _≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
        cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → ◯ (f x ≡ f y))))         →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → _⇔_.from $
                                                                            Is-equivalence≃Is-equivalence-∘ˡ
                                                                              (_≃_.is-equivalence $ inverse ◯≡≃η≡η) _) ⟩
  (∀ x y →
     Is-equivalence
       (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
        cong (◯-map f) ∘ η-cong ⦂ (◯ (x ≡ y) → η (f x) ≡ η (f y))))     →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → _⇔_.from $
                                                                            Is-equivalence≃Is-equivalence-∘ʳ lex _) ⟩
  (∀ x y →
     Is-equivalence
       (_≃_.to (≡⇒↝ _ (cong₂ _≡_ ◯-map-η ◯-map-η)) ∘
        cong (◯-map f) ⦂ (η x ≡ η y → η (f x) ≡ η (f y))))              →⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → _⇔_.from $
                                                                            Is-equivalence≃Is-equivalence-∘ˡ
                                                                              (_≃_.is-equivalence $ ≡⇒↝ _ _) _) ⟩
  (∀ x y →
     Is-equivalence
       (cong (◯-map f) ⦂ (η x ≡ η y → ◯-map f (η x) ≡ ◯-map f (η y))))  →⟨ (_⇔_.from $
                                                                            Π◯⇔Πη λ _ → Stable-Π λ _ →
                                                                            Modal→Stable-Is-equivalence
                                                                              (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _))) ⟩
  (∀ x y →
     Is-equivalence
       (cong (◯-map f) ⦂ (x ≡ η y → ◯-map f x ≡ ◯-map f (η y))))        →⟨ (∀-cong _ λ _ → _⇔_.from $
                                                                            Π◯⇔Πη λ _ →
                                                                            Modal→Stable-Is-equivalence
                                                                              (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _))) ⟩□
  (∀ x y →
     Is-equivalence
       (cong (◯-map f) ⦂ (x ≡ y → ◯-map f x ≡ ◯-map f y)))              □

-- ◯ (Embedding A B) implies Embedding (◯ A) (◯ B).

◯-cong-Embedding-◯ : ◯ (Embedding A B) → Embedding (◯ A) (◯ B)
◯-cong-Embedding-◯ =
  ◯↝→◯↝◯
    Emb.Embedding-as-Σ
    ◯-Is-embedding→Is-embedding
    (Is-embedding-cong _)
    (Stable-Π λ _ → Stable-Π λ _ →
     Modal→Stable-Is-equivalence
       (Separated-◯ _ _) (Modal→Separated (Separated-◯ _ _)))

------------------------------------------------------------------------
-- Some lemmas related to _[_]◯_

-- I did not take the lemmas in this section from "Modalities in
-- Homotopy Type Theory" or the corresponding Coq code.

-- The type η x [ _<_ ]◯ η y is equivalent to ◯ (x < y).

η-[]◯-η≃◯ : (η x [ _<_ ]◯ η y) ≃ ◯ (x < y)
η-[]◯-η≃◯ {x = x} {_<_ = _<_} {y = y} =
  η x [ _<_ ]◯ η y                                           ↔⟨⟩

  ◯ (∃ λ x′ → ∃ λ y′ → η x ≡ η x′ × η y ≡ η y′ × (x′ < y′))  ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ∃-cong λ _ → inverse $
                                                                 ◯≡≃η≡η ×-cong ◯≡≃η≡η ×-cong F.id) ⟩

  ◯ (∃ λ x′ → ∃ λ y′ → ◯ (x ≡ x′) × ◯ (y ≡ y′) × (x′ < y′))  ↝⟨ flatten-≃
                                                                  (λ F → ∃ λ x′ → ∃ λ y′ → F (x ≡ x′) × F (y ≡ y′) × (x′ < y′))
                                                                  (λ f → Σ-map id (Σ-map id (Σ-map f (Σ-map f id))))
                                                                  (λ (x′ , y′ , p , q , r) →
                                                                     ◯-map (λ (p , q) → x′ , y′ , p , q , r) $
                                                                     _≃_.from ◯× (p , q))
                                                                  lemma
                                                                  (λ (x′ , y′ , p , q , r) →
                                                                     ◯-elim
                                                                       {P = λ p →
                                                                              ◯-map (Σ-map id (Σ-map id (Σ-map η (Σ-map η id))))
                                                                                (◯-map (λ (p , q) → x′ , y′ , p , q , r)
                                                                                   (_≃_.from ◯× (p , q))) ≡
                                                                              η (x′ , y′ , p , q , r)}
                                                                       (λ _ → Separated-◯ _ _)
                                                                       (λ p →
                                                                          ◯-elim
                                                                            {P = λ q →
                                                                                   ◯-map (Σ-map id (Σ-map id (Σ-map η (Σ-map η id))))
                                                                                     (◯-map (λ (p , q) → x′ , y′ , p , q , r)
                                                                                        (_≃_.from ◯× (η p , q))) ≡
                                                                                   η (x′ , y′ , η p , q , r)}
                                                                            (λ _ → Separated-◯ _ _)
                                                                            (λ q →
    ◯-map (Σ-map id (Σ-map id (Σ-map η (Σ-map η id))))
      (◯-map (λ (p , q) → x′ , y′ , p , q , r)
         (_≃_.from ◯× (η p , η q)))                                            ≡⟨ cong (◯-map _) $
                                                                                  lemma _ ⟩
    ◯-map (Σ-map id (Σ-map id (Σ-map η (Σ-map η id))))
      (η (x′ , y′ , p , q , r))                                                ≡⟨ ◯-map-η ⟩∎

    η (x′ , y′ , η p , η q , r)                                                ∎)
                                                                            q)
                                                                       p) ⟩

  ◯ (∃ λ x′ → ∃ λ y′ → x ≡ x′ × y ≡ y′ × (x′ < y′))          ↔⟨ ◯-cong-↔ $
                                                                (∃-cong λ _ → Σ-assoc) F.∘
                                                                Σ-assoc F.∘
                                                                (∃-cong λ _ → ∃-comm) ⟩
  ◯ (∃ λ ((x′ , _) : ∃ λ x′ → x ≡ x′) →
     ∃ λ ((y′ , _) : ∃ λ y′ → y ≡ y′) →
     x′ < y′)                                                ↔⟨ ◯-cong-↔ $
                                                                drop-⊤-left-Σ $
                                                                _⇔_.to contractible⇔↔⊤ $
                                                                other-singleton-contractible _ ⟩

  ◯ (∃ λ ((y′ , _) : ∃ λ y′ → y ≡ y′) → x < y′)              ↔⟨ ◯-cong-↔ $
                                                                drop-⊤-left-Σ $
                                                                _⇔_.to contractible⇔↔⊤ $
                                                                other-singleton-contractible _ ⟩□
  ◯ (x < y)                                                  □
  where
  lemma = λ (x′ , y′ , p , q , r) →
    ◯-map (λ (p , q) → x′ , y′ , p , q , r) (_≃_.from ◯× (η p , η q))  ≡⟨ cong (◯-map _) ◯×⁻¹-η ⟩
    ◯-map (λ (p , q) → x′ , y′ , p , q , r) (η (p , q))                ≡⟨ ◯-map-η ⟩∎
    η (x′ , y′ , p , q , r)                                            ∎

-- The function _[ _<_ ]◯_ is pointwise logically equivalent to any
-- pointwise stable relation R (of a certain type) for which
-- R (η x) (η y) ⇔ ◯ (x < y) holds for all x and y.

⇔[]◯ :
  {R : ◯ A → ◯ A → Type a} →
  (∀ {x y} → Stable (R x y)) →
  (∀ {x y} → R (η x) (η y) ⇔ ◯ (x < y)) →
  R x y ⇔ (x [ _<_ ]◯ y)
⇔[]◯ {_<_ = _<_} {x = x} {y = y} {R = R} s Rηη⇔◯< =
  ◯-elim′
    {P = λ x → R x y ⇔ (x [ _<_ ]◯ y)}
    (λ _ → Stable-⇔ s (Modal→Stable Modal-◯))
    (λ x →
       ◯-elim′
         {P = λ y → R (η x) y ⇔ (η x [ _<_ ]◯ y)}
         (λ _ → Stable-⇔ s (Modal→Stable Modal-◯))
         (λ y →
            R (η x) (η y)     ↝⟨ Rηη⇔◯< ⟩
            ◯ (x < y)         ↔⟨ inverse η-[]◯-η≃◯ ⟩□
            η x [ _<_ ]◯ η y  □)
         y)
    x

-- In the presence of function extensionality _[ _<_ ]◯_ is pointwise
-- equivalent to any pointwise modal relation R (of a certain type)
-- for which R (η x) (η y) ≃ ◯ (x < y) holds for all x and y.

≃[]◯ :
  {R : ◯ A → ◯ A → Type a} →
  Extensionality a a →
  (∀ {x y} → Modal (R x y)) →
  (∀ {x y} → R (η x) (η y) ≃ ◯ (x < y)) →
  R x y ≃ (x [ _<_ ]◯ y)
≃[]◯ {_<_ = _<_} {x = x} {y = y} {R = R} ext m Rηη≃◯< =
  ◯-elim
    {P = λ x → R x y ≃ (x [ _<_ ]◯ y)}
    (λ _ → Modal-≃ ext m Modal-◯)
    (λ x →
       ◯-elim
         {P = λ y → R (η x) y ≃ (η x [ _<_ ]◯ y)}
         (λ _ → Modal-≃ ext m Modal-◯)
         (λ y →
            R (η x) (η y)     ↝⟨ Rηη≃◯< ⟩
            ◯ (x < y)         ↝⟨ inverse η-[]◯-η≃◯ ⟩□
            η x [ _<_ ]◯ η y  □)
         y)
    x
