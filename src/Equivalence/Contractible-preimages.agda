------------------------------------------------------------------------
-- Is-equivalence, defined in terms of contractible fibres
------------------------------------------------------------------------

-- Partly based on Voevodsky's work on univalent foundations.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Contractible-preimages
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Prelude as P hiding (id)

open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import H-level eq as H-level
open import H-level.Closure eq
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq using (_↠_)

private
  variable
    a b ℓ p q : Level
    A B       : Type a
    f g       : A → B

------------------------------------------------------------------------
-- Is-equivalence

-- A function f is an equivalence if all preimages under f are
-- contractible.

Is-equivalence :
  {A : Type a} {B : Type b} →
  (A → B) → Type (a ⊔ b)
Is-equivalence f = ∀ y → Contractible (f ⁻¹ y)

abstract

  -- Is-equivalence f is a proposition, assuming extensional equality.

  propositional :
    Extensionality (a ⊔ b) (a ⊔ b) →
    {A : Type a} {B : Type b} (f : A → B) →
    Is-proposition (Is-equivalence f)
  propositional {a = a} ext f =
    Π-closure (lower-extensionality a lzero ext) 1 λ _ →
      Contractible-propositional ext

  -- If the domain is contractible and the codomain is propositional,
  -- then Is-equivalence f is contractible.

  sometimes-contractible :
    Extensionality (a ⊔ b) (a ⊔ b) →
    {A : Type a} {B : Type b} {f : A → B} →
    Contractible A → Is-proposition B →
    Contractible (Is-equivalence f)
  sometimes-contractible {a = a} ext A-contr B-prop =
    Π-closure (lower-extensionality a lzero ext) 0 λ _ →
      cojoin ext (Σ-closure 0 A-contr (λ _ → +⇒≡ B-prop))

  -- Is-equivalence f is not always contractible.

  not-always-contractible₁ :
    ∃ λ (A : Type a) → ∃ λ (B : Type b) → ∃ λ (f : A → B) →
      Is-proposition A × Contractible B ×
      ¬ Contractible (Is-equivalence f)
  not-always-contractible₁ =
    ⊥ ,
    ↑ _ ⊤ ,
    const (lift tt) ,
    ⊥-propositional ,
    ↑-closure 0 ⊤-contractible ,
    λ c → ⊥-elim (proj₁ (proj₁ (proj₁ c (lift tt))))

  not-always-contractible₂ :
    ∃ λ (A : Type a) → ∃ λ (B : Type b) → ∃ λ (f : A → B) →
      Contractible A × Is-set B ×
      ¬ Contractible (Is-equivalence f)
  not-always-contractible₂ =
    ↑ _ ⊤ ,
    ↑ _ Bool ,
    const (lift true) ,
    ↑-closure 0 ⊤-contractible ,
    ↑-closure 2 Bool-set ,
    λ c → Bool.true≢false (cong lower
            (proj₂ (proj₁ (proj₁ c (lift false)))))

-- Is-equivalence respects extensional equality.

respects-extensional-equality :
  (∀ x → f x ≡ g x) →
  Is-equivalence f → Is-equivalence g
respects-extensional-equality f≡g f-eq = λ b →
  H-level.respects-surjection
    (_↔_.surjection (Preimage.respects-extensional-equality f≡g))
    0
    (f-eq b)

-- If f is an equivalence, then it has an inverse.

inverse :
  {f : A → B} → Is-equivalence f → B → A
inverse eq y = proj₁ (proj₁ (eq y))

right-inverse-of :
  (eq : Is-equivalence f) → ∀ x → f (inverse eq x) ≡ x
right-inverse-of eq x = proj₂ (proj₁ (eq x))

abstract

  left-inverse-of :
    (eq : Is-equivalence f) → ∀ x → inverse eq (f x) ≡ x
  left-inverse-of {f = f} eq x =
    cong (proj₁ {B = λ x′ → f x′ ≡ f x}) (
      proj₁ (eq (f x))  ≡⟨ proj₂ (eq (f x)) (x , refl (f x)) ⟩∎
      (x , refl (f x))  ∎)

-- All fibres of an equivalence over a given point are equal to a
-- given fibre.

irrelevance :
  (eq : Is-equivalence f) →
  ∀ y (p : f ⁻¹ y) → (inverse eq y , right-inverse-of eq y) ≡ p
irrelevance eq y = proj₂ (eq y)

abstract

  -- The two proofs left-inverse-of and right-inverse-of are
  -- related.

  left-right-lemma :
    (eq : Is-equivalence f) →
    ∀ x → cong f (left-inverse-of eq x) ≡ right-inverse-of eq (f x)
  left-right-lemma {f = f} eq x =
    lemma₁ f _ _ (lemma₂ (irrelevance eq (f x) (x , refl (f x))))
    where
    lemma₁ : {x y : A} (f : A → B) (p : x ≡ y) (q : f x ≡ f y) →
             refl (f y) ≡ trans (cong f (sym p)) q →
             cong f p ≡ q
    lemma₁ f = elim
      (λ {x y} p → ∀ q → refl (f y) ≡ trans (cong f (sym p)) q →
                         cong f p ≡ q)
      (λ x q hyp →
         cong f (refl x)                  ≡⟨ cong-refl f ⟩
         refl (f x)                       ≡⟨ hyp ⟩
         trans (cong f (sym (refl x))) q  ≡⟨ cong (λ p → trans (cong f p) q) sym-refl ⟩
         trans (cong f (refl x)) q        ≡⟨ cong (λ p → trans p q) (cong-refl f) ⟩
         trans (refl (f x)) q             ≡⟨ trans-reflˡ _ ⟩∎
         q                                ∎)

    lemma₂ : ∀ {f : A → B} {y} {f⁻¹y₁ f⁻¹y₂ : f ⁻¹ y}
             (p : f⁻¹y₁ ≡ f⁻¹y₂) →
             proj₂ f⁻¹y₂ ≡
             trans (cong f (sym (cong (proj₁ {B = λ x → f x ≡ y}) p)))
                   (proj₂ f⁻¹y₁)
    lemma₂ {f = f} {y = y} =
      let pr = proj₁ {B = λ x → f x ≡ y} in
      elim {A = f ⁻¹ y}
        (λ {f⁻¹y₁ f⁻¹y₂} p →
           proj₂ f⁻¹y₂ ≡
             trans (cong f (sym (cong pr p))) (proj₂ f⁻¹y₁))
        (λ f⁻¹y →
           proj₂ f⁻¹y                                               ≡⟨ sym $ trans-reflˡ _ ⟩
           trans (refl (f (proj₁ f⁻¹y))) (proj₂ f⁻¹y)               ≡⟨ cong (λ p → trans p (proj₂ f⁻¹y)) (sym (cong-refl f)) ⟩
           trans (cong f (refl (proj₁ f⁻¹y))) (proj₂ f⁻¹y)          ≡⟨ cong (λ p → trans (cong f p) (proj₂ f⁻¹y)) (sym sym-refl) ⟩
           trans (cong f (sym (refl (proj₁ f⁻¹y)))) (proj₂ f⁻¹y)    ≡⟨ cong (λ p → trans (cong f (sym p)) (proj₂ f⁻¹y))
                                                                            (sym (cong-refl pr)) ⟩∎
           trans (cong f (sym (cong pr (refl f⁻¹y)))) (proj₂ f⁻¹y)  ∎)

  right-left-lemma :
    (eq : Is-equivalence f) →
    ∀ x →
    cong (inverse eq) (right-inverse-of eq x) ≡
    left-inverse-of eq (inverse eq x)
  right-left-lemma {f = f} eq x = subst
    (λ x → cong f⁻¹ (right-inverse-of eq x) ≡
           left-inverse-of eq (f⁻¹ x))
    (right-inverse-of eq x)
    (cong f⁻¹ (right-inverse-of eq (f (f⁻¹ x)))             ≡⟨ cong (cong f⁻¹) $ sym $ left-right-lemma eq _ ⟩

     cong f⁻¹ (cong f (left-inverse-of eq (f⁻¹ x)))         ≡⟨ cong-∘ f⁻¹ f _ ⟩

     cong (f⁻¹ ∘ f) (left-inverse-of eq (f⁻¹ x))            ≡⟨ cong-roughly-id (f⁻¹ ∘ f) (λ _ → true) (left-inverse-of eq _) _ _
                                                                 (λ z _ → left-inverse-of eq z) ⟩
     trans (left-inverse-of eq (f⁻¹ (f (f⁻¹ x))))
       (trans (left-inverse-of eq (f⁻¹ x))
          (sym (left-inverse-of eq (f⁻¹ x))))               ≡⟨ cong (trans _) $ trans-symʳ _ ⟩

     trans (left-inverse-of eq (f⁻¹ (f (f⁻¹ x)))) (refl _)  ≡⟨ trans-reflʳ _ ⟩∎

     left-inverse-of eq (f⁻¹ (f (f⁻¹ x)))                   ∎)
    where
    f⁻¹ = inverse eq

abstract

  -- If Σ-map P.id f is an equivalence, then f is also an equivalence.

  drop-Σ-map-id :
    {A : Type a} {P : A → Type p} {Q : A → Type q}
    (f : ∀ {x} → P x → Q x) →
    Is-equivalence {A = Σ A P} {B = Σ A Q} (Σ-map P.id f) →
    ∀ x → Is-equivalence (f {x = x})
  drop-Σ-map-id {A = A} {P = P} {Q = Q} f eq x z =
    H-level.respects-surjection surj 0 (eq (x , z))
    where
    map-f : Σ A P → Σ A Q
    map-f = Σ-map P.id f

    to-P : ∀ {x y} {p : ∃ Q} → (x , f y) ≡ p → Type _
    to-P {y = y} {p} _ = ∃ λ y′ → f y′ ≡ proj₂ p

    to : map-f ⁻¹ (x , z) → f ⁻¹ z
    to ((x′ , y) , eq) = elim¹ to-P (y , refl (f y)) eq

    from : f ⁻¹ z → map-f ⁻¹ (x , z)
    from (y , eq) = (x , y) , cong (_,_ x) eq

    to∘from : ∀ p → to (from p) ≡ p
    to∘from (y , eq) = elim¹
      (λ {z′} (eq : f y ≡ z′) →
         _≡_ {A = ∃ λ (y : P x) → f y ≡ z′}
             (elim¹ to-P (y , refl (f y)) (cong (_,_ x) eq))
             (y , eq))
      (elim¹ to-P (y , refl (f y)) (cong (_,_ x) (refl (f y)))  ≡⟨ cong (elim¹ to-P (y , refl (f y))) $
                                                                        cong-refl (_,_ x) ⟩
       elim¹ to-P (y , refl (f y)) (refl (x , f y))             ≡⟨ elim¹-refl to-P _ ⟩∎
       (y , refl (f y))                                         ∎)
      eq

    surj : map-f ⁻¹ (x , z) ↠ f ⁻¹ z
    surj = record
      { logical-equivalence = record { to = to; from = from }
      ; right-inverse-of    = to∘from
      }

  -- A "computation" rule for drop-Σ-map-id.

  inverse-drop-Σ-map-id :
    {A : Type a} {P : A → Type p} {Q : A → Type q}
    {f : ∀ {x} → P x → Q x} {x : A} {y : Q x}
    {eq : Is-equivalence {A = Σ A P} {B = Σ A Q} (Σ-map P.id f)} →
    inverse (drop-Σ-map-id f eq x) y ≡
    subst P (cong proj₁ (right-inverse-of eq (x , y)))
      (proj₂ (inverse eq (x , y)))
  inverse-drop-Σ-map-id
    {P = P} {Q = Q} {f = f} {x = x} {y = y} {eq = eq} =

    proj₁
      (subst
         (λ ((_ , y) , _) → f ⁻¹ y)
         (proj₂
            (other-singleton-contractible (Σ-map P.id f p′))
            (q′ , right-inverse-of eq q′))
         (proj₂ p′ , refl _))                                 ≡⟨ cong proj₁ $ push-subst-pair _ _ ⟩

    subst
      (λ ((x , _) , _) → P x)
      (proj₂
         (other-singleton-contractible (Σ-map P.id f p′))
         (q′ , right-inverse-of eq q′))
      (proj₂ p′)                                              ≡⟨ trans (subst-∘ _ _ _) (subst-∘ _ _ _) ⟩

    subst P
      (cong proj₁ $ cong proj₁ $
       proj₂
         (other-singleton-contractible (Σ-map P.id f p′))
         (q′ , right-inverse-of eq q′))
      (proj₂ p′)                                              ≡⟨ cong (λ eq → subst P (cong proj₁ eq) (proj₂ p′))
                                                                 lemma ⟩∎
    subst P
      (cong proj₁ (right-inverse-of eq q′))
      (proj₂ p′)                                              ∎
    where
    q′ : ∃ Q
    q′ = x , y

    p′ : ∃ P
    p′ = inverse eq q′

    lemma = elim¹
      (λ {q′} eq →
         cong proj₁
           (proj₂ (other-singleton-contractible (Σ-map P.id f p′))
              (q′ , eq)) ≡
         eq)
      (cong proj₁
         (proj₂ (other-singleton-contractible (Σ-map P.id f p′))
            (Σ-map P.id f p′ , refl _))                           ≡⟨ cong (cong proj₁) $
                                                                     other-singleton-contractible-refl _ ⟩

       cong proj₁ (refl _)                                        ≡⟨ cong-refl _ ⟩∎

       refl _                                                     ∎)
      _

------------------------------------------------------------------------
-- _≃_

-- A notion of equivalence.

infix 4 _≃_

_≃_ : Type a → Type b → Type (a ⊔ b)
A ≃ B = ∃ λ (f : A → B) → Is-equivalence f

-- An identity equivalence.

id : A ≃ A
id = P.id , singleton-contractible

-- Equalities can be converted to equivalences.

≡⇒≃ : A ≡ B → A ≃ B
≡⇒≃ = elim (λ {A B} _ → A ≃ B) (λ _ → id)

-- If ≡⇒≃ is applied to reflexivity, then the result is equal to id.

≡⇒≃-refl : ≡⇒≃ (refl A) ≡ id
≡⇒≃-refl = elim-refl (λ {A B} _ → A ≃ B) (λ _ → id)

-- Univalence for fixed types.

Univalence′ : (A B : Type ℓ) → Type (lsuc ℓ)
Univalence′ A B = Is-equivalence (≡⇒≃ {A = A} {B = B})

-- Univalence.

Univalence : ∀ ℓ → Type (lsuc ℓ)
Univalence ℓ = {A B : Type ℓ} → Univalence′ A B
