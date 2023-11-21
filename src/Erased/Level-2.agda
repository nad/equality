------------------------------------------------------------------------
-- A type for values that should be erased at run-time
------------------------------------------------------------------------

-- The definitions in this module are reexported from Erased.

-- This module imports Equivalence.Erased.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
open import Prelude hiding ([_,_])

module Erased.Level-2
  {c⁺} (eq-J : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq-J

open import Logical-equivalence using (_⇔_)

open import Bijection eq-J as Bijection using (_↔_; Has-quasi-inverse)
open import Embedding eq-J as Emb using (Embedding; Is-embedding)
open import Equivalence eq-J as Eq using (_≃_; Is-equivalence)
open import Equivalence.Erased eq-J as EEq
  using (_≃ᴱ_; Is-equivalenceᴱ)
open import Extensionality eq-J
open import Function-universe eq-J as F hiding (id; _∘_)
open import H-level eq-J as H-level
open import H-level.Closure eq-J
open import Injection eq-J using (_↣_; Injective)
open import Monad eq-J hiding (map; map-id; map-∘)
open import Preimage eq-J using (_⁻¹_)
open import Surjection eq-J as S using (_↠_; Split-surjective)

open import Erased.Level-1 eq-J as E₁
  hiding (module []-cong; module []-cong₂-⊔)

private

  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B              : Type a
    eq k k′ p x y    : A
    P                : A → Type p
    f g              : A → B
    n                : ℕ

------------------------------------------------------------------------
-- Results that depend on an instantiation of the []-cong axioms (for
-- two universe levels as well as their maximum)

module []-cong₂-⊔
  (ax₁ : E₁.[]-cong-axiomatisation ℓ₁)
  (ax₂ : E₁.[]-cong-axiomatisation ℓ₂)
  (ax  : E₁.[]-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  where

  open E₁.Erased-cong ax ax
  open E₁.[]-cong₁ ax₂
  open E₁.[]-cong₂ ax₁ ax₂
  open E₁.[]-cong₂-⊔ ax₁ ax₂ ax

  private

    module EEq₁   = EEq.[]-cong₁ ax
    module EEq₂-⊔ = EEq.[]-cong₂-⊔ ax₁ ax₂ ax

  ----------------------------------------------------------------------
  -- Erased commutes with all kinds of functions (in some cases
  -- assuming extensionality)

  -- Erased "commutes" with Has-quasi-inverse (assuming function
  -- extensionality).

  Erased-Has-quasi-inverse↔Has-quasi-inverse :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 f : A → B} →
    Erased (Has-quasi-inverse f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
    Has-quasi-inverse (map f)
  Erased-Has-quasi-inverse↔Has-quasi-inverse {f} ext =
    Erased (∃ λ g → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x))            ↔⟨ Erased-Σ↔Σ ⟩

    (∃ λ g →
       Erased ((∀ x → f (erased g x) ≡ x) × (∀ x → erased g (f x) ≡ x)))  ↔⟨ (∃-cong λ _ → Erased-Σ↔Σ) ⟩

    (∃ λ g →
       Erased (∀ x → f (erased g x) ≡ x) ×
       Erased (∀ x → erased g (f x) ≡ x))                                 ↝⟨ (EEq₁.Σ-cong-contra-Erased′
                                                                                (lower-extensionality? _ ℓ₁ ℓ₂ ext)
                                                                                Π-Erased≃Erased-Π λ g →
                                                                              lemma₁ g (lower-extensionality? _ ℓ₁ ℓ₁ ext)
                                                                                ×-cong
                                                                              lemma₂ g (lower-extensionality? _ ℓ₂ ℓ₂ ext)) ⟩□
    (∃ λ g → (∀ x → map f (g x) ≡ x) × (∀ x → g (map f x) ≡ x))           □
    where
    lemma₁ :
      ∀ g →
      Erased (∀ x → erased (map f (g [ x ])) ≡ x) ↝[ ℓ₂ ∣ ℓ₂ ]
      (∀ x → map f (g x) ≡ x)
    lemma₁ g ext =
      Erased (∀ x → erased (map f (g [ x ])) ≡ x)                  ↝⟨ Erased-Π↔Π-Erased ext ⟩
      (∀ x → Erased (erased (map f (g [ erased x ])) ≡ erased x))  ↝⟨ (∀-cong ext λ { [ _ ] → F.id }) ⟩
      (∀ x → Erased (erased (map f (g x)) ≡ erased x))             ↝⟨ (∀-cong ext λ _ → from-isomorphism Erased-≡≃≡) ⟩□
      (∀ x → map f (g x) ≡ x)                                      □

    lemma₂ :
      ∀ g →
      Erased (∀ x → erased (g (map f [ x ])) ≡ x) ↝[ ℓ₁ ∣ ℓ₁ ]
      (∀ x → g (map f x) ≡ x)
    lemma₂ g ext =
      Erased (∀ x → erased (g (map f [ x ])) ≡ x)                  ↝⟨ Erased-Π↔Π-Erased ext ⟩
      (∀ x → Erased (erased (g (map f [ erased x ])) ≡ erased x))  ↝⟨ (∀-cong ext λ { [ _ ] → F.id }) ⟩
      (∀ x → Erased (erased (g (map f x)) ≡ erased x))             ↝⟨ (∀-cong ext λ _ → from-isomorphism $ E₁.[]-cong₁.Erased-≡≃≡ ax₁) ⟩□
      (∀ x → g (map f x) ≡ x)                                      □

  private

    -- A lemma used in the proof of Erased-↝↝↝.

    Erased-↝↝↝-lemma :
      (P : {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)) →

      (∀ {k} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} →
       Extensionality? k (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂) →
       (∀ x → f x ≡ g x) → P f ↝[ k ] P g) →

      ({A : Type ℓ₁} {B : Type ℓ₂} →
       (A ↝[ k ] B) ↔ (∃ λ (f : A → B) → P f)) →

      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →

      ({@0 f : A → B} →
       Erased (P f) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] P (map f)) →

      Erased (A ↝[ k ] B) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ]
      (Erased A ↝[ k ] Erased B)
    Erased-↝↝↝-lemma {k} P P-cong ↝↔Σ {A} {B} Erased↝map =
      with-other-function-→
        (λ ext →
           lemma $
           EEq₁.Σ-cong-contra-Erased′
             (lower-extensionality? _ ℓ₂ ℓ₁ ext)
             Π-Erased≃Erased-Π
             (λ f →
                Erased (P (erased ∘ f ∘ [_]→))  ↝⟨ Erased↝map ext ⟩
                P (map (erased ∘ f ∘ [_]→))     ↝⟨ P-cong ext (λ { [ _ ] → Erased-η }) ⟩□
                P f                             □))
        (lemma λ ([ f ] , p) → map f , Erased↝map _ p)
      where
      lemma : ∀ {k} → _ ↝[ k ] _ → _
      lemma hyp =
        Erased (A ↝[ k ] B)                                 ↔⟨ Erased-cong-↔ ↝↔Σ ⟩
        Erased (∃ λ (f : A → B) → P f)                      ↔⟨ Erased-Σ↔Σ ⟩
        (∃ λ (f : Erased (A → B)) → Erased (P (erased f)))  ↝⟨ hyp ⟩
        (∃ λ (f : Erased A → Erased B) → P f)               ↔⟨ inverse ↝↔Σ ⟩□
        Erased A ↝[ k ] Erased B                            □

  -- Erased commutes with all kinds of functions (in some cases
  -- assuming extensionality).

  Erased-↝↝↝ :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    Erased (A ↝[ k ] B) ↝[ ℓ₁ ⊔ ℓ₂ ∣ ℓ₁ ⊔ ℓ₂ ] (Erased A ↝[ k ] Erased B)
  Erased-↝↝↝ {k = implication} =
    Erased-Π↔Π-Erased ∘ lower-extensionality? _ ℓ₂ ℓ₁

  Erased-↝↝↝ {k = logical-equivalence} =
    Erased-⇔↔⇔

  Erased-↝↝↝ {k = injection} =
    Erased-↝↝↝-lemma
      Injective
      (λ ext → Injective-cong (lower-extensionality? _ ℓ₂ lzero ext))
      ↣↔∃-Injective
      Erased-Injective↔Injective

  Erased-↝↝↝ {k = embedding} =
    Erased-↝↝↝-lemma
      Is-embedding
      Is-embedding-cong
      Emb.Embedding-as-Σ
      Erased-Is-embedding↔Is-embedding

  Erased-↝↝↝ {k = surjection} =
    Erased-↝↝↝-lemma
      Split-surjective
      (λ ext →
         Split-surjective-cong (lower-extensionality? _ ℓ₁ lzero ext))
      ↠↔∃-Split-surjective
      (λ ext →
         Erased-Split-surjective↔Split-surjective
           (lower-extensionality? _ ℓ₁ lzero ext))

  Erased-↝↝↝ {k = bijection} =
    Erased-↝↝↝-lemma
      Has-quasi-inverse
      Has-quasi-inverse-cong
      Bijection.↔-as-Σ
      Erased-Has-quasi-inverse↔Has-quasi-inverse

  Erased-↝↝↝ {k = equivalence} =
    Erased-↝↝↝-lemma
      Is-equivalence
      Is-equivalence-cong
      Eq.≃-as-Σ
      Erased-Is-equivalence↔Is-equivalence

  Erased-↝↝↝ {k = equivalenceᴱ} =
    Erased-↝↝↝-lemma
      (λ f → Is-equivalenceᴱ f)
      (λ ext f≡g → EEq₂-⊔.Is-equivalenceᴱ-cong ext f≡g)
      (from-isomorphism EEq.≃ᴱ-as-Σ)
      EEq₂-⊔.Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ

  -- Erased preserves all kinds of functions.

  Erased-cong :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    @0 A ↝[ k ] B → Erased A ↝[ k ] Erased B
  Erased-cong {k = implication} =
    map
  Erased-cong {k = logical-equivalence} =
    Erased-cong-⇔
  Erased-cong {k = surjection} =
    Erased-cong.Erased-cong-↠ ax₁ ax₂
  Erased-cong {k = bijection} =
    Erased-cong.Erased-cong-↔ ax₁ ax₂
  Erased-cong {k = equivalence} =
    Erased-cong.Erased-cong-≃ ax₁ ax₂
  Erased-cong {k = equivalenceᴱ} =
    Erased-cong-≃ᴱ
  -- The clauses above are included in an attempt to optimise the
  -- code. Perhaps there is no need to include all of these extra
  -- clauses. However, if the clause for equivalenceᴱ is omitted, then
  -- (at the time of writing) some version of Agda type-checks
  -- Erased-cong-id and Erased-cong-∘ much more slowly.
  Erased-cong A↝B =
    Erased-↝↝↝ _ [ A↝B ]

  -- Dec-Erased preserves symmetric kinds of functions (in some cases
  -- assuming extensionality).

  Dec-Erased-cong :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} →
    @0 Extensionality? ⌊ k ⌋-sym (ℓ₁ ⊔ ℓ₂) lzero →
    @0 A ↝[ ⌊ k ⌋-sym ] B →
    Dec-Erased A ↝[ ⌊ k ⌋-sym ] Dec-Erased B
  Dec-Erased-cong ext A↝B =
    Erased-cong A↝B ⊎-cong Erased-cong (→-cong ext A↝B F.id)

------------------------------------------------------------------------
-- Results that depend on three instances of the axiomatisation of
-- []-cong, all for the same universe level

module []-cong₁₃
  (ax₁ : E₁.[]-cong-axiomatisation ℓ)
  (ax₂ : E₁.[]-cong-axiomatisation ℓ)
  (ax  : E₁.[]-cong-axiomatisation ℓ)
  where

  -- Note that []-cong₂-⊔, which contains Erased-cong, is instantiated
  -- with all of the module parameters.

  open []-cong₂-⊔ ax₁ ax₂ ax

  private
    module BC₁ = E₁.[]-cong₁ ax₁
    module BC₂ = E₁.[]-cong₁ ax₂

  ----------------------------------------------------------------------
  -- Erased-cong maps F.id to F.id for all kinds of functions
  -- (assuming function extensionality)

  private

    -- Lemmas used in the implementation of Erased-cong-id.

    Erased-cong-≃-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong Eq.id ≡ Eq.id {A = Erased A}
    Erased-cong-≃-id ext =
      Eq.lift-equality ext (apply-ext ext λ { [ _ ] → refl _ })

    Erased-cong-≃ᴱ-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong EEq.id ≡ EEq.id {A = Erased A}
    Erased-cong-≃ᴱ-id ext =
      EEq.[]-cong₂-⊔.to≡to→≡-Erased ax₁ ax₂ ax ext
        (apply-ext ext λ { [ _ ] → refl _ })

    Erased-cong-Embedding-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong F.id ≡ F.id {k = embedding} {A = Erased A}
    Erased-cong-Embedding-id ext =
      _↔_.to (Embedding-to-≡↔≡ ext) λ { [ _ ] → refl _ }

    Erased-cong-↠-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong S.id ≡ S.id {A = Erased A}
    Erased-cong-↠-id {A} ext =                          $⟨ lemma ⟩
      _↔_.to ↠↔∃-Split-surjective (Erased-cong F.id) ≡
      _↔_.to ↠↔∃-Split-surjective F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism ↠↔∃-Split-surjective) ⟩□

      Erased-cong F.id ≡ F.id                           □
      where
      lemma :
        (map id , _↠_.split-surjective (Erased-cong S.id)) ≡
        (id , λ x → x , refl x)
      lemma =
        Σ-≡,≡→≡
          (apply-ext ext λ _ → map-id)
          (apply-ext ext λ { [ x ] →

             subst (λ f → ∀ y → f ⁻¹ y)
               (apply-ext ext λ _ → map-id)
               (_↠_.split-surjective (Erased-cong S.id))
               [ x ]                                                     ≡⟨ sym $
                                                                            push-subst-application _ _ ⟩
             subst (_⁻¹ [ x ])
               (apply-ext ext λ _ → map-id)
               (_↠_.split-surjective (Erased-cong S.id) [ x ])           ≡⟨⟩

             subst (_⁻¹ [ x ])
               (apply-ext ext λ _ → map-id)
               ([ x ] , BC₂.[]-cong [ refl x ])                          ≡⟨ push-subst-pair-× _ _ ⟩

               [ x ]
             , subst (λ f → f [ x ] ≡ [ x ])
                 (apply-ext ext λ x → map-id {x = x})
                 (BC₂.[]-cong [ refl x ])                                ≡⟨ cong ([ x ] ,_) $
                                                                            subst-ext ext ⟩

             [ x ] , subst (_≡ [ x ]) (refl _) (BC₂.[]-cong [ refl x ])  ≡⟨ cong ([ x ] ,_) $
                                                                            trans (subst-refl _ _)
                                                                            BC₂.[]-cong-[refl] ⟩∎

             [ x ] , refl [ x ]                                          ∎ })

    Erased-cong-↔-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = bijection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↔-id ext =                          $⟨ lemma ⟩
      _↔_.to Bijection.↔-as-Σ (Erased-cong F.id) ≡
      _↔_.to Bijection.↔-as-Σ F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism Bijection.↔-as-Σ) ⟩□

      Erased-cong F.id ≡ F.id                       □
      where
      lemma :
        ( map id
        , map id
        , _↔_.right-inverse-of (Erased-cong F.id)
        , _↔_.left-inverse-of (Erased-cong F.id)
        ) ≡
        (id , id , refl , refl)
      lemma =
        Σ-≡,≡→≡ (apply-ext ext λ _ → map-id)
        (subst Has-quasi-inverse (apply-ext ext λ _ → map-id)
           ( map id
           , _↔_.right-inverse-of (Erased-cong F.id)
           , _↔_.left-inverse-of (Erased-cong F.id)
           )                                                              ≡⟨ push-subst-pair-× _ _ ⟩

         ( map id
         , subst
             (λ f → (∀ x → f (map id x) ≡ x) × (∀ x → map id (f x) ≡ x))
             (apply-ext ext λ x → map-id {x = x})
             ( _↔_.right-inverse-of (Erased-cong F.id)
             , _↔_.left-inverse-of (Erased-cong F.id)
             )
         )                                                                ≡⟨ cong (map id ,_) $
                                                                             push-subst-, _ _ ⟩
         ( map id
         , subst (λ f → ∀ x → f (map id x) ≡ x)
             (apply-ext ext λ x → map-id {x = x})
             (_↔_.right-inverse-of (Erased-cong F.id))
         , subst (λ f → ∀ x → map id (f x) ≡ x)
             (apply-ext ext λ x → map-id {x = x})
             (_↔_.left-inverse-of (Erased-cong F.id))
         )                                                                ≡⟨ Σ-≡,≡→≡ (apply-ext ext λ _ → map-id) (

           subst (λ f → (∀ x → f x ≡ x) × (∀ x → f x ≡ x))
             (apply-ext ext λ x → map-id {x = x})
             ( subst (λ f → ∀ x → f (map id x) ≡ x)
                 (apply-ext ext λ x → map-id {x = x})
                 (_↔_.right-inverse-of (Erased-cong F.id))
             , subst (λ f → ∀ x → map id (f x) ≡ x)
                 (apply-ext ext λ x → map-id {x = x})
                 (_↔_.left-inverse-of (Erased-cong F.id))
             )                                                                 ≡⟨ push-subst-, _ _ ⟩

             subst (λ f → ∀ x → f x ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (subst (λ f → ∀ x → f (map id x) ≡ x)
                  (apply-ext ext λ x → map-id {x = x})
                  (_↔_.right-inverse-of (Erased-cong F.id)))
           , subst (λ f → ∀ x → f x ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (subst (λ f → ∀ x → map id (f x) ≡ x)
                  (apply-ext ext λ x → map-id {x = x})
                  (_↔_.left-inverse-of (Erased-cong F.id)))                    ≡⟨ cong₂ _,_
                                                                                    (apply-ext ext lemma₁)
                                                                                    (apply-ext ext lemma₂) ⟩
           refl , refl                                                         ∎) ⟩

         (id , refl , refl)                                               ∎)
        where
        lemma₁ = λ { [ x ] →
          subst (λ f → ∀ x → f x ≡ x)
            (apply-ext ext λ x → map-id {x = x})
            (subst (λ f → ∀ x → f (map id x) ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (_↔_.right-inverse-of (Erased-cong F.id)))
            [ x ]                                                 ≡⟨ sym $
                                                                     push-subst-application _ _ ⟩
          subst (λ f → f [ x ] ≡ [ x ])
            (apply-ext ext λ x → map-id {x = x})
            (subst (λ f → ∀ x → f (map id x) ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (_↔_.right-inverse-of (Erased-cong F.id))
               [ x ])                                             ≡⟨ subst-ext ext ⟩

          subst (_≡ [ x ]) (refl [ x ])
            (subst (λ f → ∀ x → f (map id x) ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (_↔_.right-inverse-of (Erased-cong F.id))
               [ x ])                                             ≡⟨ subst-refl _ _ ⟩

          subst (λ f → ∀ x → f (map id x) ≡ x)
            (apply-ext ext λ x → map-id {x = x})
            (_↔_.right-inverse-of (Erased-cong F.id))
            [ x ]                                                 ≡⟨ sym $
                                                                     push-subst-application _ _ ⟩
          subst (λ f → f [ x ] ≡ [ x ])
            (apply-ext ext λ x → map-id {x = x})
            (BC₂.[]-cong [ refl x ])                              ≡⟨ subst-ext ext ⟩

          subst (_≡ [ x ]) (refl [ x ]) (BC₂.[]-cong [ refl x ])  ≡⟨ subst-refl _ _ ⟩

          BC₂.[]-cong [ refl x ]                                  ≡⟨ BC₂.[]-cong-[refl] ⟩∎

          refl [ x ]                                              ∎ }

        lemma₂ = λ { [ x ] →
          subst (λ f → ∀ x → f x ≡ x)
            (apply-ext ext λ x → map-id {x = x})
            (subst (λ f → ∀ x → map id (f x) ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (_↔_.left-inverse-of (Erased-cong F.id)))
            [ x ]                                         ≡⟨ sym $
                                                             push-subst-application _ _ ⟩
          subst (λ f → f [ x ] ≡ [ x ])
            (apply-ext ext λ x → map-id {x = x})
            (subst (λ f → ∀ x → map id (f x) ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (_↔_.left-inverse-of (Erased-cong F.id))
               [ x ])                                     ≡⟨ subst-ext ext ⟩

          subst (_≡ [ x ]) (refl [ x ])
            (subst (λ f → ∀ x → map id (f x) ≡ x)
               (apply-ext ext λ x → map-id {x = x})
               (_↔_.left-inverse-of (Erased-cong F.id))
               [ x ])                                     ≡⟨ subst-refl _ _ ⟩

          subst (λ f → ∀ x → map id (f x) ≡ x)
            (apply-ext ext λ x → map-id {x = x})
            (_↔_.left-inverse-of (Erased-cong F.id))
            [ x ]                                         ≡⟨ sym $
                                                             push-subst-application _ _ ⟩
          subst (λ f → map id (f [ x ]) ≡ [ x ])
            (apply-ext ext λ x → map-id {x = x})
            (BC₁.[]-cong [ refl x ])                      ≡⟨ subst-ext ext ⟩

          subst (λ y → map id y ≡ [ x ]) (refl [ x ])
            (BC₁.[]-cong [ refl x ])                      ≡⟨ subst-refl _ _ ⟩

          BC₁.[]-cong [ refl x ]                          ≡⟨ BC₁.[]-cong-[refl] ⟩∎

          refl [ x ]                                      ∎ }

    Erased-cong-↣-id :
      {@0 A : Type ℓ} →
      Extensionality ℓ ℓ →
      Erased-cong {k = injection} F.id ≡ F.id {A = Erased A}
    Erased-cong-↣-id ext =                       $⟨ lemma ⟩
      _↔_.to ↣↔∃-Injective (Erased-cong F.id) ≡
      _↔_.to ↣↔∃-Injective F.id                  ↝⟨ Eq.≃-≡ (from-isomorphism ↣↔∃-Injective) ⟩□

      Erased-cong F.id ≡ F.id                    □
      where
      lemma :
        ( map id
        , λ {_ _} → _↣_.injective (Erased-cong F.id)
        ) ≡
        (id , λ {_ _} → _↣_.injective F.id)
      lemma =
        Σ-≡,≡→≡
          (apply-ext ext λ _ → map-id)
          (implicit-extensionality ext λ { [ x ] →
           implicit-extensionality ext λ { [ y ] →
           apply-ext ext λ eq →

             subst (λ f → ∀ {x y} → f x ≡ f y → x ≡ y)
               (apply-ext ext λ _ → map-id)
               (_↣_.injective (Erased-cong F.id))
               {x = [ x ]} {y = [ y ]} eq                             ≡⟨ cong (λ f → f _) $ sym $
                                                                         push-subst-implicit-application
                                                                           _ (λ f x → ∀ {y} → f x ≡ f y → x ≡ y) ⟩
             subst (λ f → ∀ {y} → f [ x ] ≡ f y → [ x ] ≡ y)
               (apply-ext ext λ _ → map-id)
               (_↣_.injective (Erased-cong F.id) {x = [ x ]})
               {y = [ y ]} eq                                         ≡⟨ cong (λ f → f _) $ sym $
                                                                         push-subst-implicit-application
                                                                           _ (λ f y → f [ x ] ≡ f y → [ x ] ≡ y) ⟩
             subst (λ f → f [ x ] ≡ f [ y ] → [ x ] ≡ [ y ])
               (apply-ext ext λ _ → map-id)
               (_↣_.injective (Erased-cong F.id)
                  {x = [ x ]} {y = [ y ]})
               eq                                                     ≡⟨ subst-∀ ⟩

             subst (λ _ → [ x ] ≡ [ y ])
               (sym $
                Σ-≡,≡→≡ (sym (apply-ext ext λ _ → map-id)) (refl _))
               (_↣_.injective (Erased-cong F.id)
                  (subst (λ f → f [ x ] ≡ f [ y ])
                     (sym (apply-ext ext λ x → map-id {x = x})) eq))  ≡⟨ subst-const _ ⟩

             _↣_.injective (Erased-cong F.id)
               (subst (λ f → f [ x ] ≡ f [ y ])
                  (sym (apply-ext ext λ x → map-id {x = x})) eq)      ≡⟨ cong (_↣_.injective (Erased-cong F.id))
                                                                         subst-in-terms-of-trans-and-cong ⟩
             _↣_.injective (Erased-cong F.id)
               (trans
                  (sym $ cong (_$ [ x ]) $ sym $
                   apply-ext ext λ x → map-id {x = x}) $
                trans eq $ cong (_$ [ y ]) $ sym $
                apply-ext ext λ x → map-id {x = x})                   ≡⟨ cong (_↣_.injective (Erased-cong F.id)) $ cong₂ trans
                                                                           (trans (cong sym $ cong-sym _ _) $
                                                                            sym-sym _)
                                                                           (cong (trans _) $ cong-sym _ _) ⟩
             _↣_.injective (Erased-cong F.id)
               (trans
                  (cong (_$ [ x ]) $
                   apply-ext ext λ x → map-id {x = x}) $
                trans eq $ sym $ cong (_$ [ y ]) $
                apply-ext ext λ x → map-id {x = x})                   ≡⟨ cong (_↣_.injective (Erased-cong F.id)) $ cong₂ trans
                                                                           (cong-ext ext)
                                                                           (cong (trans _ ∘ sym) $ cong-ext ext) ⟩
             _↣_.injective (Erased-cong F.id)
               (trans (refl _) (trans eq $ sym $ refl _))             ≡⟨ cong (_↣_.injective (Erased-cong F.id)) $
                                                                         trans (trans-reflˡ _) $
                                                                         trans (cong (trans _) sym-refl) $
                                                                         trans-reflʳ _ ⟩
             _↣_.injective (Erased-cong F.id) eq                      ≡⟨⟩

             BC₁.[]-cong (BC₂.[]-cong⁻¹ eq)                           ≡⟨ []-cong-unique ax₁ ax₂ ⟩

             BC₂.[]-cong (BC₂.[]-cong⁻¹ eq)                           ≡⟨ _↔_.right-inverse-of BC₂.Erased-≡↔[]≡[] _ ⟩∎

             eq                                                       ∎ }})

  -- Erased-cong maps F.id to F.id for all kinds of functions
  -- (assuming function extensionality).

  Erased-cong-id :
    {@0 A : Type ℓ} →
    Extensionality ℓ ℓ →
    Erased-cong F.id ≡ F.id {k = k} {A = Erased A}
  Erased-cong-id {k = implication}         = λ ext → apply-ext ext λ _ →
                                               map-id
  Erased-cong-id {k = logical-equivalence} = Erased-cong-⇔-id
  Erased-cong-id {k = injection}           = Erased-cong-↣-id
  Erased-cong-id {k = embedding}           = Erased-cong-Embedding-id
  Erased-cong-id {k = surjection}          = Erased-cong-↠-id
  Erased-cong-id {k = bijection}           = Erased-cong-↔-id
  Erased-cong-id {k = equivalence}         = Erased-cong-≃-id
  Erased-cong-id {k = equivalenceᴱ}        = Erased-cong-≃ᴱ-id

------------------------------------------------------------------------
-- Results that depend on instances of the axiomatisation of []-cong
-- for three universe levels, as well as for the maximum of each pair
-- drawn from these three levels

module []-cong₃-⊔
  (ax₁  : []-cong-axiomatisation ℓ₁)
  (ax₂  : []-cong-axiomatisation ℓ₂)
  (ax₃  : []-cong-axiomatisation ℓ₃)
  (ax₁₂ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
  (ax₁₃ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₃))
  (ax₂₃ : []-cong-axiomatisation (ℓ₂ ⊔ ℓ₃))
  where

  private
    module EC₁ = []-cong₂-⊔ ax₁ ax₃ ax₁₃
    module EC₂ = []-cong₂-⊔ ax₂ ax₃ ax₂₃
    module EC₃ = []-cong₂-⊔ ax₁ ax₂ ax₁₂

  ----------------------------------------------------------------------
  -- Erased-cong commutes with F._∘_ for all kinds of functions
  -- (assuming function extensionality)

  private

    -- Lemmas used in the implementation of Erased-cong-∘.

    Erased-cong-≃-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ≃ C) (@0 g : A ≃ B) →
      EC₁.Erased-cong (f Eq.∘ g) ≡
      EC₂.Erased-cong f Eq.∘ EC₃.Erased-cong g
    Erased-cong-≃-∘ ext _ _ = Eq.lift-equality ext (refl _)

    Erased-cong-≃ᴱ-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ≃ᴱ C) (@0 g : A ≃ᴱ B) →
      EC₁.Erased-cong (f EEq.∘ g) ≡
      EC₂.Erased-cong f EEq.∘ EC₃.Erased-cong g
    Erased-cong-≃ᴱ-∘ ext _ _ =
      EEq.[]-cong₂-⊔.to≡to→≡-Erased ax₁ ax₃ ax₁₃ ext (refl _)

    Erased-cong-Embedding-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : Embedding B C) (@0 g : Embedding A B) →
      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-Embedding-∘ ext _ _ =
      _↔_.to (Embedding-to-≡↔≡ ext) λ _ → refl _

    right-inverse-of-cong-∘ :
      ∀ {ℓ₁ ℓ₂ ℓ₃}
      (ax₁  : []-cong-axiomatisation ℓ₁)
      (ax₂  : []-cong-axiomatisation ℓ₂)
      (ax₃  : []-cong-axiomatisation ℓ₃)
      (ax₁₂ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₂))
      (ax₁₃ : []-cong-axiomatisation (ℓ₁ ⊔ ℓ₃))
      (ax₂₃ : []-cong-axiomatisation (ℓ₂ ⊔ ℓ₃)) →
      let module EC₁′ = []-cong₂-⊔ ax₁ ax₃ ax₁₃
          module EC₂′ = []-cong₂-⊔ ax₂ ax₃ ax₂₃
          module EC₃′ = []-cong₂-⊔ ax₁ ax₂ ax₁₂
      in
      ∀ {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} {x} →
      (@0 f : B ↠ C) (@0 g : A ↠ B) →
      _↠_.right-inverse-of (EC₁′.Erased-cong (f F.∘ g)) x ≡
      _↠_.right-inverse-of (EC₂′.Erased-cong f F.∘ EC₃′.Erased-cong g) x
    right-inverse-of-cong-∘ ax₁ ax₂ ax₃ _ _ _ {x = [ x ]} f g =
      BC₃.[]-cong
        [ trans (cong (_↠_.to f)
                   (_↠_.right-inverse-of g (_↠_.from f x)))
            (_↠_.right-inverse-of f x)
        ]                                                           ≡⟨ E₁.[]-cong₁.[]-cong-trans ax₃ ⟩

      (trans
         (BC₃.[]-cong
            [ cong (_↠_.to f)
                (_↠_.right-inverse-of g (_↠_.from f x)) ]) $
       BC₃.[]-cong [ _↠_.right-inverse-of f x ])                    ≡⟨ cong (λ p → trans p _) (E₁.[]-cong₂.[]-cong-cong ax₂ ax₃) ⟩∎

      (trans
         (cong (map (_↠_.to f)) $
          BC₂.[]-cong [ _↠_.right-inverse-of g (_↠_.from f x) ]) $
       BC₃.[]-cong [ _↠_.right-inverse-of f x ])                    ∎
      where
      module BC₂ = E₁.[]-cong₁ ax₂
      module BC₃ = E₁.[]-cong₁ ax₃

    Erased-cong-↠-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality ℓ₃ (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ↠ C) (@0 g : A ↠ B) →
      EC₁.Erased-cong (f S.∘ g) ≡
      EC₂.Erased-cong f S.∘ EC₃.Erased-cong g
    Erased-cong-↠-∘ ext f g =                                    $⟨ lemma ⟩
      _↔_.to ↠↔∃-Split-surjective (EC₁.Erased-cong (f F.∘ g)) ≡
      _↔_.to ↠↔∃-Split-surjective
        (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)                ↝⟨ Eq.≃-≡ (from-isomorphism ↠↔∃-Split-surjective) ⟩□

      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g                    □
      where
      lemma :
        ( map (_↠_.to f ∘ _↠_.to g)
        , (λ x →
               [ _↠_.from g (_↠_.from f (erased x)) ]
             , _↠_.right-inverse-of (EC₁.Erased-cong (f F.∘ g)) x)
        )
        ≡
        ( (λ x → [ _↠_.to f (_↠_.to g (erased x)) ])
        , (λ x →
               [ _↠_.from g (_↠_.from f (erased x)) ]
             , _↠_.right-inverse-of
                 (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g) x)
        )
      lemma =
        cong (_ ,_) $ apply-ext ext λ ([ x ]) →
          cong ([ _↠_.from g (_↠_.from f x) ] ,_)
            (right-inverse-of-cong-∘ ax₁ ax₂ ax₃ ax₁₂ ax₁₃ ax₂₃ f g)

    Erased-cong-↔-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ↔ C) (@0 g : A ↔ B) →
      EC₁.Erased-cong {k = bijection} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-↔-∘ ext f g =                                            $⟨ lemma ⟩
      _↔_.to Bijection.↔-as-Σ (EC₁.Erased-cong (f F.∘ g)) ≡
      _↔_.to Bijection.↔-as-Σ (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)  ↝⟨ Eq.≃-≡ (from-isomorphism Bijection.↔-as-Σ) ⟩□

      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g                            □
      where
      lemma :
        ( map (_↔_.to f ∘ _↔_.to g)
        , map (_↔_.from g ∘ _↔_.from f)
        , _↔_.right-inverse-of (EC₁.Erased-cong (f F.∘ g))
        , _↔_.left-inverse-of (EC₁.Erased-cong (f F.∘ g))
        )
        ≡
        ( (λ x → [ _↔_.to f (_↔_.to g (erased x)) ])
        , (λ x → [ _↔_.from g (_↔_.from f (erased x)) ])
        , _↔_.right-inverse-of (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)
        , _↔_.left-inverse-of (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)
        )
      lemma =
        cong (λ p → map (_↔_.to f ∘ _↔_.to g)
                  , map (_↔_.from g ∘ _↔_.from f) , p) $
        cong₂ _,_
          (apply-ext (lower-extensionality ℓ₁ ℓ₁ ext) λ { [ _ ] →
             right-inverse-of-cong-∘ ax₁ ax₂ ax₃ ax₁₂ ax₁₃ ax₂₃
               (_↔_.surjection f) (_↔_.surjection g) })
          (apply-ext (lower-extensionality ℓ₃ ℓ₃ ext) λ { [ _ ] →
           right-inverse-of-cong-∘ ax₃ ax₂ ax₁ ax₂₃ ax₁₃ ax₁₂
              (_↔_.surjection $ inverse g)
              (_↔_.surjection $ inverse f) })

    Erased-cong-↣-∘ :
      {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
      Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
      (@0 f : B ↣ C) (@0 g : A ↣ B) →
      EC₁.Erased-cong {k = injection} (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
    Erased-cong-↣-∘ ext f g =                                         $⟨ lemma ⟩
      _↔_.to ↣↔∃-Injective (EC₁.Erased-cong (f F.∘ g)) ≡
      _↔_.to ↣↔∃-Injective (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)  ↝⟨ Eq.≃-≡ (from-isomorphism ↣↔∃-Injective) ⟩□

      EC₁.Erased-cong (f F.∘ g) ≡
      EC₂.Erased-cong f F.∘ EC₃.Erased-cong g                         □
      where
      module BC₁ = E₁.[]-cong₁ ax₁
      module BC₂ = E₁.[]-cong₁ ax₂
      module BC₃ = E₁.[]-cong₁ ax₃

      lemma :
        ( map (_↣_.to f ∘ _↣_.to g)
        , λ {_ _} → _↣_.injective (EC₁.Erased-cong (f F.∘ g))
        )
        ≡
        ( (λ x → [ _↣_.to f (_↣_.to g (erased x)) ])
        , λ {_ _} →
            _↣_.injective (EC₂.Erased-cong f F.∘ EC₃.Erased-cong g)
        )
      lemma =
        cong (_ ,_) $
        implicit-extensionality
          (lower-extensionality ℓ₃ lzero ext) λ { [ _ ] →
        implicit-extensionality
          (lower-extensionality ℓ₃ lzero ext) λ { [ _ ] →
        apply-ext (lower-extensionality ℓ₁ ℓ₃ ext) λ eq →
          let eq′ = [ _↣_.injective f (erased (BC₃.[]-cong⁻¹ eq)) ]
          in
          BC₁.[]-cong [ _↣_.injective g (erased eq′) ]                  ≡⟨ cong BC₁.[]-cong $
                                                                           BC₁.[]-cong [ cong (_↣_.injective g ∘ erased) $ sym $
                                                                                         _↔_.left-inverse-of BC₂.Erased-≡↔[]≡[] _ ] ⟩∎
          BC₁.[]-cong [ _↣_.injective g
                          (erased (BC₂.[]-cong⁻¹ (BC₂.[]-cong eq′))) ]  ∎ }}

  -- Erased-cong commutes with F._∘_ for all kinds of functions
  -- (assuming function extensionality).

  Erased-cong-∘ :
    {@0 A : Type ℓ₁} {@0 B : Type ℓ₂} {@0 C : Type ℓ₃} →
    Extensionality (ℓ₁ ⊔ ℓ₃) (ℓ₁ ⊔ ℓ₃) →
    (@0 f : B ↝[ k ] C) (@0 g : A  ↝[ k ] B) →
    EC₁.Erased-cong (f F.∘ g) ≡ EC₂.Erased-cong f F.∘ EC₃.Erased-cong g
  Erased-cong-∘ {k = implication}         = λ _ f → map-∘ f
  Erased-cong-∘ {k = logical-equivalence} = λ _ → Erased-cong-⇔-∘
  Erased-cong-∘ {k = injection}           = Erased-cong-↣-∘
  Erased-cong-∘ {k = embedding}           = λ ext f g →
                                              Erased-cong-Embedding-∘
                                                ext f g
  Erased-cong-∘ {k = surjection}          = λ ext →
                                              Erased-cong-↠-∘
                                                (lower-extensionality ℓ₁ lzero ext)
  Erased-cong-∘ {k = bijection}           = Erased-cong-↔-∘
  Erased-cong-∘ {k = equivalence}         = Erased-cong-≃-∘
  Erased-cong-∘ {k = equivalenceᴱ}        = Erased-cong-≃ᴱ-∘

------------------------------------------------------------------------
-- Results that depend on instances of the axiomatisation of []-cong
-- for all universe levels

module []-cong (ax : ∀ {ℓ} → []-cong-axiomatisation ℓ) where

  private
    open module BC₂ {ℓ₁ ℓ₂} = []-cong₂-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) ax
      public
    open module BC₁₃ {ℓ} = []-cong₁₃ (ax {ℓ = ℓ}) ax ax
      public
    open module BC₃ {ℓ₁ ℓ₂ ℓ₃} =
      []-cong₃-⊔ (ax {ℓ = ℓ₁}) (ax {ℓ = ℓ₂}) (ax {ℓ = ℓ₃}) ax ax ax
      public
