------------------------------------------------------------------------
-- Some results that hold for modalities that commute with Erased
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality
import Modality.Basics

module Modality.Commutes-with-Erased
  {c⁺}
  (eq-J : ∀ {a p} → Equality-with-J a p c⁺)
  (open Modality.Basics eq-J)
  {a}
  (M : Modality a)
  (commutes-with-Erased : Modality.Commutes-with-Erased M)
  where

open Derived-definitions-and-properties eq-J
open Modality M
  hiding (Stable-Π; Stable-Erased; Stable-Contractibleᴱ; Stable-⁻¹ᴱ)

open import Logical-equivalence using (_⇔_)
import Modality.Box-cong
open import Prelude

open import Equivalence eq-J as Eq using (_≃_)
open import Equivalence.Erased eq-J as EEq using (_≃ᴱ_; Is-equivalenceᴱ)
open import Equivalence.Erased.Contractible-preimages eq-J as ECP
  using (Contractibleᴱ; _⁻¹ᴱ_)
import Equivalence.Half-adjoint eq-J as HA
open import Erased.Level-1 eq-J as E
  using (Erased; []-cong-axiomatisation)
import Erased.Level-2 eq-J as E₂
open import Extensionality eq-J
open import Function-universe eq-J as F hiding (_∘_)
open import H-level eq-J
import Modality.Has-choice eq-J M as C

private
  variable
    ℓ   : Level
    A B : Type ℓ
    f k : A

------------------------------------------------------------------------
-- ◯ commutes with Erased

-- ◯ (Erased A) is equivalent to Erased (◯ A).

◯-Erased≃Erased-◯ : ◯ (Erased A) ≃ Erased (◯ A)
◯-Erased≃Erased-◯ = Eq.⟨ _ , commutes-with-Erased ⟩

------------------------------------------------------------------------
-- Some results that hold if the []-cong axioms can be instantiated

module []-cong (ax : []-cong-axiomatisation a) where

  private
    open module MBC = Modality.Box-cong eq-J ax M
      hiding (Modal→Stable-Is-equivalenceᴱ; ◯-cong-◯)

  private
    module EC = E₂.[]-cong₂-⊔ ax ax ax
    module BC = ECP.[]-cong₂ ax ax

  ----------------------------------------------------------------------
  -- Some results related to stability

  -- If A is k-stable, then Erased A is k-stable.

  Stable-Erased : @0 Stable-[ k ] A → Stable-[ k ] (Erased A)
  Stable-Erased {A = A} s =
    ◯ (Erased A)  ↔⟨ ◯-Erased≃Erased-◯ ⟩
    Erased (◯ A)  ↝⟨ EC.Erased-cong s ⟩□
    Erased A      □

  -- If f has type A → B, A is modal, and equality is k-stable for B,
  -- then f ⁻¹ᴱ y is k-stable.

  Stable-⁻¹ᴱ :
    {A B : Type a} {f : A → B} {y : B} →
    Modal A →
    @0 For-iterated-equality 1 Stable-[ k ] B →
    Stable-[ k ] (f ⁻¹ᴱ y)
  Stable-⁻¹ᴱ m s =
    Stable-Σ m λ _ →
    Stable-Erased (s _ _)

  ----------------------------------------------------------------------
  -- An equivalence

  -- If the modality is left exact, then ◯ (f ⁻¹ᴱ y) is equivalent to
  -- ◯ (η ∘ f ⁻¹ᴱ η y).

  ◯⁻¹ᴱ≃◯∘⁻¹ᴱ :
    {A : Type a} {f : A → B} {y : B} →
    @0 Left-exact-η-cong →
    ◯ (f ⁻¹ᴱ y) ≃ ◯ (η ∘ f ⁻¹ᴱ η y)
  ◯⁻¹ᴱ≃◯∘⁻¹ᴱ {A = A} {f = f} {y = y} lex =
    ◯ (∃ λ (x : A) → Erased (f x ≡ y))        ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
    ◯ (∃ λ (x : A) → ◯ (Erased (f x ≡ y)))    ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩
    ◯ (∃ λ (x : A) → Erased (◯ (f x ≡ y)))    ↔⟨ (◯-cong-≃ $ ∃-cong (λ _ → EC.Erased-cong (◯≡≃η≡η lex))) ⟩□
    ◯ (∃ λ (x : A) → Erased (η (f x) ≡ η y))  □

  ----------------------------------------------------------------------
  -- Some results that hold if the modality has choice in erased
  -- contexts

  module Has-erased-choice (@0 has-choice : Has-choice) where

    -- If A is modal, then Contractibleᴱ A is k-stable (perhaps
    -- assuming function extensionality).

    Stable-Contractibleᴱ :
      @0 Extensionality? k a a →
      Modal A →
      Stable-[ k ] (Contractibleᴱ A)
    Stable-Contractibleᴱ ext m =
      Stable-Σ m λ _ →
      Stable-Erased (
      C.Stable-Π has-choice ext λ _ →
      Modal→Stable (Modal→Separated m _ _))

    mutual

      -- If the modality is left exact, then ◯ commutes with
      -- Contractibleᴱ (assuming function extensionality).

      ◯-Contractibleᴱ≃Contractibleᴱ-◯ :
        @0 Left-exact-η-cong →
        ◯ (Contractibleᴱ A) ↝[ a ∣ a ] Contractibleᴱ (◯ A)
      ◯-Contractibleᴱ≃Contractibleᴱ-◯ lex ext =
        ◯-Contractibleᴱ≃Contractibleᴱ-◯′ ext lex (◯Ση≃Σ◯◯ ext)

      -- A generalisation of ◯-Contractibleᴱ≃Contractibleᴱ-◯.

      ◯-Contractibleᴱ≃Contractibleᴱ-◯′ :
        @0 Extensionality? k a a →
        @0 Left-exact-η-cong →
        ({A : Type a} {P : ◯ A → Type a} →
         ◯ (Σ A (P ∘ η)) ↝[ k ] Σ (◯ A) (◯ ∘ P)) →
        ◯ (Contractibleᴱ A) ↝[ k ] Contractibleᴱ (◯ A)
      ◯-Contractibleᴱ≃Contractibleᴱ-◯′ {A = A} ext lex comm =
        ◯ (Contractibleᴱ A)                               ↔⟨⟩
        ◯ (∃ λ (x : A) → Erased ((y : A) → x ≡ y))        ↔⟨ inverse ◯Σ◯≃◯Σ ⟩
        ◯ (∃ λ (x : A) → ◯ (Erased ((y : A) → x ≡ y)))    ↔⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩
        ◯ (∃ λ (x : A) → Erased (◯ ((y : A) → x ≡ y)))    ↝⟨ (◯-cong-↝ᴱ ext λ ext → ∃-cong λ _ → EC.Erased-cong (
                                                              inverse-ext? (C.Π◯≃◯Π has-choice) ext)) ⟩
        ◯ (∃ λ (x : A) → Erased ((y : A) → ◯ (x ≡ y)))    ↝⟨ (◯-cong-↝ᴱ ext λ ext → ∃-cong λ _ →
                                                              EC.Erased-cong (∀-cong ext λ _ → from-equivalence $
                                                              ◯≡≃η≡η lex)) ⟩
        ◯ (∃ λ (x : A) → Erased ((y : A) → η x ≡ η y))    ↝⟨ comm ⟩
        (∃ λ (x : ◯ A) → ◯ (Erased ((y : A) → x ≡ η y)))  ↔⟨ (∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩
        (∃ λ (x : ◯ A) → Erased (◯ ((y : A) → x ≡ η y)))  ↝⟨ (∃-cong λ _ → EC.Erased-cong (inverse-ext? (C.Π◯≃◯Π has-choice) ext)) ⟩
        (∃ λ (x : ◯ A) → Erased ((y : A) → ◯ (x ≡ η y)))  ↝⟨ (∃-cong λ _ → EC.Erased-cong (inverse-ext? Π◯◯≃Π◯η ext)) ⟩
        (∃ λ (x : ◯ A) → Erased ((y : ◯ A) → ◯ (x ≡ y)))  ↝⟨ (∃-cong λ _ → EC.Erased-cong (∀-cong ext λ _ → from-equivalence $ inverse $
                                                              Modal→≃◯ (Separated-◯ _ _))) ⟩
        (∃ λ (x : ◯ A) → Erased ((y : ◯ A) → x ≡ y))      ↔⟨⟩
        Contractibleᴱ (◯ A)                               □

  ----------------------------------------------------------------------
  -- Some results that hold if the modality has choice

  module Has-choice (has-choice : Has-choice) where

    open Has-erased-choice has-choice public
    open C has-choice hiding (module Left-exact)
    open C.Left-exact has-choice

    --------------------------------------------------------------------
    -- More results related to stability

    -- If f has type A → B, where A is modal and B is separated, then
    -- ECP.Is-equivalenceᴱ f is k-stable (perhaps assuming function
    -- extensionality).

    Modal→Stable-Is-equivalenceᴱ-CP :
      {@0 f : A → B} →
      Extensionality? k a a →
      Modal A → @0 Separated B →
      Stable-[ k ] (ECP.Is-equivalenceᴱ f)
    Modal→Stable-Is-equivalenceᴱ-CP {f = f} ext m s =
      Stable-Π ext λ y →
      let m′ : Modal (f ⁻¹ᴱ y)
          m′ = Modal-⁻¹ᴱ m s in
      Stable-Σ m′ λ _ →
      Stable-Erased (
      Stable-Π ext λ _ →
      Modal→Stable (Modal→Separated m′ _ _))

    -- If f has type A → B, where A is modal and B is separated, then
    -- Is-equivalenceᴱ f is k-stable (perhaps assuming function
    -- extensionality).

    Modal→Stable-Is-equivalenceᴱ :
      {@0 f : A → B} →
      Extensionality? k a a →
      Modal A → @0 Separated B →
      Stable-[ k ] (Is-equivalenceᴱ f)
    Modal→Stable-Is-equivalenceᴱ {k = k} {f = f} ext m s =
      generalise-ext?′
        (Stable→Stable-⇔ $ MBC.Modal→Stable-Is-equivalenceᴱ m s)
        (λ ext → Modal→Stable $ Modal-Is-equivalenceᴱ ext m s)
        Modal→Stable-≃ᴱ-Is-equivalenceᴱ
        ext
      where
      Modal→Stable-≃ᴱ-Is-equivalenceᴱ :
        @0 Extensionality a a →
        Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)
      Modal→Stable-≃ᴱ-Is-equivalenceᴱ ext =
                                                                 $⟨ s′ ⟩
        Stable-[ equivalenceᴱ ] (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  →⟨ Stable-respects-↝-sym $ inverse $
                                                                    EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext ⟩□
        Stable-[ equivalenceᴱ ] (Is-equivalenceᴱ f)              □
        where
        ext′ = E.[ ext ]

        s′ =
          Stable-Π ext′ λ y →
          let m′ : Modal (f ⁻¹ᴱ y)
              m′ = Modal-⁻¹ᴱ m s in
          Stable-Σ m′ λ _ →
          Stable-Erased (
          Stable-Π ext′ λ _ →
          Modal→Stable (Modal→Separated m′ _ _))

    --------------------------------------------------------------------
    -- Some results that hold if the modality is left exact in erased
    -- contexts (in addition to having choice)

    module Left-exact (@0 lex : Left-exact-η-cong) where

      -- A function f is ◯-connected with erased proofs if and only if
      -- ◯ (ECP.Is-equivalenceᴱ f) holds.

      Connected-→ᴱ≃◯-Is-equivalenceᴱ-CP :
        ◯ -Connected-→ᴱ f ↝[ a ∣ a ] ◯ (ECP.Is-equivalenceᴱ f)
      Connected-→ᴱ≃◯-Is-equivalenceᴱ-CP {f = f} ext =
        ◯ -Connected-→ᴱ f                    ↔⟨⟩
        (∀ y → Contractibleᴱ (◯ (f ⁻¹ᴱ y)))  ↝⟨ (∀-cong ext λ _ → inverse-ext? (◯-Contractibleᴱ≃Contractibleᴱ-◯ lex) ext) ⟩
        (∀ y → ◯ (Contractibleᴱ (f ⁻¹ᴱ y)))  ↝⟨ Π◯≃◯Π ext ⟩
        ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))    ↔⟨⟩
        ◯ (ECP.Is-equivalenceᴱ f)            □

      ------------------------------------------------------------------
      -- Some results that hold if the modality commutes with Σ (in
      -- addition to having choice, and being left exact in erased
      -- contexts)

      module Commutes-with-Σ (commutes-with-Σ : Commutes-with-Σ) where

        -- ◯ (ECP.Is-equivalenceᴱ f) is equivalent to
        -- ECP.Is-equivalenceᴱ (◯-map f) (assuming function
        -- extensionality).

        ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP :
          ◯ (ECP.Is-equivalenceᴱ f) ↝[ a ∣ a ]
          ECP.Is-equivalenceᴱ (◯-map f)
        ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP {f = f} ext =
          ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))          ↝⟨ inverse-ext? Connected-→ᴱ≃◯-Is-equivalenceᴱ-CP ext ⟩
          (∀ y → Contractibleᴱ (◯ (f ⁻¹ᴱ y)))        ↝⟨ (∀-cong ext λ _ → BC.Contractibleᴱ-cong ext $ ◯⁻¹ᴱ≃◯∘⁻¹ᴱ lex) ⟩
          (∀ y → Contractibleᴱ (◯ (η ∘ f ⁻¹ᴱ η y)))  ↝⟨ (∀-cong ext λ _ → BC.Contractibleᴱ-cong ext $ ◯∘⁻¹ᴱ≃◯-map-⁻¹ᴱ commutes-with-Σ) ⟩
          (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ η y))    ↝⟨ inverse-ext?
                                                          (Π◯↝Πη λ ext _ → Stable-Contractibleᴱ ext $ Modal-⁻¹ᴱ Modal-◯ Separated-◯)
                                                          ext ⟩□
          (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))      □

        private

          -- ◯ (Is-equivalenceᴱ f) is logically equivalent to
          -- Is-equivalenceᴱ (◯-map f).

          ◯-Is-equivalenceᴱ⇔Is-equivalenceᴱ :
            ◯ (Is-equivalenceᴱ f) ⇔ Is-equivalenceᴱ (◯-map f)
          ◯-Is-equivalenceᴱ⇔Is-equivalenceᴱ {f = f} =
            ◯ (Is-equivalenceᴱ f)                  ↝⟨ ◯-cong-⇔ EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩
            ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))      ↝⟨ ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP _ ⟩
            (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))  ↝⟨ inverse $ EEq.Is-equivalenceᴱ⇔Is-equivalenceᴱ-CP ⟩□
            Is-equivalenceᴱ (◯-map f)              □

          -- ◯ (Is-equivalenceᴱ f) is equivalent (with erased proofs)
          -- to Is-equivalenceᴱ (◯-map f) (assuming function
          -- extensionality).

          ◯-Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ :
            @0 Extensionality a a →
            ◯ (Is-equivalenceᴱ f) ≃ᴱ Is-equivalenceᴱ (◯-map f)
          ◯-Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ {f = f} ext =
            ◯ (Is-equivalenceᴱ f)                  ↝⟨ ◯-cong-≃ᴱ (EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext) ⟩
            ◯ (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))      ↝⟨ ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP E.[ ext ] ⟩
            (∀ y → Contractibleᴱ (◯-map f ⁻¹ᴱ y))  ↝⟨ inverse $ EEq.Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ-CP ext ⟩□
            Is-equivalenceᴱ (◯-map f)              □

          -- ◯ (Is-equivalenceᴱ f) is equivalent to
          -- Is-equivalenceᴱ (◯-map f) (assuming function
          -- extensionality).

          ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ′ :
            {f : A → B} →
            Extensionality a a →
            ◯ (Is-equivalenceᴱ f) ≃ Is-equivalenceᴱ (◯-map f)
          ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ′
            {A = A} {B = B} {f = f} ext =

            ◯ (Is-equivalenceᴱ f)                                       ↔⟨⟩

            ◯ (∃ λ (f⁻¹ : B → A) → Erased (HA.Proofs f f⁻¹))            ↝⟨ inverse ◯Σ◯≃◯Σ ⟩

            ◯ (∃ λ (f⁻¹ : B → A) → ◯ (Erased (HA.Proofs f f⁻¹)))        ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ◯-Erased≃Erased-◯) ⟩

            ◯ (∃ λ (f⁻¹ : B → A) → Erased (◯ (HA.Proofs f f⁻¹)))        ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → EC.Erased-cong (
                                                                            ◯-Half-adjoint-proofs≃Half-adjoint-proofs-◯-map-◯-map
                                                                              lex ext)) ⟩

            ◯ (∃ λ (f⁻¹ : B → A) →
                 Erased (HA.Proofs (◯-map f) (◯-map f⁻¹)))              ↝⟨ (◯-cong-≃ $ ∃-cong λ _ → ≡⇒↝ _ $
                                                                            cong (λ g → Erased (HA.Proofs (◯-map f) g)) $ sym $
                                                                            apply-ext ext λ _ → ◯-map-◯-ηˡ) ⟩
            ◯ (∃ λ (f⁻¹ : B → A) →
                 Erased (HA.Proofs (◯-map f) (◯-map-◯ (η f⁻¹))))        ↝⟨ Eq.⟨ _ , commutes-with-Σ ⟩ ⟩

            (∃ λ (f⁻¹ : ◯ (B → A)) →
               ◯ (Erased (HA.Proofs (◯-map f) (◯-map-◯ f⁻¹))))          ↝⟨ (∃-cong λ _ →
                                                                            Modal→Stable $
                                                                            Modal-Erased (
                                                                            Modal-Σ (Modal-Π ext λ _ → Separated-◯ _ _) λ _ →
                                                                            Modal-Σ (Modal-Π ext λ _ → Separated-◯ _ _) λ _ →
                                                                            Modal-Π ext λ _ →
                                                                            Modal→Separated (Separated-◯ _ _) _ _)) ⟩

            (∃ λ (f⁻¹ : ◯ (B → A)) →
               Erased (HA.Proofs (◯-map f) (◯-map-◯ f⁻¹)))              ↝⟨ Σ◯→≃Σ◯→◯ ext ⟩

            (∃ λ (f⁻¹ : ◯ B → ◯ A) → Erased (HA.Proofs (◯-map f) f⁻¹))  ↔⟨⟩

            Is-equivalenceᴱ (◯-map f)                                   □

        -- ◯ (Is-equivalenceᴱ f) is equivalent to
        -- Is-equivalenceᴱ (◯-map f) (assuming function
        -- extensionality).

        ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ :
          ◯ (Is-equivalenceᴱ f) ↝[ a ∣ a ] Is-equivalenceᴱ (◯-map f)
        ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ =
          generalise-ext?′
            ◯-Is-equivalenceᴱ⇔Is-equivalenceᴱ
            (from-equivalence ∘ ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ′)
            ◯-Is-equivalenceᴱ≃ᴱIs-equivalenceᴱ

        -- ◯ commutes with ECP._≃ᴱ_ (assuming function
        -- extensionality).

        ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ : ◯ (A ECP.≃ᴱ B) ↝[ a ∣ a ] (◯ A ECP.≃ᴱ ◯ B)
        ◯≃ᴱ-CP-≃◯≃ᴱ-CP-◯ ext =
          ◯↝↝◯↝◯
            {P = λ f → ECP.Is-equivalenceᴱ f}
            F.id
            ◯-Is-equivalenceᴱ-CP≃Is-equivalenceᴱ-CP
            (λ ext f≡g →
               ECP.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
            (Modal→Stable-Is-equivalenceᴱ-CP ext Modal-◯ Separated-◯)
            ([]-cong.Σ◯→↝Σ◯→◯-Is-equivalenceᴱ-CP ax ext)
            ext

        -- ◯ commutes with _≃ᴱ_ (assuming function extensionality).

        ◯≃ᴱ≃◯≃ᴱ◯ : ◯ (A ≃ᴱ B) ↝[ a ∣ a ] (◯ A ≃ᴱ ◯ B)
        ◯≃ᴱ≃◯≃ᴱ◯ ext =
          ◯↝↝◯↝◯
            (from-equivalence EEq.≃ᴱ-as-Σ)
            ◯-Is-equivalenceᴱ≃Is-equivalenceᴱ
            (λ ext f≡g →
               EEq.[]-cong₂-⊔.Is-equivalenceᴱ-cong ax ax ax ext f≡g)
            (Modal→Stable-Is-equivalenceᴱ ext Modal-◯ Separated-◯)
            ([]-cong.Σ◯→↝Σ◯→◯-Is-equivalenceᴱ ax ext)
            ext

    --------------------------------------------------------------------
    -- Some results that hold if the modality is left exact and
    -- commutes with Σ (in addition to having choice)

    module Left-exact-Commutes-with-Σ
      (lex             : Left-exact-η-cong)
      (commutes-with-Σ : Commutes-with-Σ)
      where

      open Left-exact lex public hiding (module Commutes-with-Σ)
      open Left-exact.Commutes-with-Σ lex commutes-with-Σ public

      -- ◯ commutes with _↝[ k ]_ (assuming function extensionality).

      ◯↝≃◯↝◯ : ◯ (A ↝[ k ] B) ↝[ a ∣ a ] (◯ A ↝[ k ] ◯ B)
      ◯↝≃◯↝◯ {k = implication}         = ◯→≃◯→◯
      ◯↝≃◯↝◯ {k = logical-equivalence} = ◯⇔≃◯⇔◯
      ◯↝≃◯↝◯ {k = injection}           = ◯↣≃◯↣◯ lex
      ◯↝≃◯↝◯ {k = embedding}           = ◯-Embedding≃Embedding-◯-◯ lex
      ◯↝≃◯↝◯ {k = surjection}          = ◯↠≃◯↠◯ lex
      ◯↝≃◯↝◯ {k = bijection}           = ◯↔≃◯↔◯ lex
      ◯↝≃◯↝◯ {k = equivalence}         = ◯≃≃◯≃◯ lex
      ◯↝≃◯↝◯ {k = equivalenceᴱ}        =
        Left-exact.Commutes-with-Σ.◯≃ᴱ≃◯≃ᴱ◯ lex commutes-with-Σ

      -- A variant of MBC.◯-cong-◯.

      ◯-cong-◯ : ◯ (A ↝[ k ] B) → ◯ A ↝[ k ] ◯ B
      ◯-cong-◯ = ◯↝≃◯↝◯ _
