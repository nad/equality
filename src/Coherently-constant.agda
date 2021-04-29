------------------------------------------------------------------------
-- Coherently constant functions
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Coherently-constant
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude hiding (_+_)

open import Eilenberg-MacLane-space eq as K using (K[_]1; base; loop)
open import Embedding equality-with-J as Emb using (Embedding)
open import Equality.Decidable-UIP equality-with-J using (Constant)
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Group eq
open import Group.Finite-cyclic eq as FC using (ℤ/[1+_]ℤ; _≡_mod_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional eq as T using (∥_∥; ∣_∣)
open import Injection equality-with-J using (Injective)
open import Integer eq
open import Pointed-type.Homotopy-group eq
open import Preimage equality-with-J using (_⁻¹_)
import Quotient eq as Q
open import Univalence-axiom equality-with-J

private
  variable
    a b     : Level
    A B C D : Type a
    f       : A → B
    p       : A

-- Coherently constant functions.
--
-- Shulman uses the term "conditionally constant" in "Not every weakly
-- constant function is conditionally constant"
-- (https://homotopytypetheory.org/2015/06/11/not-every-weakly-constant-function-is-conditionally-constant/).
-- I do not know who first came up with this definition.

Coherently-constant :
  {A : Type a} {B : Type b} → (A → B) → Type (a ⊔ b)
Coherently-constant {A = A} {B = B} f =
  ∃ λ (g : ∥ A ∥ → B) → f ≡ g ∘ ∣_∣

-- Every coherently constant function is weakly constant.
--
-- This result is mentioned by Shulman.

Coherently-constant→Constant :
  Coherently-constant f → Constant f
Coherently-constant→Constant {f = f} (g , eq) x y =
  f x      ≡⟨ cong (_$ x) eq ⟩
  g ∣ x ∣  ≡⟨ cong g (T.truncation-is-proposition _ _) ⟩
  g ∣ y ∣  ≡⟨ sym $ cong (_$ y) eq ⟩∎
  f y      ∎

-- Every weakly constant function with a stable domain is coherently
-- constant.
--
-- This result was proved by Kraus, Escardó, Coquand and Altenkirch in
-- "Notions of Anonymous Existence in Martin-Löf Type Theory".

Stable-domain→Constant→Coherently-constant :
  {f : A → B} →
  (∥ A ∥ → A) → Constant f → Coherently-constant f
Stable-domain→Constant→Coherently-constant {f = f} s c =
    f ∘ s
  , ⟨ext⟩ λ x →
      f x          ≡⟨ c _ _ ⟩∎
      f (s ∣ x ∣)  ∎

private

  -- Definitions used in the proof of ¬-Constant→Coherently-constant.

  module ¬-Constant→Coherently-constant
    (univ : Univalence lzero)
    where

    -- CCC C is the statement that every constant function from a
    -- merely inhabited type in Type to C is coherently constant.

    CCC : Type → Type₁
    CCC C =
      (B : Type) → ∥ B ∥ →
      (g : B → C) → Constant g → Coherently-constant g

    Has-retraction : {A B : Type} → (A → B) → Type
    Has-retraction f = ∃ λ g → g ∘ f ≡ id

    -- IR C is the statement that every injective, (-1)-connected
    -- function from C to a type in Type has a retraction.

    IR : Type → Type₁
    IR C =
      (A : Type) (f : C → A) → (∀ x → ∥ f ⁻¹ x ∥) →
      Injective f → Has-retraction f

    -- CCC C implies IR C.

    CCC→IR : CCC C → IR C
    CCC→IR {C = C} ccc A f conn inj =
        (λ a → proj₁ (cc a) (conn a))
      , ⟨ext⟩ λ c →
          proj₁ (cc (f c)) (conn (f c))    ≡⟨ cong (proj₁ (cc (f c))) $ T.truncation-is-proposition _ _ ⟩
          proj₁ (cc (f c)) ∣ c , refl _ ∣  ≡⟨ sym $ cong (_$ c , refl _) $ proj₂ (cc (f c)) ⟩∎
          c                                ∎
      where
      cc : (a : A) → Coherently-constant {A = f ⁻¹ a} proj₁
      cc a = ccc (f ⁻¹ a) (conn a) proj₁ λ (c₁ , p₁) (c₂ , p₂) →
        inj (f c₁  ≡⟨ p₁ ⟩
             a     ≡⟨ sym p₂ ⟩∎
             f c₂  ∎)

    -- If there is an embedding from C to D, then CCC D implies CCC C.

    CCC→CCC : Embedding C D → CCC D → CCC C
    CCC→CCC emb ccc B ∥B∥ g c = proj₁ ∘ h , refl _
      where
      e = Embedding.to emb

      cc : Coherently-constant (e ∘ g)
      cc = ccc B ∥B∥ (e ∘ g) λ x y →
        e (g x)  ≡⟨ cong e (c x y) ⟩∎
        e (g y)  ∎

      h : (b : ∥ B ∥) → ∃ λ c → e c ≡ proj₁ cc b
      h = T.elim _ (λ _ → Emb.embedding→⁻¹-propositional
                            (Embedding.is-embedding emb) _) λ b →
        g b , cong (_$ b) (proj₂ cc)

    -- If CCC (A ≃ A) holds for every type A, then CCC K[ G ]1 holds
    -- for every abelian group G.

    CCC-≃→CCC-K :
      ((A : Type) → CCC (A ≃ A)) →
      (G : Group lzero) → Abelian G → CCC K[ G ]1
    CCC-≃→CCC-K ccc G abelian =
                               $⟨ ccc K[ G ]1 ⟩
      CCC (K[ G ]1 ≃ K[ G ]1)  ↝⟨ CCC→CCC emb ⟩□
      CCC K[ G ]1              □
      where
      Aut[K[G]] = (K[ G ]1 ≃ K[ G ]1) , Eq.id

      Aut[K[G]]-groupoid : H-level 3 (K[ G ]1 ≃ K[ G ]1)
      Aut[K[G]]-groupoid = Eq.left-closure ext 2 K.is-groupoid

      Ω[Aut[K[G]]] =
        Fundamental-group′ Aut[K[G]] Aut[K[G]]-groupoid

      emb : Embedding K[ G ]1 (K[ G ]1 ≃ K[ G ]1)
      emb =
        K[ G ]1             ↔⟨ inverse $ K.cong-≃ $ K.Fundamental-group′[K1≃K1]≃ᴳ univ abelian ⟩
        K[ Ω[Aut[K[G]]] ]1  ↝⟨ proj₁ $ K.K[Fundamental-group′]1↣ᴮ univ Aut[K[G]]-groupoid ⟩□
        proj₁ Aut[K[G]]     □

    -- The group of integers.

    module ℤG = Group ℤ-group

    -- The groups ℤ/2ℤ and ℤ/4ℤ.

    ℤ/2ℤ = ℤ/[1+ 1 ]ℤ
    ℤ/4ℤ = ℤ/[1+ 3 ]ℤ

    module ℤ/2ℤ where
      open Group ℤ/2ℤ public
        renaming (_∘_ to infixl 6 _+_; _⁻¹ to infix 8 -_)

    module ℤ/4ℤ where
      open Group ℤ/4ℤ public
        renaming (_∘_ to infixl 6 _+_; _⁻¹ to infix 8 -_)

    -- Multiplication by two, as a function from ℤ/2ℤ to ℤ/4ℤ.

    mul2 : ℤ/2ℤ.Carrier → ℤ/4ℤ.Carrier
    mul2 = Q.rec λ where
      .Q.[]ʳ i                                 → Q.[ i *+ 2 ]
      .Q.is-setʳ                               → Q./-is-set
      .Q.[]-respects-relationʳ {x = i} {y = j} →
        i ≡ j mod 2                  ↝⟨ FC.*+-cong {j = j} {n = 2} 2 ⟩
        i *+ 2 ≡ j *+ 2 mod 4        ↝⟨ Q.[]-respects-relation ⟩□
        Q.[ i *+ 2 ] ≡ Q.[ j *+ 2 ]  □

    -- The function mul2, expressed as a group homomorphism.

    mul2ʰ : ℤ/2ℤ →ᴳ ℤ/4ℤ
    mul2ʰ = λ where
      .related     → mul2
      .homomorphic → Q.elim-prop λ where
        .Q.is-propositionʳ _ → Π-closure ext 1 λ _ →
                               Group.Carrier-is-set ℤ/[1+ 3 ]ℤ
        .Q.[]ʳ i → Q.elim-prop λ where
          .Q.is-propositionʳ _ → Group.Carrier-is-set ℤ/[1+ 3 ]ℤ
          .Q.[]ʳ j → cong Q.[_]
            ((i + j) *+ 2     ≡⟨ *+-distrib-+ {i = i} 2 ⟩∎
             i *+ 2 + j *+ 2  ∎)

    -- Integer division by 2, as a function from ℤ/4ℤ to ℤ/2ℤ.

    div2 : ℤ/4ℤ.Carrier → ℤ/2ℤ.Carrier
    div2 = Q.rec λ where
      .Q.[]ʳ i                                 → Q.[ ⌊ i /2⌋ ]
      .Q.is-setʳ                               → Q./-is-set
      .Q.[]-respects-relationʳ {x = i} {y = j} →
        i ≡ j mod 4                    ↝⟨ FC.⌊/2⌋-cong j 2 ⟩
        ⌊ i /2⌋ ≡ ⌊ j /2⌋ mod 2        ↝⟨ Q.[]-respects-relation ⟩□
        Q.[ ⌊ i /2⌋ ] ≡ Q.[ ⌊ j /2⌋ ]  □

    -- Some lemmas relating mul2 and div2.

    mul2-div2-lemma₁ :
      ∀ i j → div2 (j ℤ/4ℤ.+ ℤ/4ℤ.- mul2 i) ≡ div2 j ℤ/2ℤ.+ ℤ/2ℤ.- i
    mul2-div2-lemma₁ = Q.elim-prop λ where
      .Q.is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        Q./-is-set
      .Q.[]ʳ i → Q.elim-prop λ where
        .Q.is-propositionʳ _ → Q./-is-set
        .Q.[]ʳ j             → cong Q.[_]
          (⌊ j - i *+ 2 /2⌋    ≡⟨ cong (⌊_/2⌋ ∘ _+_ j) $ ℤG.^+⁻¹ {p = i} 2 ⟩
           ⌊ j + - i *+ 2 /2⌋  ≡⟨ ⌊+*+2/2⌋≡ j ⟩∎
           ⌊ j /2⌋ + - i       ∎)

    mul2-div2-lemma₂ :
      ∀ i j → ℤ/2ℤ.- i ℤ/2ℤ.+ div2 (mul2 i ℤ/4ℤ.+ j) ≡ div2 j
    mul2-div2-lemma₂ = Q.elim-prop λ where
      .Q.is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        Q./-is-set
      .Q.[]ʳ i → Q.elim-prop λ where
        .Q.is-propositionʳ _ → Q./-is-set
        .Q.[]ʳ j             → cong Q.[_]
          (- i + ⌊ i *+ 2 + j /2⌋  ≡⟨ cong (_+_ (- i) ∘ ⌊_/2⌋) $ +-comm (i *+ 2) ⟩
           - i + ⌊ j + i *+ 2 /2⌋  ≡⟨ cong (_+_ (- i)) $ ⌊+*+2/2⌋≡ j ⟩
           - i + (⌊ j /2⌋ + i)     ≡⟨ cong (_+_ (- i)) $ +-comm ⌊ j /2⌋ ⟩
           - i + (i + ⌊ j /2⌋)     ≡⟨ +-assoc (- i) ⟩
           - i + i + ⌊ j /2⌋       ≡⟨ cong (_+ ⌊ j /2⌋) $ +-left-inverse i ⟩
           + 0 + ⌊ j /2⌋           ≡⟨ +-left-identity ⟩∎
           ⌊ j /2⌋                 ∎)

    -- The type K[ ℤ/4ℤ ]1 is (-1)-connected.

    K[ℤ/4ℤ]-connected : (x : K[ ℤ/4ℤ ]1) → ∥ K.map mul2ʰ ⁻¹ x ∥
    K[ℤ/4ℤ]-connected = K.elim-set λ where
      .K.baseʳ     → ∣ base , refl _ ∣
      .K.loopʳ _   → T.truncation-is-proposition _ _
      .K.is-setʳ _ → mono₁ 1 T.truncation-is-proposition

    -- Two equivalences.

    Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ : _≡_ {A = K[ ℤ/4ℤ ]1} base base ≃ ℤ/4ℤ.Carrier
    Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ =
      K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid .related

    Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ : _≡_ {A = K[ ℤ/2ℤ ]1} base base ≃ ℤ/2ℤ.Carrier
    Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ =
      K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid .related

    -- The function K.map mul2ʰ is injective.

    inj : Injective (K.map mul2ʰ)
    inj {x = x} {y = y} = K.elim-set e x y
      where
      lemma = K.elim-set λ where
        .K.is-setʳ _ →
          Π-closure ext 2 λ _ →
          K.is-groupoid
        .K.baseʳ →
          base ≡ base   ↔⟨ Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ ⟩
          ℤ/4ℤ.Carrier  ↝⟨ div2 ⟩
          ℤ/2ℤ.Carrier  ↔⟨ inverse Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ ⟩□
          base ≡ base   □
        .K.loopʳ i → ⟨ext⟩ λ eq →
          let j = _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ eq in

          subst (λ y → base ≡ K.map mul2ʰ y → base ≡ y)
            (loop i) (loop ∘ div2 ∘ _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ) eq        ≡⟨ subst-→ ⟩

          subst (base ≡_) (loop i)
            (loop $ div2 $ _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ $
             subst ((base ≡_) ∘ K.map mul2ʰ) (sym (loop i)) eq)       ≡⟨ trans (sym trans-subst) $
                                                                         cong (flip trans _) $
                                                                         cong (loop ∘ div2 ∘ _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ) $
                                                                         trans (subst-∘ _ _ _) $
                                                                         trans (sym trans-subst) $
                                                                         cong (trans _) $
                                                                         trans (cong-sym _ _) $
                                                                         cong sym $ K.rec-loop ⟩
          trans
            (loop $ div2 $ _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ $
             trans eq (sym (loop (mul2 i))))
            (loop i)                                                  ≡⟨ cong (flip trans _) $ cong (loop ∘ div2) $
                                                                         K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid .homomorphic _ _ ⟩
          trans
            (loop $ div2 $
             j ℤ/4ℤ.+ _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ (sym (loop (mul2 i))))
            (loop i)                                                  ≡⟨ cong (flip trans _) $ cong (loop ∘ div2 ∘ (j ℤ/4ℤ.+_)) $
                                                                         →ᴳ-⁻¹ (K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid) _ ⟩
          trans
            (loop $ div2 $
             j ℤ/4ℤ.+ ℤ/4ℤ.- _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ (loop (mul2 i)))
            (loop i)                                                  ≡⟨ cong (flip trans _ ∘ loop ∘ div2 ∘ (j ℤ/4ℤ.+_) ∘ ℤ/4ℤ.-_) $
                                                                         _≃_.right-inverse-of Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ _ ⟩

          trans (loop (div2 (j ℤ/4ℤ.+ ℤ/4ℤ.- mul2 i))) (loop i)       ≡⟨ cong (flip trans _) $ cong loop $ mul2-div2-lemma₁ i j ⟩

          trans (loop (div2 j ℤ/2ℤ.+ ℤ/2ℤ.- i)) (loop i)              ≡⟨ cong (flip trans _) $
                                                                         ≃ᴳ-sym {G₂ = ℤ/2ℤ} (K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid)
                                                                           .homomorphic _ _ ⟩

          trans (trans (loop (div2 j)) (loop (ℤ/2ℤ.- i))) (loop i)    ≡⟨ cong (flip trans _) $ cong (trans _) $
                                                                         →ᴳ-⁻¹ (≃ᴳ-sym $ K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid) _ ⟩

          trans (trans (loop (div2 j)) (sym (loop i))) (loop i)       ≡⟨ trans (trans-assoc _ _ _) $
                                                                         trans (cong (trans _) $ trans-symˡ _) $
                                                                         trans-reflʳ _ ⟩∎
          loop (div2 j)                                               ∎

      e = λ where
        .K.is-setʳ _ →
          Π-closure ext 2 λ _ →
          Π-closure ext 2 λ _ →
          K.is-groupoid
        .K.baseʳ   → lemma
        .K.loopʳ i → ⟨ext⟩ $ K.elim-prop λ where
          .K.is-propositionʳ _ → Π-closure ext 2 λ _ →
                                 K.is-groupoid
          .K.baseʳ             → ⟨ext⟩ λ eq →
            let j = _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ eq in

            subst (λ x → ∀ y → K.map mul2ʰ x ≡ K.map mul2ʰ y → x ≡ y)
              (loop i) lemma base eq                                   ≡⟨ trans (cong (_$ eq) $ sym $
                                                                                 push-subst-application _ _)
                                                                          subst-→ ⟩
            subst (_≡ base) (loop i)
              (lemma base $
               subst (λ x → K.map mul2ʰ x ≡ K.map mul2ʰ base)
                 (sym (loop i)) eq)                                    ≡⟨ trans subst-trans-sym $
                                                                          cong (trans _) $ cong (lemma base) $
                                                                          trans (subst-∘ _ _ _) $
                                                                          subst-trans-sym ⟩
            trans (sym $ loop i)
              (lemma base $
               trans (sym (cong (K.map mul2ʰ) (sym (loop i)))) eq)     ≡⟨ cong (trans _) $ cong (lemma base) $ cong (flip trans _) $
                                                                          trans (sym $ cong-sym _ _) $
                                                                          cong (cong _) $ sym-sym _ ⟩
            trans (sym $ loop i)
              (lemma base (trans (cong (K.map mul2ʰ) (loop i)) eq))    ≡⟨ cong (trans _) $ cong (lemma base) $ cong (flip trans _)
                                                                          K.rec-loop ⟩
            trans (sym $ loop i)
              (lemma base (trans (loop (mul2 i)) eq))                  ≡⟨⟩

            trans (sym $ loop i)
              (loop $ div2 $ _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ $
               trans (loop (mul2 i)) eq)                               ≡⟨ cong₂ (λ p q → trans p (loop (div2 q)))
                                                                            (sym $
                                                                             →ᴳ-⁻¹ (≃ᴳ-sym $ K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid) _)
                                                                            (K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid .homomorphic _ _) ⟩
            trans (loop (ℤ/2ℤ.- i))
              (loop $ div2 $
               _≃_.to Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ (loop (mul2 i)) ℤ/4ℤ.+ j)        ≡⟨ cong (trans (loop (ℤ/2ℤ.- i)) ∘ loop ∘ div2 ∘ (ℤ/4ℤ._+ j)) $
                                                                          _≃_.right-inverse-of Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ _ ⟩

            trans (loop (ℤ/2ℤ.- i)) (loop (div2 (mul2 i ℤ/4ℤ.+ j)))    ≡⟨ sym $
                                                                          ≃ᴳ-sym (K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid)
                                                                            .homomorphic _ _ ⟩

            loop (ℤ/2ℤ.- i ℤ/2ℤ.+ div2 (mul2 i ℤ/4ℤ.+ j))              ≡⟨ cong loop $ mul2-div2-lemma₂ i j ⟩

            loop (div2 j)                                              ≡⟨⟩

            lemma base eq                                              ∎

    -- It is not the case that IR holds for K[ ℤ/2ℤ ]1.

    ¬IR : ¬ IR K[ ℤ/2ℤ ]1
    ¬IR ir = contradiction
      where
      -- The function K.map mul2ʰ has a retraction.

      map-mul2ʰ-has-retraction : Has-retraction (K.map mul2ʰ)
      map-mul2ʰ-has-retraction =
        ir K[ ℤ/[1+ 3 ]ℤ ]1 (K.map mul2ʰ) K[ℤ/4ℤ]-connected inj

      -- The retraction, and the proof showing that it is a
      -- retraction.

      r₁ : K[ ℤ/4ℤ ]1 → K[ ℤ/2ℤ ]1
      r₁ = proj₁ map-mul2ʰ-has-retraction

      r₁-retraction : r₁ ∘ K.map mul2ʰ ≡ id
      r₁-retraction = proj₂ map-mul2ʰ-has-retraction

      -- A lemma related to r₁.

      r₁-lemma :
        trans (sym $ cong (_$ base) r₁-retraction)
          (trans (cong r₁ (cong (K.map mul2ʰ) p))
             (cong (_$ base) r₁-retraction)) ≡
        p
      r₁-lemma {p = p} =
        trans (sym $ cong (_$ base) r₁-retraction)
          (trans (cong r₁ (cong (K.map mul2ʰ) p))
             (cong (_$ base) r₁-retraction))        ≡⟨ cong (trans _) $ cong (flip trans _) $
                                                       cong-∘ _ _ _ ⟩
        trans (sym $ cong (_$ base) r₁-retraction)
          (trans (cong (r₁ ∘ K.map mul2ʰ) p)
             (cong (_$ base) r₁-retraction))        ≡⟨ cong (trans _) $
                                                       naturality (λ x → cong (_$ x) r₁-retraction) ⟩
        trans (sym $ cong (_$ base) r₁-retraction)
          (trans (cong (_$ base) r₁-retraction)
             (cong id p))                           ≡⟨ trans-sym-[trans] _ _ ⟩

        cong id p                                   ≡⟨ sym $ cong-id _ ⟩∎

        p                                           ∎

      -- A variant of r₁ that is definitionally equal to base for
      -- base.

      r₂ : K[ ℤ/4ℤ ]1 → K[ ℤ/2ℤ ]1
      r₂ = K.rec λ where
        .K.baseʳ → base

        .K.loopʳ i →
          base     ≡⟨ sym $ cong (_$ base) r₁-retraction ⟩
          r₁ base  ≡⟨ cong r₁ (loop i) ⟩
          r₁ base  ≡⟨ cong (_$ base) r₁-retraction ⟩∎
          base     ∎

        .K.loop-idʳ →
          trans (sym $ cong (_$ base) r₁-retraction)
            (trans (cong r₁ (loop ℤ/4ℤ.id))
               (cong (_$ base) r₁-retraction))                    ≡⟨ cong (trans _) $ cong (flip trans _) $ cong (cong r₁) $ sym
                                                                     K.rec-loop ⟩
          trans (sym $ cong (_$ base) r₁-retraction)
            (trans (cong r₁ (cong (K.map mul2ʰ) (loop ℤ/2ℤ.id)))
               (cong (_$ base) r₁-retraction))                    ≡⟨ r₁-lemma ⟩

          loop ℤ/2ℤ.id                                            ≡⟨ K.loop-id ⟩∎

          refl _                                                  ∎

        .K.loop-∘ʳ {x = x} {y = y} →
          trans (sym $ cong (_$ base) r₁-retraction)
            (trans (cong r₁ (loop (x ℤ/4ℤ.+ y)))
               (cong (_$ base) r₁-retraction))           ≡⟨ cong (trans _) $ cong (flip trans _) $ cong (cong r₁) $
                                                            K.loop-∘ ⟩
          trans (sym $ cong (_$ base) r₁-retraction)
            (trans (cong r₁ (trans (loop x) (loop y)))
               (cong (_$ base) r₁-retraction))           ≡⟨ trans (cong (trans _) $
                                                                   trans (cong (flip trans _) $
                                                                          cong-trans _ _ _) $
                                                                   trans-assoc _ _ _) $
                                                            sym $ trans-assoc _ _ _ ⟩
          trans
            (trans (sym $ cong (_$ base) r₁-retraction)
               (cong r₁ (loop x)))
            (trans (cong r₁ (loop y))
               (cong (_$ base) r₁-retraction))           ≡⟨ trans (cong (trans _) $ sym $
                                                                   trans--[trans-sym] _ _) $
                                                            trans (sym $ trans-assoc _ _ _) $
                                                            cong (flip trans _) $
                                                            trans-assoc _ _ _ ⟩∎
          trans
            (trans (sym $ cong (_$ base) r₁-retraction)
               (trans (cong r₁ (loop x))
                  (cong (_$ base) r₁-retraction)))
            (trans (sym $ cong (_$ base) r₁-retraction)
               (trans (cong r₁ (loop y))
                  (cong (_$ base) r₁-retraction)))       ∎

        .K.is-groupoidʳ → K.is-groupoid

      -- The functions r₁ and r₂ are pointwise equal.

      r₁≡r₂ : ∀ x → r₁ x ≡ r₂ x
      r₁≡r₂ = K.elim-set λ where
        .K.is-setʳ _ → K.is-groupoid
        .K.baseʳ     →
          r₁ base  ≡⟨ cong (_$ base) r₁-retraction ⟩∎
          r₂ base  ∎
        .K.loopʳ i →
          subst (λ x → r₁ x ≡ r₂ x) (loop i)
            (cong (_$ base) r₁-retraction)                  ≡⟨ subst-in-terms-of-trans-and-cong ⟩

          trans (sym (cong r₁ (loop i)))
            (trans (cong (_$ base) r₁-retraction)
               (cong r₂ (loop i)))                          ≡⟨ cong (trans _) $ cong (trans _)
                                                               K.rec-loop ⟩
          trans (sym (cong r₁ (loop i)))
            (trans (cong (_$ base) r₁-retraction)
               (trans (sym $ cong (_$ base) r₁-retraction)
                  (trans (cong r₁ (loop i))
                     (cong (_$ base) r₁-retraction))))      ≡⟨ cong (trans _) $
                                                               trans--[trans-sym] _ _ ⟩
          trans (sym (cong r₁ (loop i)))
            (trans (cong r₁ (loop i))
               (cong (_$ base) r₁-retraction))              ≡⟨ trans-sym-[trans] _ _ ⟩∎

          cong (_$ base) r₁-retraction                      ∎

      -- Thus r₂ is also a retraction of K.map mul2ʰ.

      r₂-retraction : r₂ ∘ K.map mul2ʰ ≡ id
      r₂-retraction =
        r₂ ∘ K.map mul2ʰ  ≡⟨ cong (_∘ K.map mul2ʰ) $ sym $ ⟨ext⟩ r₁≡r₂ ⟩
        r₁ ∘ K.map mul2ʰ  ≡⟨ r₁-retraction ⟩∎
        id                ∎

      -- A group homomorphism from ℤ/4ℤ to ℤ/2ℤ.

      r₃ : ℤ/4ℤ →ᴳ ℤ/2ℤ
      r₃ .related =
        ℤ/4ℤ.Carrier  ↔⟨ inverse Ω[K[ℤ/4ℤ]]≃ℤ/4ℤ ⟩
        base ≡ base   ↝⟨ cong r₂ ⟩
        base ≡ base   ↔⟨ Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ ⟩□
        ℤ/2ℤ.Carrier  □
      r₃ .homomorphic i j =
        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ (cong r₂ (loop (i ℤ/4ℤ.+ j)))        ≡⟨ cong (_≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ ∘ cong r₂) K.loop-∘ ⟩

        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ (cong r₂ (trans (loop i) (loop j)))  ≡⟨ cong (_≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ) $ cong-trans _ _ _ ⟩

        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ
          (trans (cong r₂ (loop i)) (cong r₂ (loop j)))             ≡⟨ K.Fundamental-group′[K1]≃ᴳ univ K.is-groupoid
                                                                         .homomorphic _ _ ⟩∎
        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ (cong r₂ (loop i)) ℤ/2ℤ.+
        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ (cong r₂ (loop j))                   ∎

      -- The homomorphism r₃ is a retraction of mul2.

      r₃-retraction : ∀ i → Homomorphic.to r₃ (mul2 i) ≡ i
      r₃-retraction i =
        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ (cong r₂ (loop (mul2 i)))  ≡⟨ cong (_≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ) lemma ⟩
        _≃_.to Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ (loop i)                   ≡⟨ _≃_.right-inverse-of Ω[K[ℤ/2ℤ]]≃ℤ/2ℤ _ ⟩∎
        i                                                 ∎
        where
        lemma =
          cong r₂ (loop (mul2 i))                           ≡⟨ K.rec-loop ⟩

          trans (sym $ cong (_$ base) r₁-retraction)
            (trans (cong r₁ (loop (mul2 i)))
               (cong (_$ base) r₁-retraction))              ≡⟨ cong (trans _) $ cong (flip trans _) $ cong (cong r₁) $ sym
                                                               K.rec-loop ⟩
          trans (sym $ cong (_$ base) r₁-retraction)
            (trans (cong r₁ (cong (K.map mul2ʰ) (loop i)))
               (cong (_$ base) r₁-retraction))              ≡⟨ r₁-lemma ⟩∎

          loop i                                            ∎

      -- 0 and 1 are equal when viewed as elements of ℤ/2ℤ.

      0≡1 : _≡_ {A = ℤ/2ℤ.Carrier} Q.[ + 0 ] Q.[ + 1 ]
      0≡1 =
        Q.[ + 0 ]                           ≡⟨ sym $ FC.+≡0 (Homomorphic.to r₃ Q.[ + 1 ]) ⟩

        Homomorphic.to r₃ Q.[ + 1 ] ℤ/2ℤ.+
        Homomorphic.to r₃ Q.[ + 1 ]         ≡⟨ sym $ r₃ .homomorphic Q.[ + 1 ] Q.[ + 1 ] ⟩

        Homomorphic.to r₃ Q.[ + 2 ]         ≡⟨⟩

        Homomorphic.to r₃ (mul2 Q.[ + 1 ])  ≡⟨ r₃-retraction Q.[ + 1 ] ⟩∎

        Q.[ + 1 ]                           ∎

      -- However, this is contradictory.

      contradiction : ⊥
      contradiction = FC.0≢1 0 0≡1

-- It is not the case that, for every type A : Type and merely
-- inhabited type B : Type, every weakly constant function from B to
-- A ≃ A is coherently constant (assuming univalence).
--
-- This result is due to Sattler (personal communication), building on
-- work by Shulman (see "Not every weakly constant function is
-- conditionally constant").

¬-Constant→Coherently-constant :
  Univalence lzero →
  ¬ ((A B : Type) → ∥ B ∥ →
     (g : B → A ≃ A) → Constant g → Coherently-constant g)
¬-Constant→Coherently-constant univ =
  ((A : Type) → CCC (A ≃ A))                     ↝⟨ CCC-≃→CCC-K ⟩
  ((G : Group lzero) → Abelian G → CCC K[ G ]1)  ↝⟨ (λ hyp G abelian → CCC→IR (hyp G abelian)) ⟩
  ((G : Group lzero) → Abelian G → IR K[ G ]1)   ↝⟨ (λ hyp → hyp ℤ/[1+ 1 ]ℤ FC.abelian) ⟩
  IR K[ ℤ/[1+ 1 ]ℤ ]1                            ↝⟨ ¬IR ⟩□
  ⊥                                              □
  where
  open ¬-Constant→Coherently-constant univ
