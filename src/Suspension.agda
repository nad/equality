------------------------------------------------------------------------
-- Suspensions
------------------------------------------------------------------------

{-# OPTIONS --cubical=no-glue --safe #-}

-- The beginning of this module follows the HoTT book rather closely.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining suspensions uses path equality, but
-- the supplied notion of equality is used for many other things.

import Equality.Path as P

module Suspension
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J as Embedding using (Embedding)
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (_↣_)
open import Interval eq as Interval using (Interval; [0]; [1]; 0≡1)
import Nat equality-with-J as Nat
open import Pointed-type equality-with-J
  using (Pointed-type; _→ᴮ_; Ω)
open import Surjection equality-with-J using (_↠_)

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level
    A B           : Type a
    P             : A → Type p
    C             : Pointed-type a
    e r x y       : A
    f g           : A → B

-- Suspensions.

data Susp (A : Type a) : Type a where
  north south : Susp A
  meridianᴾ   : A → north P.≡ south

-- Meridians.

meridian : A → _≡_ {A = Susp A} north south
meridian = _↔_.from ≡↔≡ ∘ meridianᴾ

-- A dependent eliminator, expressed using paths.

record Elimᴾ {A : Type a} (P : Susp A → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    northʳ    : P north
    southʳ    : P south
    meridianʳ : ∀ x → P.[ (λ i → P (meridianᴾ x i)) ] northʳ ≡ southʳ

open Elimᴾ public

elimᴾ : Elimᴾ P → (x : Susp A) → P x
elimᴾ {A} {P} e = helper
  where
  module E = Elimᴾ e

  helper : (x : Susp A) → P x
  helper north           = E.northʳ
  helper south           = E.southʳ
  helper (meridianᴾ x i) = E.meridianʳ x i

-- A non-dependent eliminator, expressed using paths.

record Recᴾ (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    northʳ    : B
    southʳ    : B
    meridianʳ : A → northʳ P.≡ southʳ

open Recᴾ public

recᴾ : Recᴾ A B → Susp A → B
recᴾ {A} {B} r = elimᴾ eᴾ
  where
  module R = Recᴾ r

  eᴾ : Elimᴾ (λ (_ : Susp A) → B)
  eᴾ .northʳ    = R.northʳ
  eᴾ .southʳ    = R.southʳ
  eᴾ .meridianʳ = R.meridianʳ

-- A dependent eliminator.

record Elim {A : Type a} (P : Susp A → Type p) : Type (a ⊔ p) where
  no-eta-equality
  field
    northʳ    : P north
    southʳ    : P south
    meridianʳ : ∀ x → subst P (meridian x) northʳ ≡ southʳ

open Elim public

elim : Elim P → (x : Susp A) → P x
elim {P} e = elimᴾ eᴾ
  where
  module E = Elim e

  eᴾ : Elimᴾ P
  eᴾ .northʳ    = E.northʳ
  eᴾ .southʳ    = E.southʳ
  eᴾ .meridianʳ = subst≡→[]≡ ∘ E.meridianʳ

-- A "computation rule" for meridians.

elim-meridian : dcong (elim e) (meridian x) ≡ e .meridianʳ x
elim-meridian = dcong-subst≡→[]≡ (refl _)

-- A non-dependent eliminator.

record Rec (A : Type a) (B : Type b) : Type (a ⊔ b) where
  no-eta-equality
  field
    northʳ    : B
    southʳ    : B
    meridianʳ : A → northʳ ≡ southʳ

open Rec public

rec : Rec A B → Susp A → B
rec {A} {B} r = recᴾ rᴾ
  where
  module R = Rec r

  rᴾ : Recᴾ A B
  rᴾ .northʳ    = R.northʳ
  rᴾ .southʳ    = R.southʳ
  rᴾ .meridianʳ = _↔_.to ≡↔≡ ∘ R.meridianʳ

-- A "computation rule" for meridians.

rec-meridian : cong (rec r) (meridian x) ≡ r .meridianʳ x
rec-meridian = cong-≡↔≡ (refl _)

-- The universal property of suspensions.

universal-property :
  (Susp A → B) ↔ (∃ λ (n : B) → ∃ λ (s : B) → A → n ≡ s)
universal-property {A} {B} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f north , f south , cong f ∘ meridian
      ; from = rec ∘ from′
      }
    ; right-inverse-of = λ x@(n , s , m) →
        n , s , cong (rec (from′ x)) ∘ meridian  ≡⟨ cong (λ m → n , s , m) $ ⟨ext⟩ (λ _ → rec-meridian) ⟩∎
        n , s , m                                ∎
    }
  ; left-inverse-of = λ f →
      let r = from′ (f north , f south , cong f ∘ meridian)

          lemma = λ x →
            subst (λ x → rec r x ≡ f x) (meridian x) (refl _)        ≡⟨ subst-in-terms-of-trans-and-cong ⟩

            trans (sym $ cong (rec r) (meridian x))
                  (trans (refl _) (cong f (meridian x)))             ≡⟨ cong₂ (λ p q → trans (sym p) q) rec-meridian (trans-reflˡ _) ⟩

            trans (sym $ cong f (meridian x)) (cong f (meridian x))  ≡⟨ trans-symˡ _ ⟩∎

            refl _                                                   ∎
      in
      rec r  ≡⟨ (⟨ext⟩ $ elim λ where
                   .northʳ    → refl _
                   .southʳ    → refl _
                   .meridianʳ → lemma) ⟩∎
      f      ∎
  }
  where
  from′ : (∃ λ (n : B) → ∃ λ (s : B) → A → n ≡ s) → Rec A B
  from′ (n , s , m) .northʳ    = n
  from′ (n , s , m) .southʳ    = s
  from′ (n , s , m) .meridianʳ = m

-- Based maps from suspensions of pointed types (using north as the
-- point) are isomorphic to based maps to loop spaces.

Susp→ᴮ↔ : (Susp A , north) →ᴮ C ↔ (A , x) →ᴮ Ω C
Susp→ᴮ↔ {A} {C = B , y} {x} =
  (Susp A , north) →ᴮ (B , y)                                            ↔⟨⟩
  (∃ λ (f : Susp A → B) → f north ≡ y)                                   ↝⟨ Σ-cong universal-property (λ _ → F.id) ⟩
  (∃ λ (f : ∃ λ n → ∃ λ s → A → n ≡ s) → proj₁ f ≡ y)                    ↝⟨ inverse Σ-assoc ⟩
  (∃ λ n → (∃ λ s → A → n ≡ s) × n ≡ y)                                  ↝⟨ (∃-cong λ _ → inverse Σ-assoc) ⟩
  (∃ λ n → ∃ λ s → (A → n ≡ s) × n ≡ y)                                  ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ×-comm) ⟩
  (∃ λ n → ∃ λ s → n ≡ y × (A → n ≡ s))                                  ↝⟨ (∃-cong λ _ → ∃-comm) ⟩
  (∃ λ n → n ≡ y × ∃ λ s → A → n ≡ s)                                    ↝⟨ Σ-assoc ⟩
  (∃ λ (p : ∃ λ n → n ≡ y) → ∃ λ s → A → proj₁ p ≡ s)                    ↝⟨ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $ singleton-contractible _ ⟩
  (∃ λ s → A → y ≡ s)                                                    ↝⟨ (∃-cong λ _ → inverse $ drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                             other-singleton-contractible _) ⟩
  (∃ λ s → ∃ λ (f : A → y ≡ s) → ∃ λ (eq : y ≡ s) → f x ≡ eq)            ↝⟨ (∃-cong λ _ → ∃-comm) ⟩
  (∃ λ s → ∃ λ (eq : y ≡ s) → ∃ λ (f : A → y ≡ s) → f x ≡ eq)            ↝⟨ Σ-assoc ⟩
  (∃ λ (p : ∃ λ s → y ≡ s) → ∃ λ (f : A → y ≡ proj₁ p) → f x ≡ proj₂ p)  ↝⟨ drop-⊤-left-Σ $ _⇔_.to contractible⇔↔⊤ $
                                                                            other-singleton-contractible _ ⟩
  (∃ λ (f : A → y ≡ y) → f x ≡ refl y)                                   ↔⟨⟩
  (A , x) →ᴮ (Ω (B , y))                                                 □

-- The type of booleans can be expressed as a suspension.

Bool↔Susp-⊥ : Bool ↔ Susp (⊥ {ℓ = ℓ})
Bool↔Susp-⊥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = if_then north else south
      ; from = rec λ where
          .northʳ → true
          .southʳ → false
      }
    ; right-inverse-of = elim λ where
        .northʳ → refl _
        .southʳ → refl _
    }
  ; left-inverse-of = λ where
      true  → refl _
      false → refl _
  }

private

  -- A lemma used in some proofs below.

  subst-in-terms-of-trans-and-cong′ :
    {x≡y : x ≡ y} {fgx≡x : f (g x) ≡ x} →
    subst (λ z → f (g z) ≡ z) x≡y fgx≡x ≡
    trans (sym (cong f (cong g x≡y))) (trans fgx≡x x≡y)
  subst-in-terms-of-trans-and-cong′ {f} {g} {x≡y} {fgx≡x} =
    subst (λ z → f (g z) ≡ z) x≡y fgx≡x                         ≡⟨ subst-in-terms-of-trans-and-cong ⟩
    trans (sym (cong (f ∘ g) x≡y)) (trans fgx≡x (cong id x≡y))  ≡⟨ sym $ cong₂ (λ p q → trans (sym p) (trans fgx≡x q)) (cong-∘ _ _ _) (cong-id _) ⟩∎
    trans (sym (cong f (cong g x≡y))) (trans fgx≡x x≡y)         ∎

-- The remainder of this module is not based on the HoTT book.

-- The interval can be expressed as a suspension.

Interval↔Susp-⊤ : Interval ↔ Susp ⊤
Interval↔Susp-⊤ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = elim λ where
        .northʳ      → refl _
        .southʳ      → refl _
        .meridianʳ _ →
           subst (λ x → to (from x) ≡ x) (meridian tt) (refl _)           ≡⟨ subst-in-terms-of-trans-and-cong′ ⟩

           trans (sym (cong to (cong from (meridian tt))))
                 (trans (refl _) (meridian tt))                           ≡⟨ cong₂ (λ p q → trans (sym (cong to p)) q)
                                                                               rec-meridian
                                                                               (trans-reflˡ _) ⟩
           trans (sym (cong to 0≡1)) (meridian tt)                        ≡⟨ cong (λ p → trans (sym p) (meridian tt)) $ Interval.rec-0≡1 _ _ _ ⟩

           trans (sym (meridian tt)) (meridian tt)                        ≡⟨ trans-symˡ _ ⟩∎

           refl _                                                         ∎
    }
  ; left-inverse-of = Interval.elim
      _
      (refl _)
      (refl _)
      (subst (λ x → from (to x) ≡ x) 0≡1 (refl _)                  ≡⟨ subst-in-terms-of-trans-and-cong′ ⟩
       trans (sym (cong from (cong to 0≡1))) (trans (refl _) 0≡1)  ≡⟨ cong₂ (λ p q → trans (sym (cong from p)) q)
                                                                        (Interval.rec-0≡1 _ _ _)
                                                                        (trans-reflˡ _) ⟩
       trans (sym (cong from (meridian tt))) 0≡1                   ≡⟨ cong (λ p → trans (sym p) 0≡1) rec-meridian ⟩
       trans (sym 0≡1) 0≡1                                         ≡⟨ trans-symˡ _ ⟩∎
       refl _                                                      ∎)
  }
  where
  to   = Interval.rec north south (meridian tt)
  from = rec λ where
    .northʳ      → [0]
    .southʳ      → [1]
    .meridianʳ _ → 0≡1

-- A map function.

map : (A → B) → Susp A → Susp B
map A→B = rec λ where
  .northʳ    → north
  .southʳ    → south
  .meridianʳ → meridian ∘ A→B

private opaque

  -- A helper function used to implement cong-↠ and cong-↔.

  map∘map :
    (∀ x → f (g x) ≡ x) →
    ∀ x → map f (map g x) ≡ x
  map∘map {f} {g} hyp = elim λ where
    .northʳ      → refl _
    .southʳ      → refl _
    .meridianʳ x →
       subst (λ x → map f (map g x) ≡ x) (meridian x) (refl _)   ≡⟨ subst-in-terms-of-trans-and-cong′ ⟩

       trans (sym $ cong (map f) $ cong (map g) (meridian x))
             (trans (refl _) (meridian x))                       ≡⟨ cong₂ (λ p q → trans (sym $ cong (map f) p) q)
                                                                      rec-meridian
                                                                      (trans-reflˡ _) ⟩

       trans (sym $ cong (map f) $ meridian (g x)) (meridian x)  ≡⟨ cong (λ p → trans (sym p) (meridian x)) rec-meridian ⟩

       trans (sym $ meridian (f (g x))) (meridian x)             ≡⟨ cong (λ y → trans (sym $ meridian y) (meridian x)) $ hyp x ⟩

       trans (sym $ meridian x) (meridian x)                     ≡⟨ trans-symˡ _ ⟩∎

       refl _                                                    ∎

-- Some preservation lemmas.

cong-⇔ : A ⇔ B → Susp A ⇔ Susp B
cong-⇔ A⇔B = record
  { to   = map (_⇔_.to   A⇔B)
  ; from = map (_⇔_.from A⇔B)
  }

cong-↠ : A ↠ B → Susp A ↠ Susp B
cong-↠ A↠B = record
  { logical-equivalence = cong-⇔ (_↠_.logical-equivalence A↠B)
  ; right-inverse-of    = map∘map (_↠_.right-inverse-of A↠B)
  }

cong-↔ : A ↔ B → Susp A ↔ Susp B
cong-↔ A↔B = record
  { surjection      = cong-↠ (_↔_.surjection A↔B)
  ; left-inverse-of = map∘map (_↔_.left-inverse-of A↔B)
  }

cong-≃ : A ≃ B → Susp A ≃ Susp B
cong-≃ = from-isomorphism ∘ cong-↔ ∘ from-isomorphism

private

  -- Lemmas used to implement ¬-cong-↣ and ¬-cong-Embedding.

  ⊥↣⊤ : ⊥ {ℓ = ℓ₁} ↣ ↑ ℓ₂ ⊤
  ⊥↣⊤ = record
    { to        = λ ()
    ; injective = λ {}
    }

  ¬Susp⊥↣Susp⊤ : ¬ (Susp (⊥ {ℓ = ℓ₁}) ↣ Susp (↑ ℓ₂ ⊤))
  ¬Susp⊥↣Susp⊤ =
    Susp ⊥ ↣ Susp (↑ _ ⊤)                                          ↝⟨ (λ f → from-isomorphism (cong-↔ Bijection.↑↔) F.∘ f F.∘
                                                                             from-isomorphism (cong-↔ ⊥↔⊥)) ⟩
    Susp ⊥₀ ↣ Susp ⊤                                               ↝⟨ (λ f → from-isomorphism (inverse Interval↔Susp-⊤) F.∘ f F.∘
                                                                             from-isomorphism Bool↔Susp-⊥) ⟩
    Bool ↣ Interval                                                ↝⟨ (λ inj → _↣_.to inj , _↣_.injective inj) ⟩
    (∃ λ (f : Bool → Interval) → f true ≡ f false → true ≡ false)  ↝⟨ Σ-map id (λ f → f (mono₁ 0 Interval.interval-contractible _ _)) ⟩
    (Bool → Interval) × true ≡ false                               ↝⟨ proj₂ ⟩
    true ≡ false                                                   ↝⟨ Bool.true≢false ⟩□
    ⊥                                                              □

-- Some negative preservation results.

¬-cong-↣ :
  ¬ (∀ {A : Type a} {B : Type b} → A ↣ B → Susp A ↣ Susp B)
¬-cong-↣ {a} {b} =
  (∀ {A B} → A ↣ B → Susp A ↣ Susp B)  ↝⟨ (λ hyp → hyp) ⟩
  (⊥ ↣ ↑ _ ⊤ → Susp ⊥ ↣ Susp (↑ _ ⊤))  ↝⟨ _$ ⊥↣⊤ ⟩
  Susp ⊥ ↣ Susp (↑ _ ⊤)                ↝⟨ ¬Susp⊥↣Susp⊤ ⟩□
  ⊥                                    □

¬-cong-Embedding :
  ¬ (∀ {A : Type a} {B : Type b} →
     Embedding A B → Embedding (Susp A) (Susp B))
¬-cong-Embedding =
  (∀ {A B} → Embedding A B → Embedding (Susp A) (Susp B))    ↝⟨ (λ hyp → hyp) ⟩
  (Embedding ⊥ (↑ _ ⊤) → Embedding (Susp ⊥) (Susp (↑ _ ⊤)))  ↝⟨ _$ Emb-⊥-⊤ ⟩
  Embedding (Susp ⊥) (Susp (↑ _ ⊤))                          ↝⟨ Embedding.injection ⟩
  Susp ⊥ ↣ Susp (↑ _ ⊤)                                      ↝⟨ ¬Susp⊥↣Susp⊤ ⟩□
  ⊥                                                          □
  where
  Emb-⊥-⊤ : Embedding ⊥ (↑ _ ⊤)
  Emb-⊥-⊤ =
    _↔_.to (Embedding.↣↔Embedding
              ext
              (mono₁ 1 ⊥-propositional)
              (mono (Nat.zero≤ 2) (↑-closure 0 ⊤-contractible)))
           ⊥↣⊤
