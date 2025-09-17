------------------------------------------------------------------------
-- Half adjoint equivalences
------------------------------------------------------------------------

-- This development is partly based on the presentation of half
-- adjoint equivalences in the HoTT book, and partly based on
-- Voevodsky's work on univalent foundations.

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Equivalence.Half-adjoint
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as B using (_↔_)
import Equivalence.Contractible-preimages eq as CP
import H-level eq as H-level
open import Preimage eq using (_⁻¹_)
open import Surjection eq using (_↠_)

private
  variable
    a b c p p₁ p₂ pℓ q : Level
    A B                : Type a
    P                  : A → Type p
    f g                : (x : A) → P x
    A↔B                : A ↔ B
    x                  : A

------------------------------------------------------------------------
-- The definition of Is-equivalence

mutual

  -- Is-equivalence f means that f is a half adjoint equivalence.

  Is-equivalence :
    {A : Type a} {B : Type b} →
    (A → B) → Type (a ⊔ b)
  Is-equivalence {A} {B} f =
    ∃ λ (f⁻¹ : B → A) → Proofs f f⁻¹

  -- The "proofs" contained in Is-equivalence f.

  Proofs :
    {A : Type a} {B : Type b} →
    (A → B) → (B → A) → Type (a ⊔ b)
  Proofs f f⁻¹ =
    ∃ λ (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
    ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
      ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x)

-- Some projections.

inverse :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  Is-equivalence f → B → A
inverse = proj₁₀

right-inverse-of :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  (eq : Is-equivalence f) →
  ∀ x → f (inverse eq x) ≡ x
right-inverse-of = proj₁₀ ∘ proj₂₀

left-inverse-of :
  {@0 A : Type a} {@0 B : Type b} {@0 f : A → B} →
  (eq : Is-equivalence f) →
  ∀ x → inverse eq (f x) ≡ x
left-inverse-of = proj₁₀ ∘ proj₂₀ ∘ proj₂₀

------------------------------------------------------------------------
-- Identity, inverse, composition

-- The identity function is an equivalence.

id-equivalence : Is-equivalence (id {A = A})
id-equivalence =
    id
  , refl
  , refl
  , (λ x →
       cong id (refl x)  ≡⟨ sym $ cong-id _ ⟩∎
       refl x            ∎)

-- If f is an equivalence, then its inverse is also an equivalence.

inverse-equivalence :
  (eq : Is-equivalence f) → Is-equivalence (inverse eq)
inverse-equivalence {f} (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
  f , f⁻¹-f , f-f⁻¹ , f⁻¹-f-f⁻¹
  where

  opaque

    f⁻¹-f-f⁻¹ : ∀ x → cong f⁻¹ (f-f⁻¹ x) ≡ f⁻¹-f (f⁻¹ x)
    f⁻¹-f-f⁻¹ x = subst
      (λ x → cong f⁻¹ (f-f⁻¹ x) ≡ f⁻¹-f (f⁻¹ x))
      (f-f⁻¹ x)
      (cong f⁻¹ (f-f⁻¹ (f (f⁻¹ x)))       ≡⟨ cong (cong f⁻¹) $ sym $ f-f⁻¹-f _ ⟩

       cong f⁻¹ (cong f (f⁻¹-f (f⁻¹ x)))  ≡⟨ cong-∘ f⁻¹ f _ ⟩

       cong (f⁻¹ ∘ f) (f⁻¹-f (f⁻¹ x))     ≡⟨ cong-≡id-≡-≡id f⁻¹-f ⟩∎

       f⁻¹-f (f⁻¹ (f (f⁻¹ x)))            ∎)

-- If f and g are inverses, then f ∘ g is an equivalence.

composition-equivalence :
  Is-equivalence f → Is-equivalence g → Is-equivalence (f ∘ g)
composition-equivalence
  {f} {g}
  (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f)
  (g⁻¹ , g-g⁻¹ , g⁻¹-g , g-g⁻¹-g) =
    [f-g]⁻¹
  , [f-g]-[f-g]⁻¹
  , [f-g]⁻¹-[f-g]
  , [f-g]-[f-g]⁻¹-[f-g]
  where
  [f-g] = f ∘ g

  [f-g]⁻¹ = g⁻¹ ∘ f⁻¹

  [f-g]-[f-g]⁻¹ = λ (@ω x) →
    f (g (g⁻¹ (f⁻¹ x)))  ≡⟨ cong f $ g-g⁻¹ _ ⟩
    f (f⁻¹ x)            ≡⟨ f-f⁻¹ _ ⟩∎
    x                    ∎

  [f-g]⁻¹-[f-g] = λ (@ω x) →
    g⁻¹ (f⁻¹ (f (g x)))  ≡⟨ cong g⁻¹ $ f⁻¹-f _ ⟩
    g⁻¹ (g x)            ≡⟨ g⁻¹-g _ ⟩∎
    x                    ∎

  opaque

    [f-g]-[f-g]⁻¹-[f-g] :
      ∀ x → cong [f-g] ([f-g]⁻¹-[f-g] x) ≡ [f-g]-[f-g]⁻¹ ([f-g] x)
    [f-g]-[f-g]⁻¹-[f-g] x =
      cong (f ∘ g) (trans (cong g⁻¹ (f⁻¹-f (g x))) (g⁻¹-g x))           ≡⟨ trans (sym $ cong-∘ _ _ _) $
                                                                           cong (cong _) $
                                                                           trans (cong-trans _ _ _) $
                                                                           cong (flip trans _) $
                                                                           cong-∘ _ _ _ ⟩
      cong f (trans (cong (g ∘ g⁻¹) (f⁻¹-f (g x))) (cong g (g⁻¹-g x)))  ≡⟨ cong (cong _) $ cong (trans _) $ g-g⁻¹-g _ ⟩
      cong f (trans (cong (g ∘ g⁻¹) (f⁻¹-f (g x))) (g-g⁻¹ (g x)))       ≡⟨ cong (cong f) $ naturality g-g⁻¹ ⟩
      cong f (trans (g-g⁻¹ (f⁻¹ (f (g x)))) (cong id (f⁻¹-f (g x))))    ≡⟨ cong (cong _) $ cong (trans _) $ sym $ cong-id _ ⟩
      cong f (trans (g-g⁻¹ (f⁻¹ (f (g x)))) (f⁻¹-f (g x)))              ≡⟨ cong-trans _ _ _ ⟩
      trans (cong f (g-g⁻¹ (f⁻¹ (f (g x))))) (cong f (f⁻¹-f (g x)))     ≡⟨ cong (trans _) $ f-f⁻¹-f _ ⟩∎
      trans (cong f (g-g⁻¹ (f⁻¹ (f (g x))))) (f-f⁻¹ (f (g x)))          ∎

------------------------------------------------------------------------
-- Conversions to and from bijections

-- Equivalences are bijections (functions with quasi-inverses).

Is-equivalence→↔ :
  {@0 A : Type a} {@0 B : Type b} {f : A → B} →
  Is-equivalence f → A ↔ B
Is-equivalence→↔ {f} (f⁻¹ , f-f⁻¹ , f⁻¹-f , _) = record
  { surjection = record
    { logical-equivalence = record
      { to   = f
      ; from = f⁻¹
      }
    ; right-inverse-of = f-f⁻¹
    }
  ; left-inverse-of = f⁻¹-f
  }

-- Functions with quasi-inverses are equivalences.
--
-- Note that the left inverse proof is preserved unchanged.

↔→Is-equivalenceˡ :
  (A↔B : A ↔ B) → Is-equivalence (_↔_.to A↔B)
↔→Is-equivalenceˡ A↔B =
    from
  , right-inverse-of′
  , A↔B.left-inverse-of
  , left-right
  where
  open module A↔B = _↔_ A↔B using (to; from)

  opaque

    right-inverse-of′ : ∀ x → to (from x) ≡ x
    right-inverse-of′ x =
      to (from x)              ≡⟨ sym (A↔B.right-inverse-of _) ⟩
      to (from (to (from x)))  ≡⟨ cong to (A↔B.left-inverse-of _) ⟩
      to (from x)              ≡⟨ A↔B.right-inverse-of _ ⟩∎
      x                        ∎

    left-right :
      ∀ x → cong to (A↔B.left-inverse-of x) ≡ right-inverse-of′ (to x)
    left-right x =
      let lemma =
            trans (A↔B.right-inverse-of _)
              (cong to (A↔B.left-inverse-of _))                         ≡⟨ cong (trans _) $
                                                                           cong-id _ ⟩
            trans (A↔B.right-inverse-of _)
              (cong id (cong to (A↔B.left-inverse-of _)))               ≡⟨ sym $ naturality A↔B.right-inverse-of ⟩

            trans (cong (to ∘ from) (cong to (A↔B.left-inverse-of _)))
              (A↔B.right-inverse-of _)                                  ≡⟨ cong (flip trans _) $
                                                                           cong-∘ _ _ _ ⟩
            trans (cong (to ∘ from ∘ to) (A↔B.left-inverse-of _))
              (A↔B.right-inverse-of _)                                  ≡⟨ cong (flip trans _) $ sym $
                                                                           cong-∘ _ _ _ ⟩
            trans (cong to (cong (from ∘ to) (A↔B.left-inverse-of _)))
              (A↔B.right-inverse-of _)                                  ≡⟨ cong (flip trans _ ∘ cong to) $
                                                                           cong-≡id-≡-≡id A↔B.left-inverse-of ⟩∎
            trans (cong to (A↔B.left-inverse-of _))
              (A↔B.right-inverse-of _)                                  ∎
      in
      cong to (A↔B.left-inverse-of x)             ≡⟨ sym $ trans-sym-[trans] _ _ ⟩

      trans (sym (A↔B.right-inverse-of _))
        (trans (A↔B.right-inverse-of _)
           (cong to (A↔B.left-inverse-of _)))     ≡⟨ cong (trans _) lemma ⟩∎

      trans (sym (A↔B.right-inverse-of _))
        (trans (cong to (A↔B.left-inverse-of _))
           (A↔B.right-inverse-of _))              ∎

_ : proj₁ (↔→Is-equivalenceˡ A↔B) ≡ _↔_.from A↔B
_ = refl _

_ :
  proj₁ (proj₂ (proj₂ (↔→Is-equivalenceˡ A↔B))) ≡
  _↔_.left-inverse-of A↔B
_ = refl _

-- Functions with quasi-inverses are equivalences.
--
-- Note that the right inverse proof is preserved unchanged.

↔→Is-equivalenceʳ :
  (A↔B : A ↔ B) → Is-equivalence (_↔_.to A↔B)
↔→Is-equivalenceʳ =
  inverse-equivalence ∘
  ↔→Is-equivalenceˡ ∘
  B.inverse

_ : proj₁ (↔→Is-equivalenceʳ A↔B) ≡ _↔_.from A↔B
_ = refl _

_ : proj₁ (proj₂ (↔→Is-equivalenceʳ A↔B)) ≡ _↔_.right-inverse-of A↔B
_ = refl _

------------------------------------------------------------------------
-- Is-equivalence is related to CP.Is-equivalence

-- Is-equivalence f and CP.Is-equivalence f are logically equivalent.
--
-- See also Function-universe.Is-equivalence≃Is-equivalence-CP.

Is-equivalence⇔Is-equivalence-CP :
  Is-equivalence f ⇔ CP.Is-equivalence f
Is-equivalence⇔Is-equivalence-CP = record
  { to   = to
  ; from = from
  }
  where
  to : Is-equivalence f → CP.Is-equivalence f
  to {f} (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) y =
      (f⁻¹ y , f-f⁻¹ y)
    , λ (x , f-f⁻¹′) →
      Σ-≡,≡→≡
        (f⁻¹ y      ≡⟨ sym $ cong f⁻¹ f-f⁻¹′ ⟩
         f⁻¹ (f x)  ≡⟨ f⁻¹-f x ⟩∎
         x          ∎)
        (elim¹
           (λ {y} f-f⁻¹′ →
              subst (λ x → f x ≡ y)
                (trans (sym (cong f⁻¹ f-f⁻¹′)) (f⁻¹-f x))
                (f-f⁻¹ y) ≡
              f-f⁻¹′)
           (subst (λ x′ → f x′ ≡ f x)
              (trans (sym (cong f⁻¹ (refl _))) (f⁻¹-f x))
              (f-f⁻¹ (f x))                                    ≡⟨ cong (flip (subst _) _) $
                                                                  trans (cong (flip trans _) $
                                                                         trans (cong sym $ cong-refl _) $
                                                                         sym-refl) $
                                                                  trans-reflˡ _ ⟩

            subst (λ x′ → f x′ ≡ f x) (f⁻¹-f x) (f-f⁻¹ (f x))  ≡⟨ subst-∘ _ _ _ ⟩

            subst (_≡ f x) (cong f (f⁻¹-f x)) (f-f⁻¹ (f x))    ≡⟨ subst-trans-sym ⟩

            trans (sym (cong f (f⁻¹-f x))) (f-f⁻¹ (f x))       ≡⟨ cong (flip trans _ ∘ sym) $
                                                                  f-f⁻¹-f _ ⟩

            trans (sym (f-f⁻¹ (f x))) (f-f⁻¹ (f x))            ≡⟨ trans-symˡ _ ⟩∎

            refl _                                             ∎)
           f-f⁻¹′)

  from : CP.Is-equivalence f → Is-equivalence f
  from eq =
      CP.inverse eq
    , CP.right-inverse-of eq
    , CP.left-inverse-of eq
    , CP.left-right-lemma eq

-- All fibres of an equivalence over a given point are equal to a
-- given fibre.

irrelevance :
  (eq : Is-equivalence f) →
  ∀ y (p : f ⁻¹ y) → (inverse eq y , right-inverse-of eq y) ≡ p
irrelevance =
  CP.irrelevance ∘
  _⇔_.to Is-equivalence⇔Is-equivalence-CP

-- When proving that a function is an equivalence one can assume that
-- the codomain is inhabited.

[inhabited→Is-equivalence]→Is-equivalence :
  {f : A → B} →
  (B → Is-equivalence f) → Is-equivalence f
[inhabited→Is-equivalence]→Is-equivalence hyp =
  _⇔_.from Is-equivalence⇔Is-equivalence-CP $ λ x →
  _⇔_.to Is-equivalence⇔Is-equivalence-CP (hyp x) x

------------------------------------------------------------------------
-- Some lemmas

-- Is-equivalence respects extensional equality.

respects-extensional-equality :
  (∀ x → f x ≡ g x) →
  Is-equivalence f → Is-equivalence g
respects-extensional-equality
  {f} {g} f≡g (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
  ↔→Is-equivalenceʳ (record
    { surjection = record
      { logical-equivalence = record
        { to   = g
        ; from = f⁻¹
        }
      ; right-inverse-of = λ x →
          g (f⁻¹ x)  ≡⟨ sym $ f≡g _ ⟩
          f (f⁻¹ x)  ≡⟨ f-f⁻¹ _ ⟩∎
          x          ∎
      }
    ; left-inverse-of = λ x →
        f⁻¹ (g x)  ≡⟨ cong f⁻¹ $ sym $ f≡g _ ⟩
        f⁻¹ (f x)  ≡⟨ f⁻¹-f _ ⟩∎
        x          ∎
    })

-- Functions between contractible types are equivalences.

function-between-contractible-types-is-equivalence :
  ∀ {a b} {A : Type a} {B : Type b} (f : A → B) →
  Contractible A → Contractible B → Is-equivalence f
function-between-contractible-types-is-equivalence f A-contr B-contr =
  ↔→Is-equivalenceˡ (record
    { surjection = record
      { logical-equivalence = record
        { from = λ _ → proj₁ A-contr
        }
      ; right-inverse-of = λ x →
          f (proj₁ A-contr)  ≡⟨ sym $ proj₂ B-contr _ ⟩
          proj₁ B-contr      ≡⟨ proj₂ B-contr _ ⟩∎
          x                  ∎
      }
    ; left-inverse-of = proj₂ A-contr
    })

opaque

  -- If Σ-map id f is an equivalence, then f is also an equivalence.

  drop-Σ-map-id :
    {A : Type a} {P : A → Type p} {Q : A → Type q}
    (f : ∀ {x} → P x → Q x) →
    Is-equivalence {A = Σ A P} {B = Σ A Q} (Σ-map id f) →
    ∀ x → Is-equivalence (f {x = x})
  drop-Σ-map-id f eq x =
    _⇔_.from Is-equivalence⇔Is-equivalence-CP $
    CP.drop-Σ-map-id f
      (_⇔_.to Is-equivalence⇔Is-equivalence-CP eq)
      x

  -- A "computation" rule for drop-Σ-map-id.

  inverse-drop-Σ-map-id :
    {A : Type a} {P : A → Type p} {Q : A → Type q}
    {f : ∀ {x} → P x → Q x} {x : A} {y : Q x}
    {eq : Is-equivalence {A = Σ A P} {B = Σ A Q} (Σ-map id f)} →
    inverse (drop-Σ-map-id f eq x) y ≡
    subst P (cong proj₁ (right-inverse-of eq (x , y)))
      (proj₂ (inverse eq (x , y)))
  inverse-drop-Σ-map-id = CP.inverse-drop-Σ-map-id
