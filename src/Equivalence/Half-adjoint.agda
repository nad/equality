------------------------------------------------------------------------
-- Half adjoint equivalences
------------------------------------------------------------------------

-- This development is partly based on the presentation of half
-- adjoint equivalences in the HoTT book, and partly based on
-- Voevodsky's work on univalent foundations.

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Half-adjoint
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq as B using (_↔_)
import Equivalence.Contractible-preimages eq as CP
open import H-level eq as H-level
open import H-level.Closure eq
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq as S hiding (id; _∘_)

private
  variable
    a b p q : Level
    A B C   : Type a
    P       : A → Type p
    Q       : (x : A) → P x → Type q
    f g     : A → B
    A↔B     : A ↔ B

------------------------------------------------------------------------
-- The definition of Is-equivalence

mutual

  -- Is-equivalence f means that f is a half adjoint equivalence.

  Is-equivalence :
    {A : Type a} {B : Type b} →
    (A → B) → Type (a ⊔ b)
  Is-equivalence {A = A} {B = B} f =
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

inverse : {f : A → B} → Is-equivalence f → B → A
inverse = proj₁

right-inverse-of :
  {f : A → B} →
  (eq : Is-equivalence f) →
  ∀ x → f (inverse eq x) ≡ x
right-inverse-of = proj₁ ∘ proj₂

left-inverse-of :
  {f : A → B} →
  (eq : Is-equivalence f) →
  ∀ x → inverse eq (f x) ≡ x
left-inverse-of = proj₁ ∘ proj₂ ∘ proj₂

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
inverse-equivalence {f = f} (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
  f , f⁻¹-f , f-f⁻¹ , f⁻¹-f-f⁻¹
  where

  abstract

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
  {f = f} {g = g}
  (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f)
  (g⁻¹ , g-g⁻¹ , g⁻¹-g , g-g⁻¹-g) =
    [f-g]⁻¹
  , [f-g]-[f-g]⁻¹
  , [f-g]⁻¹-[f-g]
  , [f-g]-[f-g]⁻¹-[f-g]
  where
  [f-g] = f ∘ g

  [f-g]⁻¹ = g⁻¹ ∘ f⁻¹

  [f-g]-[f-g]⁻¹ = λ x →
    f (g (g⁻¹ (f⁻¹ x)))  ≡⟨ cong f $ g-g⁻¹ _ ⟩
    f (f⁻¹ x)            ≡⟨ f-f⁻¹ _ ⟩∎
    x                    ∎

  [f-g]⁻¹-[f-g] = λ x →
    g⁻¹ (f⁻¹ (f (g x)))  ≡⟨ cong g⁻¹ $ f⁻¹-f _ ⟩
    g⁻¹ (g x)            ≡⟨ g⁻¹-g _ ⟩∎
    x                    ∎

  abstract

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
  {f : A → B} → Is-equivalence f → A ↔ B
Is-equivalence→↔ {f = f} (f⁻¹ , f-f⁻¹ , f⁻¹-f , _) = record
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

  abstract

    right-inverse-of′ : ∀ x → to (from x) ≡ x
    right-inverse-of′ x =
      to (from x)              ≡⟨ sym (A↔B.right-inverse-of _) ⟩
      to (from (to (from x)))  ≡⟨ cong to (A↔B.left-inverse-of _) ⟩
      to (from x)              ≡⟨ A↔B.right-inverse-of _ ⟩∎
      x                        ∎

    left-right :
      ∀ x → cong to (A↔B.left-inverse-of x) ≡ right-inverse-of′ (to x)
    left-right x =
      cong to (A↔B.left-inverse-of x)             ≡⟨ sym $ trans-sym-[trans] _ _ ⟩

      trans (sym (A↔B.right-inverse-of _))
        (trans (A↔B.right-inverse-of _)
           (cong to (A↔B.left-inverse-of _)))     ≡⟨ cong (trans _) lemma ⟩∎

      trans (sym (A↔B.right-inverse-of _))
        (trans (cong to (A↔B.left-inverse-of _))
           (A↔B.right-inverse-of _))              ∎
      where
      lemma =
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
-- Is-equivalence is related to CP.Is-equivalence (part one)

-- Is-equivalence f and CP.Is-equivalence f are logically equivalent.

Is-equivalence⇔Is-equivalence-CP :
  Is-equivalence f ⇔ CP.Is-equivalence f
Is-equivalence⇔Is-equivalence-CP = record
  { to   = to
  ; from = from
  }
  where
  to : Is-equivalence f → CP.Is-equivalence f
  to {f = f} (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) y =
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
-- The "inverse of extensionality" is an equivalence (assuming
-- extensionality)

-- Is-equivalence respects extensional equality.

respects-extensional-equality :
  (∀ x → f x ≡ g x) →
  Is-equivalence f → Is-equivalence g
respects-extensional-equality
  {f = f} {g = g} f≡g (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
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

abstract

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

  -- The function ext⁻¹ is an equivalence (assuming extensionality).

  ext⁻¹-is-equivalence :
    ({P : A → Type b} → Extensionality′ A P) →
    {P : A → Type b} {f g : (x : A) → P x} →
    Is-equivalence (ext⁻¹ {f = f} {g = g})
  ext⁻¹-is-equivalence {A = A} ext {P = P} {f = f} {g = g} =
    drop-Σ-map-id ext⁻¹ lemma₂ f
    where
    surj :
      (∀ x → Singleton (g x)) ↠
      (∃ λ (f : (x : A) → P x) → ∀ x → f x ≡ g x)
    surj = record
      { logical-equivalence = record
        { to   = λ f → proj₁ ∘ f , proj₂ ∘ f
        ; from = λ p x → proj₁ p x , proj₂ p x
        }
      ; right-inverse-of = refl
      }

    lemma₁ : Contractible (∃ λ (f : (x : A) → P x) → ∀ x → f x ≡ g x)
    lemma₁ =
      H-level.respects-surjection surj 0 $
        _⇔_.from Π-closure-contractible⇔extensionality
          ext (singleton-contractible ∘ g)

    lemma₂ :
      Is-equivalence
        {A = ∃ λ f → f ≡ g}
        {B = ∃ λ f → ∀ x → f x ≡ g x}
        (Σ-map id ext⁻¹)
    lemma₂ = function-between-contractible-types-is-equivalence
               _ (singleton-contractible g) lemma₁

------------------------------------------------------------------------
-- Results related to h-levels

abstract

  -- Is-equivalence f is a proposition (assuming extensionality).

  propositional :
    {A : Type a} {B : Type b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (f : A → B) → Is-proposition (Is-equivalence f)
  propositional {a = a} {b = b} {A = A} {B = B} ext f =
    [inhabited⇒+]⇒+ 0 λ eq →
    mono₁ 0 $
    H-level.respects-surjection
      ((∃ λ ((f⁻¹ , f-f⁻¹) : ∃ λ f⁻¹ → ∀ x → f (f⁻¹ x) ≡ x) →
        ∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
            ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))              ↠⟨ _↔_.surjection $ B.inverse B.Σ-assoc ⟩□

       Is-equivalence f                                        □)
      0 $
    Σ-closure 0 (lemma₁ eq) (uncurry $ lemma₂ eq)
    where
    ext₁ : Extensionality b b
    ext₁ = lower-extensionality a a ext

    ext₁′ : Extensionality b a
    ext₁′ = lower-extensionality a b ext

    ext-↠ :
      {A B : Type b} {f g : A → B} →
      f ≡ g ↠ (∀ x → f x ≡ g x)
    ext-↠ =
      _↔_.surjection $
      Is-equivalence→↔ $
      ext⁻¹-is-equivalence (apply-ext ext₁)

    lemma₁ :
      Is-equivalence f →
      Contractible (∃ λ (f⁻¹ : B → A) → ∀ x → f (f⁻¹ x) ≡ x)
    lemma₁ (f⁻¹ , f-f⁻¹ , f⁻¹-f , f-f⁻¹-f) =
      H-level.respects-surjection
        ((∃ λ f⁻¹ → f ∘ f⁻¹ ≡ id)         ↠⟨ (∃-cong λ _ → ext-↠) ⟩□
         (∃ λ f⁻¹ → ∀ x → f (f⁻¹ x) ≡ x)  □)
        0 $
      Preimage.bijection⁻¹-contractible
        (record
           { surjection = record
             { logical-equivalence = record
               { to   = f   ∘_
               ; from = f⁻¹ ∘_
               }
             ; right-inverse-of = λ g → apply-ext ext₁ λ x →
                 f (f⁻¹ (g x))  ≡⟨ f-f⁻¹ (g x) ⟩∎
                 g x            ∎
             }
           ; left-inverse-of = λ g → apply-ext ext₁′ λ x →
               f⁻¹ (f (g x))  ≡⟨ f⁻¹-f (g x) ⟩∎
               g x            ∎
           })
        id

    ext₂ : Extensionality a (a ⊔ b)
    ext₂ = lower-extensionality b lzero ext

    lemma₂ :
      Is-equivalence f →
      (f⁻¹ : B → A) (f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x) →
      Contractible
        (∃ λ (f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x) →
           ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))
    lemma₂ eq f⁻¹ f-f⁻¹ =
      H-level.respects-surjection
        ((∀ x → (f⁻¹ (f x) , f-f⁻¹ (f x)) ≡ (x , refl (f x)))             ↠⟨ (∀-cong ext₂ λ _ → _↔_.surjection $ B.inverse B.Σ-≡,≡↔≡) ⟩

         (∀ x → ∃ λ f⁻¹-f →
                  subst (λ y → f y ≡ f x) f⁻¹-f (f-f⁻¹ (f x)) ≡
                  refl (f x))                                             ↠⟨ (∀-cong ext₂ λ x → ∃-cong λ f⁻¹-f →
                                                                              elim (λ {A B} _ → A ↠ B) (λ _ → S.id) (

             subst (λ y → f y ≡ f x) f⁻¹-f (f-f⁻¹ (f x)) ≡ refl (f x)           ≡⟨ cong (_≡ _) $ subst-∘ _ _ _ ⟩
             subst (_≡ f x) (cong f f⁻¹-f) (f-f⁻¹ (f x)) ≡ refl (f x)           ≡⟨ cong (_≡ _) subst-trans-sym ⟩
             trans (sym (cong f f⁻¹-f)) (f-f⁻¹ (f x)) ≡ refl (f x)              ≡⟨ [trans≡]≡[≡trans-symˡ] _ _ _ ⟩
             f-f⁻¹ (f x) ≡ trans (sym (sym (cong f f⁻¹-f))) (refl (f x))        ≡⟨ cong (_ ≡_) $ trans-reflʳ _ ⟩
             f-f⁻¹ (f x) ≡ sym (sym (cong f f⁻¹-f))                             ≡⟨ cong (_ ≡_) $ sym-sym _ ⟩∎
             f-f⁻¹ (f x) ≡ cong f f⁻¹-f                                         ∎)) ⟩

         (∀ x → ∃ λ f⁻¹-f → f-f⁻¹ (f x) ≡ cong f f⁻¹-f)                   ↠⟨ (∀-cong ext₂ λ _ → ∃-cong λ _ →
                                                                              _↔_.surjection B.≡-comm) ⟩

         (∀ x → ∃ λ f⁻¹-f → cong f f⁻¹-f ≡ f-f⁻¹ (f x))                   ↠⟨ _↔_.surjection B.ΠΣ-comm ⟩□

         (∃ λ f⁻¹-f → ∀ x → cong f (f⁻¹-f x) ≡ f-f⁻¹ (f x))               □)
        0 $
      Π-closure ext₂ 0 λ x →
      H-level.⇒≡ 0 $
      _⇔_.to Is-equivalence⇔Is-equivalence-CP eq (f x)

-- If the domain of f is contractible and the codomain is
-- propositional, then Is-equivalence f is contractible (assuming
-- extensionality).

sometimes-contractible :
  Extensionality (a ⊔ b) (a ⊔ b) →
  {A : Type a} {B : Type b} {f : A → B} →
  Contractible A → Is-proposition B →
  Contractible (Is-equivalence f)
sometimes-contractible {a = a} {b = b} ext A-contr B-prop =
  Σ-closure 0 (Π-closure ext-b-a 0 λ _ → A-contr)              λ _ →
  Σ-closure 0 (Π-closure ext-b-b 0 λ _ → H-level.+⇒≡ B-prop)   λ _ →
  Σ-closure 0 (Π-closure ext-a-a 0 λ _ → H-level.⇒≡ 0 A-contr) λ _ →
  Π-closure ext-a-b 0 λ _ → H-level.⇒≡ 0 $ H-level.+⇒≡ B-prop
  where
  ext-a-a : Extensionality a a
  ext-a-a = lower-extensionality b b ext

  ext-a-b : Extensionality a b
  ext-a-b = lower-extensionality b a ext

  ext-b-a : Extensionality b a
  ext-b-a = lower-extensionality a b ext

  ext-b-b : Extensionality b b
  ext-b-b = lower-extensionality a a ext

------------------------------------------------------------------------
-- Is-equivalence is related to CP.Is-equivalence (part two)

-- Is-equivalence f and CP.Is-equivalence f are isomorphic (assuming
-- extensionality).

Is-equivalence↔Is-equivalence-CP :
  {A : Type a} {B : Type b} {f : A → B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  Is-equivalence f ↔ CP.Is-equivalence f
Is-equivalence↔Is-equivalence-CP ext = record
  { surjection = record
    { logical-equivalence = Is-equivalence⇔Is-equivalence-CP
    ; right-inverse-of    = λ _ → CP.propositional ext _ _ _
    }
  ; left-inverse-of = λ _ → propositional ext _ _ _
  }
