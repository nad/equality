------------------------------------------------------------------------
-- Equivalences with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Equality

module Equivalence.Erased
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open Derived-definitions-and-properties eq
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id) renaming (_∘_ to _⊚_)

open import Bijection eq using (_↔_)
open import Equivalence eq as Eq using (_≃_; Is-equivalence)
open import Erased.Level-1 eq as Erased
open import Function-universe eq as F hiding (id; _∘_; inverse)
open import H-level eq as H-level
open import H-level.Closure eq
open import Preimage eq as Preimage using (_⁻¹_)
open import Surjection eq as Surjection using (_↠_; Split-surjective)

private
  variable
    a b d ℓ q  : Level
    A B C      : Set a
    k k′ p x y : A
    P Q        : A → Set p
    f g        : (x : A) → P x

------------------------------------------------------------------------
-- Some basic stuff

open import Equivalence.Erased.Basics eq public

private
  variable
    A≃B : A ≃ᴱ B

------------------------------------------------------------------------
-- More conversion lemmas

-- In an erased context _⁻¹_ and _⁻¹ᴱ_ are pointwise equivalent.

@0 ⁻¹≃⁻¹ᴱ : f ⁻¹ y ≃ f ⁻¹ᴱ y
⁻¹≃⁻¹ᴱ {f = f} {y = y} =
  (∃ λ x → f x ≡ y)           Eq.≃⟨ (Eq.Σ-preserves Eq.id λ _ → Eq.inverse $ Eq.↔⇒≃ $ erased Erased↔) ⟩□
  (∃ λ x → Erased (f x ≡ y))  □

-- In an erased context Contractible and Contractibleᴱ are pointwise
-- equivalent.

@0 Contractible≃Contractibleᴱ :
  Contractible A ≃ Contractibleᴱ A
Contractible≃Contractibleᴱ =
  (∃ λ x → ∀ y → x ≡ y)           Eq.≃⟨ (Eq.Σ-preserves Eq.id λ _ → Eq.inverse $ Eq.↔⇒≃ $ erased Erased↔) ⟩□
  (∃ λ x → Erased (∀ y → x ≡ y))  □

-- In an erased context Is-equivalence and Is-equivalenceᴱ are
-- pointwise equivalent (assuming extensionality).

@0 Is-equivalence≃Is-equivalenceᴱ :
  {A : Set a} {B : Set b} {f : A → B} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  Is-equivalence f ↝[ k ] Is-equivalenceᴱ f
Is-equivalence≃Is-equivalenceᴱ {a = a} {k = k} {f = f} ext =
  (∀ y → Contractible (f ⁻¹ y))    ↝⟨ (∀-cong ext′ λ _ → H-level-cong ext 0 ⁻¹≃⁻¹ᴱ) ⟩
  (∀ y → Contractible (f ⁻¹ᴱ y))   ↝⟨ (∀-cong ext′ λ _ → from-isomorphism Contractible≃Contractibleᴱ) ⟩□
  (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  □
  where
  ext′ = lower-extensionality? k a lzero ext

-- In an erased context _≃_ and _≃ᴱ_ are pointwise equivalent
-- (assuming extensionality).

@0 ≃≃≃ᴱ :
  {A : Set a} {B : Set b} →
  Extensionality? k (a ⊔ b) (a ⊔ b) →
  (A ≃ B) ↝[ k ] (A ≃ᴱ B)
≃≃≃ᴱ {A = A} {B = B} ext =
  A ≃ B                        ↔⟨ Eq.↔⇒≃ Eq.≃-as-Σ ⟩
  (∃ λ f → Is-equivalence f)   ↝⟨ (∃-cong λ _ → Is-equivalence≃Is-equivalenceᴱ ext) ⟩
  (∃ λ f → Is-equivalenceᴱ f)  ↔⟨ Eq.inverse ≃ᴱ-as-Σ ⟩□
  A ≃ᴱ B                       □

-- A half adjoint equivalence with erased proofs can be turned into an
-- equivalence with erased proofs.

≃ᴱ→≃ᴱ :
  (f : A → B) (g : B → A)
  (@0 f∘g : ∀ x → f (g x) ≡ x)
  (@0 g∘f : ∀ x → g (f x) ≡ x) →
  @0 (∀ x → cong f (g∘f x) ≡ f∘g (f x)) →
  A ≃ᴱ B
≃ᴱ→≃ᴱ {A = A} {B = B} f g f∘g g∘f coh =
  ⟨ f
  , (λ y → (g y , [ f∘g y ])
         , [ (λ (x , eq) →
                let lemma =
                      sym (cong f (trans (cong g (sym (erased eq)))
                                     (g∘f x)))                        ≡⟨ cong sym $
                                                                         cong-trans _ _ _ ⟩
                      sym (trans (cong f (cong g (sym (erased eq))))
                             (cong f (g∘f x)))                        ≡⟨ cong₂ (λ p q → sym (trans p q))
                                                                           (cong-∘ _ _ _)
                                                                           (coh _) ⟩
                      sym (trans (cong (f ⊚ g) (sym (erased eq)))
                             (f∘g (f x)))                             ≡⟨ sym-trans _ _ ⟩

                      trans (sym (f∘g (f x)))
                        (sym (cong (f ⊚ g) (sym (erased eq))))        ≡⟨ cong (trans _) $ sym $
                                                                         cong-sym _ _ ⟩
                      trans (sym (f∘g (f x)))
                        (cong (f ⊚ g) (sym (sym (erased eq))))        ≡⟨ cong (λ eq → trans (sym (f∘g (f x))) (cong (f ⊚ g) eq)) $
                                                                         sym-sym _ ⟩∎
                      trans (sym (f∘g (f x)))
                        (cong (f ⊚ g) (erased eq))                    ∎
                in
                Σ-≡,≡→≡
                  (g y      ≡⟨ cong g (sym (erased eq)) ⟩
                   g (f x)  ≡⟨ g∘f x ⟩∎
                   x        ∎)
                  (subst (λ x → Erased (f x ≡ y))
                     (trans (cong g (sym (erased eq))) (g∘f x))
                     [ f∘g y ]                                         ≡⟨ Erased.[]-cong₃.push-subst-[]
                                                                            erased-instance-of-[]-cong-axiomatisation ⟩
                   [ subst (λ x → f x ≡ y)
                       (trans (cong g (sym (erased eq))) (g∘f x))
                       (f∘g y)
                   ]                                                   ≡⟨ cong [_]→ $ subst-∘ _ _ _ ⟩

                   [ subst (_≡ y)
                       (cong f
                          (trans (cong g (sym (erased eq))) (g∘f x)))
                       (f∘g y)
                   ]                                                   ≡⟨ cong (λ eq → [ subst (_≡ y) eq (f∘g y) ]) $ sym $
                                                                          sym-sym _ ⟩
                   [ subst (_≡ y)
                       (sym (sym (cong f
                                    (trans (cong g (sym (erased eq)))
                                       (g∘f x)))))
                       (f∘g y)
                   ]                                                   ≡⟨ cong [_]→ $ subst-trans _ ⟩

                   [ trans
                       (sym (cong f
                               (trans (cong g (sym (erased eq)))
                                  (g∘f x))))
                       (f∘g y)
                   ]                                                   ≡⟨ cong (λ eq → [ trans eq (f∘g y) ]) lemma ⟩

                   [ trans (trans (sym (f∘g (f x)))
                              (cong (f ⊚ g) (erased eq)))
                       (f∘g y)
                   ]                                                   ≡⟨ cong [_]→ $
                                                                          elim₁
                                                                            (λ eq → trans (trans _ (cong (f ⊚ g) eq)) _ ≡ eq)
                                                                            (
                       trans (trans (sym (f∘g y))
                                (cong (f ⊚ g) (refl _)))
                         (f∘g y)                                             ≡⟨ cong (λ eq → trans (trans _ eq) _) $ cong-refl _ ⟩

                       trans (trans (sym (f∘g y)) (refl _)) (f∘g y)          ≡⟨ cong (λ eq → trans eq _) $ trans-reflʳ _ ⟩

                       trans (sym (f∘g y)) (f∘g y)                           ≡⟨ trans-symˡ _ ⟩∎

                       refl _                                                ∎)
                                                                            (erased eq) ⟩
                   [ erased eq ]                                       ≡⟨⟩

                   eq                                                  ∎))
           ])
  ⟩

-- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.

Erased-⁻¹ᴱ↔Erased-⁻¹ :
  {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} {@0 y : B} →
  Erased (f ⁻¹ᴱ y) ↔ Erased (f ⁻¹ y)
Erased-⁻¹ᴱ↔Erased-⁻¹ {f = f} {y = y} =
  Erased (∃ λ x → Erased (f x ≡ y))             ↝⟨ Erased-Σ↔Σ ⟩
  (∃ λ x → Erased (Erased (f (erased x) ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
  (∃ λ x → Erased (f (erased x) ≡ y))           ↝⟨ F.inverse Erased-Σ↔Σ ⟩□
  Erased (∃ λ x → f x ≡ y)                      □

-- An isomorphism relating Contractibleᴱ to Contractible.

Erased-Contractibleᴱ↔Erased-Contractible :
  {@0 A : Set a} →
  Erased (Contractibleᴱ A) ↔ Erased (Contractible A)
Erased-Contractibleᴱ↔Erased-Contractible =
  Erased (∃ λ x → Erased (∀ y → x ≡ y))           ↝⟨ Erased-Σ↔Σ ⟩
  (∃ λ x → Erased (Erased (∀ y → erased x ≡ y)))  ↝⟨ (∃-cong λ _ → Erased-Erased↔Erased) ⟩
  (∃ λ x → Erased (∀ y → erased x ≡ y))           ↝⟨ F.inverse Erased-Σ↔Σ ⟩□
  Erased (∃ λ x → ∀ y → x ≡ y)                    □

------------------------------------------------------------------------
-- Some lemmas

-- A preservation lemma related to Σ.
--
-- Note that the argument called f∘g is not marked as erased. The from
-- argument of [≃]→≃ᴱ (which Agda can infer in this case, at least at
-- the time of writing) is included explicitly to show where f∘g is
-- used in a (potentially) non-erased context.
--
-- Presumably more lemmas of this kind could be proved (for instance a
-- variant for Π), but so far I have not found any use for them.
--
-- See also Σ-cong-≃ᴱ-Erased and Σ-cong-contra-≃ᴱ-Erased below.

Σ-cong-≃ᴱ :
  (f : A → B) (g : B → A)
  (f∘g : ∀ x → f (g x) ≡ x) →
  @0 (∀ y (p : f ⁻¹ y) → (g y , f∘g y) ≡ p) →
  (∀ x → P x ≃ᴱ Q (f x)) →
  Σ A P ≃ᴱ Σ B Q
Σ-cong-≃ᴱ {Q = Q} f g f∘g irr P≃Q =
  [≃]→≃ᴱ
    {from = λ p → g (proj₁ p)
                , _≃ᴱ_.from (P≃Q (g (proj₁ p)))
                    (subst Q (sym (f∘g (proj₁ p))) (proj₂ p))}
    ([proofs] (Σ-cong
                 Eq.⟨ f , (λ y → (g y , f∘g y) , irr y) ⟩
                 (≃ᴱ→≃ ⊚ P≃Q)))

-- In an erased context two equivalences are equal if the underlying
-- functions are equal (assuming extensionality).
--
-- See also to≡to→≡-Erased below.

@0 to≡to→≡ :
  {A : Set a} {B : Set b} {p q : A ≃ᴱ B} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  _≃ᴱ_.to p ≡ _≃ᴱ_.to q → p ≡ q
to≡to→≡ ext p≡q =
  _≃_.to (Eq.≃-≡ (Eq.inverse $ ≃≃≃ᴱ ext))
    (Eq.lift-equality ext p≡q)

-- If f is a half adjoint equivalence with certain erased proofs, then
-- x ≡ y is equivalent (with erased proofs) to f x ≡ f y.
--
-- (Perhaps it is possible to prove a similar lemma which returns a
-- half adjoint equivalence where the "left-inverse-of" part is not
-- erased.)
--
-- See also to≡to≃ᴱ≡-Erased below.

≡≃ᴱto≡to :
  (f : A → B) (g : B → A)
  (@0 f∘g : ∀ y → f (g y) ≡ y)
  (g∘f : ∀ x → g (f x) ≡ x) →
  @0 (∀ x → cong f (g∘f x) ≡ f∘g (f x)) →
  (x ≡ y) ≃ᴱ (f x ≡ f y)
≡≃ᴱto≡to {x = x} {y = y} f g f∘g g∘f coh = ↔→≃ᴱ
  (_↠_.from ≡↠≡)
  (_↠_.to   ≡↠≡)
  (λ eq →
     _↠_.from ≡↠≡ (_↠_.to ≡↠≡ eq)                              ≡⟨⟩

     cong f (trans (sym (g∘f x)) (trans (cong g eq) (g∘f y)))  ≡⟨ cong-trans _ _ _ ⟩

     trans (cong f (sym (g∘f x)))
       (cong f (trans (cong g eq) (g∘f y)))                    ≡⟨ cong₂ trans
                                                                    (cong-sym _ _)
                                                                    (cong-trans _ _ _) ⟩
     trans (sym (cong f (g∘f x)))
       (trans (cong f (cong g eq)) (cong f (g∘f y)))           ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong f (cong g eq)) q))
                                                                    (coh _)
                                                                    (coh _) ⟩
     trans (sym (f∘g (f x)))
       (trans (cong f (cong g eq)) (f∘g (f y)))                ≡⟨⟩

     _↠_.to ≡↠≡′ (_↠_.from ≡↠≡′ eq)                            ≡⟨ _↠_.right-inverse-of ≡↠≡′ eq ⟩∎

     eq                                                        ∎)
  (_↠_.right-inverse-of ≡↠≡)
  where
  ≡↠≡ : (f x ≡ f y) ↠ (x ≡ y)
  ≡↠≡ = Surjection.↠-≡ (record
    { logical-equivalence = record
      { to   = g
      ; from = f
      }
    ; right-inverse-of = g∘f
    })

  @0 ≡↠≡′ : ∀ {x y} → (g x ≡ g y) ↠ (x ≡ y)
  ≡↠≡′ = Surjection.↠-≡ (record
    { logical-equivalence = record
      { to   = f
      ; from = g
      }
    ; right-inverse-of = f∘g
    })

------------------------------------------------------------------------
-- Some type formers are propositional in erased contexts

-- In an erased context Contractibleᴱ is propositional (assuming
-- extensionality).

@0 Contractibleᴱ-propositional :
  {A : Set a} →
  Extensionality a a →
  Is-proposition (Contractibleᴱ A)
Contractibleᴱ-propositional ext =
  H-level.respects-surjection
    (_≃_.surjection Contractible≃Contractibleᴱ)
    1
    (Contractible-propositional ext)

-- In an erased context Is-equivalenceᴱ f is a proposition (assuming
-- extensionality).
--
-- See also Is-equivalenceᴱ-propositional-for-Erased below.

@0 Is-equivalenceᴱ-propositional :
  {A : Set a} {B : Set b} →
  Extensionality (a ⊔ b) (a ⊔ b) →
  (f : A → B) → Is-proposition (Is-equivalenceᴱ f)
Is-equivalenceᴱ-propositional ext f =
  H-level.respects-surjection
    (_≃_.surjection $ Is-equivalence≃Is-equivalenceᴱ ext)
    1
    (Eq.propositional ext f)

------------------------------------------------------------------------
-- Some results related to Contractibleᴱ

-- Contractibleᴱ respects split surjections with erased proofs.

Contractibleᴱ-respects-surjection :
  (f : A → B) → @0 Split-surjective f →
  Contractibleᴱ A → Contractibleᴱ B
Contractibleᴱ-respects-surjection {A = A} {B = B} f s h@(x , _) =
    f x
  , [ proj₂ (H-level.respects-surjection surj 0
               (Contractibleᴱ→Contractible h))
    ]
  where
  @0 surj : A ↠ B
  surj = record
    { logical-equivalence = record
      { to   = f
      ; from = proj₁ ⊚ s
      }
    ; right-inverse-of = proj₂ ⊚ s
    }

-- "Preimages" (with erased proofs) of an erased function with a
-- quasi-inverse with erased proofs are contractible.

Contractibleᴱ-⁻¹ᴱ :
  (@0 f : A → B)
  (g : B → A)
  (@0 f∘g : ∀ x → f (g x) ≡ x)
  (@0 g∘f : ∀ x → g (f x) ≡ x) →
  ∀ y → Contractibleᴱ (f ⁻¹ᴱ y)
Contractibleᴱ-⁻¹ᴱ {A = A} {B = B} f g f∘g g∘f y =
    (g y , [ proj₂ (proj₁ c)  ])
  , [ cong ⁻¹→⁻¹ᴱ ⊚ proj₂ c ⊚ ⁻¹ᴱ→⁻¹ ]
  where
  @0 A↔B : A ↔ B
  A↔B = record
    { surjection = record
      { logical-equivalence = record
        { to   = f
        ; from = g
        }
      ; right-inverse-of = f∘g
      }
    ; left-inverse-of = g∘f
    }

  @0 c : Contractible (f ⁻¹ y)
  c = Preimage.bijection⁻¹-contractible A↔B y

-- Two types that are contractible (with erased proofs) are equivalent
-- (with erased proofs).

Contractibleᴱ→≃ᴱ : Contractibleᴱ A → Contractibleᴱ B → A ≃ᴱ B
Contractibleᴱ→≃ᴱ (a , [ irrA ]) (b , [ irrB ]) = ↔→≃ᴱ
  (const b)
  (const a)
  irrB
  irrA

-- There is a logical equivalence between Contractibleᴱ A and A ≃ᴱ ⊤.

Contractibleᴱ⇔≃ᴱ⊤ : Contractibleᴱ A ⇔ A ≃ᴱ ⊤
Contractibleᴱ⇔≃ᴱ⊤ = record
  { to   = flip Contractibleᴱ→≃ᴱ Contractibleᴱ-⊤
  ; from = λ A≃⊤ →
      Contractibleᴱ-respects-surjection
        (_≃ᴱ_.from A≃⊤)
        (λ a → tt
             , (_≃ᴱ_.from A≃⊤ tt               ≡⟨⟩
                _≃ᴱ_.from A≃⊤ (_≃ᴱ_.to A≃⊤ a)  ≡⟨ _≃ᴱ_.left-inverse-of A≃⊤ _ ⟩∎
                a                              ∎))
        Contractibleᴱ-⊤
  }
  where
  Contractibleᴱ-⊤ = Contractible→Contractibleᴱ ⊤-contractible

-- There is an equivalence with erased proofs between Contractibleᴱ A
-- and A ≃ᴱ ⊤ (assuming extensionality).

Contractibleᴱ≃ᴱ≃ᴱ⊤ :
  {A : Set a} →
  Extensionality a a →
  Contractibleᴱ A ≃ᴱ (A ≃ᴱ ⊤)
Contractibleᴱ≃ᴱ≃ᴱ⊤ ext = ↔→≃ᴱ
  (_⇔_.to   Contractibleᴱ⇔≃ᴱ⊤)
  (_⇔_.from Contractibleᴱ⇔≃ᴱ⊤)
  (λ _ → to≡to→≡ ext (refl _))
  (λ _ → Contractibleᴱ-propositional ext _ _)

-- If an inhabited type comes with an erased proof of
-- propositionality, then it is contractible (with erased proofs).

inhabited→Is-proposition→Contractibleᴱ :
  A → @0 Is-proposition A → Contractibleᴱ A
inhabited→Is-proposition→Contractibleᴱ x prop = (x , [ prop x ])

-- A variant of the previous result.

inhabited→Is-proposition→≃ᴱ⊤ :
  A → @0 Is-proposition A → A ≃ᴱ ⊤
inhabited→Is-proposition→≃ᴱ⊤ x prop =
  _⇔_.to Contractibleᴱ⇔≃ᴱ⊤
    (inhabited→Is-proposition→Contractibleᴱ x prop)

-- Some closure properties.

Contractibleᴱ-Σ :
  Contractibleᴱ A → (∀ x → Contractibleᴱ (P x)) → Contractibleᴱ (Σ A P)
Contractibleᴱ-Σ cA@(a , _) cB =
    (a , proj₁ (cB a))
  , [ proj₂ $ Σ-closure 0 (Contractibleᴱ→Contractible cA)
                          (Contractibleᴱ→Contractible ⊚ cB)
    ]

Contractibleᴱ-× :
  Contractibleᴱ A → Contractibleᴱ B → Contractibleᴱ (A × B)
Contractibleᴱ-× cA cB = Contractibleᴱ-Σ cA (λ _ → cB)

Contractibleᴱ-Π :
  {A : Set a} {P : A → Set p} →
  @0 Extensionality a p →
  (∀ x → Contractibleᴱ (P x)) → Contractibleᴱ ((x : A) → P x)
Contractibleᴱ-Π ext c =
    proj₁ ⊚ c
  , [ proj₂ $ Π-closure ext 0 (Contractibleᴱ→Contractible ⊚ c)
    ]

Contractibleᴱ-↑ : Contractibleᴱ A → Contractibleᴱ (↑ ℓ A)
Contractibleᴱ-↑ c@(a , _) =
    lift a
  , [ proj₂ $ ↑-closure 0 (Contractibleᴱ→Contractible c)
    ]

------------------------------------------------------------------------
-- The groupoid laws hold for id and _∘_

module Groupoid where

  -- In an erased context the groupoid laws hold for id and _∘_.
  --
  -- TODO: Is it possible to prove the first three results in a
  -- non-erased context?

  @0 left-identity :
    {A : Set a} {B : Set b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (f : A ≃ᴱ B) → id ∘ f ≡ f
  left-identity ext _ = to≡to→≡ ext (refl _)

  @0 right-identity :
    {A : Set a} {B : Set b} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    (f : A ≃ᴱ B) → f ∘ id ≡ f
  right-identity ext _ = to≡to→≡ ext (refl _)

  @0 associativity :
    {A : Set a} {D : Set d} →
    Extensionality (a ⊔ d) (a ⊔ d) →
    (f : C ≃ᴱ D) (g : B ≃ᴱ C) (h : A ≃ᴱ B) →
    f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  associativity ext _ _ _ = to≡to→≡ ext (refl _)

  @0 left-inverse :
    {A : Set a} →
    Extensionality a a →
    (f : A ≃ᴱ B) → inverse f ∘ f ≡ id
  left-inverse ext f =
    to≡to→≡ ext $ apply-ext ext $
    _≃_.left-inverse-of (≃ᴱ→≃ f)

  @0 right-inverse :
    {B : Set b} →
    Extensionality b b →
    (f : A ≃ᴱ B) → f ∘ inverse f ≡ id
  right-inverse ext f =
    to≡to→≡ ext $ apply-ext ext $
    _≃_.right-inverse-of (≃ᴱ→≃ f)

------------------------------------------------------------------------
-- Some simplification lemmas

-- Two simplification lemmas for id.

right-inverse-of-id :
  _≃ᴱ_.right-inverse-of id x ≡ refl x
right-inverse-of-id = refl _

@0 left-inverse-of-id :
  _≃ᴱ_.left-inverse-of id x ≡ refl x
left-inverse-of-id {x = x} =
  left-inverse-of x               ≡⟨⟩
  left-inverse-of (P.id x)        ≡⟨ sym $ right-left-lemma x ⟩
  cong P.id (right-inverse-of x)  ≡⟨ sym $ cong-id _ ⟩
  right-inverse-of x              ≡⟨ right-inverse-of-id ⟩∎
  refl x                          ∎
  where
  open _≃ᴱ_ id

-- Two simplification lemmas for inverse.

@0 right-inverse-of∘inverse :
  (A≃B : A ≃ᴱ B) →
  _≃ᴱ_.right-inverse-of (inverse A≃B) x ≡
  _≃ᴱ_.left-inverse-of A≃B x
right-inverse-of∘inverse _ = refl _

@0 left-inverse-of∘inverse :
  (A≃B : A ≃ᴱ B) →
  _≃ᴱ_.left-inverse-of (inverse A≃B) x ≡
  _≃ᴱ_.right-inverse-of A≃B x
left-inverse-of∘inverse {A = A} {B = B} {x = x} A≃B =
  subst (λ x → _≃ᴱ_.left-inverse-of (inverse A≃B) x ≡
               right-inverse-of x)
        (right-inverse-of x)
        (_≃ᴱ_.left-inverse-of (inverse A≃B) (to (from x))        ≡⟨ sym $ _≃ᴱ_.right-left-lemma (inverse A≃B) (from x) ⟩
         cong to (_≃ᴱ_.right-inverse-of (inverse A≃B) (from x))  ≡⟨ cong (cong to) $ right-inverse-of∘inverse A≃B ⟩
         cong to (left-inverse-of (from x))                      ≡⟨ left-right-lemma (from x) ⟩∎
         right-inverse-of (to (from x))                          ∎)
  where
  open _≃ᴱ_ A≃B

------------------------------------------------------------------------
-- Results that depend on an axiomatisation of []-cong

module []-cong (ax : ∀ {a} → []-cong-axiomatisation a) where

  open Erased.[]-cong₃ ax

  ----------------------------------------------------------------------
  -- More preservation lemmas

  -- Equivalences with erased proofs are in some cases preserved by Σ
  -- (assuming extensionality). Note the type of Q.

  Σ-cong-≃ᴱ-Erased :
    {Q : @0 B → Set q}
    (A≃B : A ≃ᴱ B) →
    (∀ x → P x ≃ᴱ Q (_≃ᴱ_.to A≃B x)) →
    Σ A P ≃ᴱ Σ B (λ x → Q x)
  Σ-cong-≃ᴱ-Erased {B = B} {A = A} {P = P} {Q = Q} A≃B P≃Q =
    [≃]→≃ᴱ ([proofs] ΣAP≃ΣBQ)
    where
    @0 ΣAP≃ΣBQ : Σ A P ≃ Σ B (λ x → Q x)
    ΣAP≃ΣBQ =
      Eq.with-other-inverse
        (Σ-cong (≃ᴱ→≃ A≃B) (λ x → ≃ᴱ→≃ (P≃Q x)))
        (λ (x , y) →
             _≃ᴱ_.from A≃B x
           , _≃ᴱ_.from (P≃Q (_≃ᴱ_.from A≃B x))
               (subst (λ ([ x ]) → Q x)
                  ([]-cong [ sym (_≃ᴱ_.right-inverse-of A≃B x) ]) y))
        (λ (x , y) →
           cong (λ y → _ , _≃ᴱ_.from (P≃Q (_≃ᴱ_.from A≃B x)) y) (
             subst (λ x → Q x) (sym (_≃ᴱ_.right-inverse-of A≃B x)) y  ≡⟨ sym subst-[]-cong-[] ⟩∎

             subst (λ ([ x ]) → Q x)
               ([]-cong [ sym (_≃ᴱ_.right-inverse-of A≃B x) ])
               y                                                      ∎))

  -- A variant of Σ-cong-≃ᴱ-Erased.

  Σ-cong-contra-≃ᴱ-Erased :
    {P : @0 A → Set p}
    (B≃A : B ≃ᴱ A) →
    (∀ x → P (_≃ᴱ_.to B≃A x) ≃ᴱ Q x) →
    Σ A (λ x → P x) ≃ᴱ Σ B Q
  Σ-cong-contra-≃ᴱ-Erased {Q = Q} {P = P} B≃A P≃Q = ↔→≃ᴱ
    (λ (x , y) →
         _≃ᴱ_.from B≃A x
       , _≃ᴱ_.to (P≃Q (_≃ᴱ_.from B≃A x))
            (subst (λ ([ x ]) → P x)
               ([]-cong [ sym (_≃ᴱ_.right-inverse-of B≃A x) ])
               y))
    (λ (x , y) → _≃ᴱ_.to B≃A x , _≃ᴱ_.from (P≃Q x) y)
    (λ (x , y) → Σ-≡,≡→≡
       (_≃ᴱ_.left-inverse-of B≃A x)
       (subst Q (_≃ᴱ_.left-inverse-of B≃A x)
          (_≃ᴱ_.to (P≃Q _)
             (subst (λ ([ x ]) → P x)
                ([]-cong [ sym (_≃ᴱ_.right-inverse-of B≃A _) ])
                (_≃ᴱ_.from (P≃Q x) y)))                                  ≡⟨ cong (λ eq → subst Q (_≃ᴱ_.left-inverse-of B≃A x) (_≃ᴱ_.to (P≃Q _) eq))
                                                                            subst-[]-cong-[] ⟩
        subst Q (_≃ᴱ_.left-inverse-of B≃A x)
          (_≃ᴱ_.to (P≃Q _)
             (subst (λ x → P x) (sym (_≃ᴱ_.right-inverse-of B≃A _))
                (_≃ᴱ_.from (P≃Q x) y)))                                  ≡⟨ cong (λ eq → subst Q (_≃ᴱ_.left-inverse-of B≃A x)
                                                                                           (_≃ᴱ_.to (P≃Q _)
                                                                                              (subst (λ x → P x) (sym eq) _))) $ sym $
                                                                            _≃ᴱ_.left-right-lemma B≃A _ ⟩
        subst Q (_≃ᴱ_.left-inverse-of B≃A x)
          (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from B≃A (_≃ᴱ_.to B≃A x)))
             (subst (λ x → P x)
                (sym (cong (_≃ᴱ_.to B≃A) (_≃ᴱ_.left-inverse-of B≃A _)))
                (_≃ᴱ_.from (P≃Q x) y)))                                  ≡⟨ elim₁
                                                                              (λ eq → subst Q eq
                                                                                        (_≃ᴱ_.to (P≃Q _)
                                                                                           (subst (λ x → P x)
                                                                                              (sym (cong (_≃ᴱ_.to B≃A) eq))
                                                                                              (_≃ᴱ_.from (P≃Q x) y))) ≡
                                                                                      y)
                                                                              (
            subst Q (refl _)
              (_≃ᴱ_.to (P≃Q x)
                 (subst (λ x → P x)
                    (sym (cong (_≃ᴱ_.to B≃A) (refl _)))
                    (_≃ᴱ_.from (P≃Q x) y)))                                    ≡⟨ subst-refl _ _ ⟩

            _≃ᴱ_.to (P≃Q x)
              (subst (λ x → P x)
                 (sym (cong (_≃ᴱ_.to B≃A) (refl _)))
                 (_≃ᴱ_.from (P≃Q x) y))                                        ≡⟨ cong (λ eq → _≃ᴱ_.to (P≃Q _) (subst (λ x → P x) (sym eq) _)) $
                                                                                  cong-refl _ ⟩
            _≃ᴱ_.to (P≃Q x)
              (subst (λ x → P x)
                 (sym (refl _)) (_≃ᴱ_.from (P≃Q x) y))                         ≡⟨ cong (λ eq → _≃ᴱ_.to (P≃Q _) (subst (λ x → P x) eq _))
                                                                                  sym-refl ⟩
            _≃ᴱ_.to (P≃Q x)
              (subst (λ x → P x)
                 (refl _) (_≃ᴱ_.from (P≃Q x) y))                               ≡⟨ cong (λ eq → _≃ᴱ_.to (P≃Q _) eq) $
                                                                                  subst-refl _ _ ⟩

            _≃ᴱ_.to (P≃Q x) (_≃ᴱ_.from (P≃Q x) y)                              ≡⟨ _≃ᴱ_.right-inverse-of (P≃Q x) _ ⟩∎

            y                                                                  ∎)
                                                                              (_≃ᴱ_.left-inverse-of B≃A x) ⟩∎
        y                                                                ∎))
    (λ (x , y) → Σ-≡,≡→≡
       (_≃ᴱ_.right-inverse-of B≃A x)
       (subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
          (_≃ᴱ_.from (P≃Q _)
             (_≃ᴱ_.to (P≃Q _)
                (subst (λ ([ x ]) → P x)
                   ([]-cong [ sym (_≃ᴱ_.right-inverse-of B≃A _) ]) y)))  ≡⟨ cong (subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)) $
                                                                            _≃ᴱ_.left-inverse-of (P≃Q _) _ ⟩
        subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
          (subst (λ ([ x ]) → P x)
             ([]-cong [ sym (_≃ᴱ_.right-inverse-of B≃A _) ]) y)          ≡⟨ cong (subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x))
                                                                            subst-[]-cong-[] ⟩
        subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
          (subst (λ x → P x) (sym (_≃ᴱ_.right-inverse-of B≃A _)) y)      ≡⟨ subst-subst-sym _ _ _ ⟩∎

        y                                                                ∎))

  -- Equivalences with erased proofs are in some cases preserved by Π
  -- (assuming extensionality). Note the type of Q.

  Π-cong-≃ᴱ-Erased :
    {A : Set a} {B : Set b} {P : A → Set p} {Q : @0 B → Set q} →
    Extensionality (a ⊔ b) (p ⊔ q) →
    (A≃B : A ≃ᴱ B) →
    (∀ x → P x ≃ᴱ Q (_≃ᴱ_.to A≃B x)) →
    ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
  Π-cong-≃ᴱ-Erased
    {a = a} {p = p} {A = A} {B = B} {P = P} {Q = Q} ext A≃B P≃Q =
    [≃]→≃ᴱ ([proofs] ΠAP≃ΠBQ)
    where
    @0 ΠAP≃ΠBQ : ((x : A) → P x) ≃ ((x : B) → Q x)
    ΠAP≃ΠBQ =
      Eq.with-other-function
        (Π-cong ext (≃ᴱ→≃ A≃B) (λ x → ≃ᴱ→≃ (P≃Q x)))
        (λ f x → subst (λ ([ x ]) → Q x)
                   ([]-cong [ _≃ᴱ_.right-inverse-of A≃B x ])
                   (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from A≃B x))
                       (f (_≃ᴱ_.from A≃B x))))
        (λ f → apply-ext (lower-extensionality a p ext) λ x →
           subst (λ x → Q x) (_≃ᴱ_.right-inverse-of A≃B x)
              (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from A≃B x)) (f (_≃ᴱ_.from A≃B x)))  ≡⟨ sym subst-[]-cong-[] ⟩∎

           subst (λ ([ x ]) → Q x)
             ([]-cong [ _≃ᴱ_.right-inverse-of A≃B x ])
             (_≃ᴱ_.to (P≃Q (_≃ᴱ_.from A≃B x)) (f (_≃ᴱ_.from A≃B x)))   ∎)

  -- A variant of Π-cong-≃ᴱ-Erased.

  Π-cong-contra-≃ᴱ-Erased :
    {A : Set a} {B : Set b} {P : @0 A → Set p} {Q : B → Set q} →
    Extensionality (a ⊔ b) (p ⊔ q) →
    (B≃A : B ≃ᴱ A) →
    (∀ x → P (_≃ᴱ_.to B≃A x) ≃ᴱ Q x) →
    ((x : A) → P x) ≃ᴱ ((x : B) → Q x)
  Π-cong-contra-≃ᴱ-Erased
    {b = b} {q = q} {A = A} {B = B} {P = P} {Q = Q} ext B≃A P≃Q =
    [≃]→≃ᴱ ([proofs] ΠAP≃ΠBQ)
    where
    @0 ΠAP≃ΠBQ : ((x : A) → P x) ≃ ((x : B) → Q x)
    ΠAP≃ΠBQ =
      Eq.with-other-inverse
        (Π-cong-contra ext (≃ᴱ→≃ B≃A) (λ x → ≃ᴱ→≃ (P≃Q x)))
        (λ f x → subst (λ ([ x ]) → P x)
                   ([]-cong [ _≃ᴱ_.right-inverse-of B≃A x ])
                   (_≃ᴱ_.from (P≃Q (_≃ᴱ_.from B≃A x))
                      (f (_≃ᴱ_.from B≃A x))))
        (λ f → apply-ext (lower-extensionality b q ext) λ x →
           subst (λ x → P x) (_≃ᴱ_.right-inverse-of B≃A x)
              (_≃ᴱ_.from (P≃Q (_≃ᴱ_.from B≃A x)) (f (_≃ᴱ_.from B≃A x)))  ≡⟨ sym subst-[]-cong-[] ⟩∎

           subst (λ ([ x ]) → P x)
             ([]-cong [ _≃ᴱ_.right-inverse-of B≃A x ])
             (_≃ᴱ_.from (P≃Q (_≃ᴱ_.from B≃A x)) (f (_≃ᴱ_.from B≃A x)))   ∎)

  -- Contractibleᴱ preserves isomorphisms (assuming extensionality).

  Contractibleᴱ-cong :
    {A : Set a} {B : Set b} →
    Extensionality? k′ (a ⊔ b) (a ⊔ b) →
    A ↔[ k ] B → Contractibleᴱ A ↝[ k′ ] Contractibleᴱ B
  Contractibleᴱ-cong {A = A} {B = B} ext A↔B =
    (∃ λ (x : A) → Erased ((y : A) → x ≡ y))  ↝⟨ (Σ-cong A≃B′ λ _ →
                                                  Erased-cong?
                                                    (λ ext → Π-cong ext A≃B′ λ _ →
                                                             from-isomorphism $ F.inverse $ Eq.≃-≡ A≃B′)
                                                    ext) ⟩
    (∃ λ (x : B) → Erased ((y : B) → x ≡ y))  □
    where
    A≃B′ = from-isomorphism A↔B

  -- The function _⁻¹ᴱ y respects erased extensional equality.

  ⁻¹ᴱ-respects-extensional-equality :
    {@0 B : Set b} {@0 f g : A → B} {@0 y : B} →
    @0 (∀ x → f x ≡ g x) → f ⁻¹ᴱ y ≃ g ⁻¹ᴱ y
  ⁻¹ᴱ-respects-extensional-equality {f = f} {g = g} {y = y} f≡g =
    (∃ λ x → Erased (f x ≡ y))  ↝⟨ (∃-cong λ _ → Erased-cong-≃ (≡⇒↝ _ (cong (_≡ _) $ f≡g _))) ⟩□
    (∃ λ x → Erased (g x ≡ y))  □

  -- Is-equivalenceᴱ respects erased extensional equality.

  Is-equivalenceᴱ-respects-extensional-equality :
    {A : Set a} {B : Set b} {@0 f g : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    @0 (∀ x → f x ≡ g x) →
    Is-equivalenceᴱ f ↝[ k ] Is-equivalenceᴱ g
  Is-equivalenceᴱ-respects-extensional-equality
    {a = a} {k = k} {f = f} {g = g} ext f≡g =
    (∀ y → Contractibleᴱ (f ⁻¹ᴱ y))  ↝⟨ (∀-cong (lower-extensionality? k a lzero ext) λ _ →
                                         Contractibleᴱ-cong ext $
                                         ⁻¹ᴱ-respects-extensional-equality f≡g) ⟩□
    (∀ y → Contractibleᴱ (g ⁻¹ᴱ y))  □

  ----------------------------------------------------------------------
  -- The left-to-right and right-to-left components of an equivalence
  -- with erased proofs can be replaced with extensionally equal
  -- functions

  -- The forward direction of an equivalence with erased proofs can be
  -- replaced by an extensionally equal function.

  with-other-function :
    (A≃B : A ≃ᴱ B) (f : A → B) →
    @0 (∀ x → _≃ᴱ_.to A≃B x ≡ f x) →
    A ≃ᴱ B
  with-other-function ⟨ g , is-equivalence ⟩ f g≡f =
    ⟨ f
    , Is-equivalenceᴱ-respects-extensional-equality _ g≡f
        is-equivalence
    ⟩

  _ : _≃ᴱ_.to (with-other-function A≃B f p) ≡ f
  _ = refl _

  _ : _≃ᴱ_.from (with-other-function A≃B f p) ≡ _≃ᴱ_.from A≃B
  _ = refl _

  -- The same applies to the other direction.

  with-other-inverse :
    (A≃B : A ≃ᴱ B) (g : B → A) →
    @0 (∀ x → _≃ᴱ_.from A≃B x ≡ g x) →
    A ≃ᴱ B
  with-other-inverse A≃B g ≡g =
    inverse $ with-other-function (inverse A≃B) g ≡g

  _ : _≃ᴱ_.from (with-other-inverse A≃B g p) ≡ g
  _ = refl _

  _ : _≃ᴱ_.to (with-other-inverse A≃B f p) ≡ _≃ᴱ_.to A≃B
  _ = refl _

  ----------------------------------------------------------------------
  -- A lemma

  -- Erased commutes with Contractibleᴱ.

  Erased-Contractibleᴱ↔Contractibleᴱ-Erased :
    {@0 A : Set a} →
    Extensionality? k a a →
    Erased (Contractibleᴱ A) ↝[ k ] Contractibleᴱ (Erased A)
  Erased-Contractibleᴱ↔Contractibleᴱ-Erased {A = A} ext =
    Erased (∃ λ x → Erased ((y : A) → x ≡ y))           ↔⟨ Erased-cong-↔ (∃-cong λ _ → erased Erased↔) ⟩
    Erased (∃ λ x → (y : A) → x ≡ y)                    ↔⟨ Erased-Σ↔Σ ⟩
    (∃ λ x → Erased ((y : A) → erased x ≡ y))           ↝⟨ (∃-cong λ _ →
                                                            Erased-cong?
                                                              (λ ext → ∀-cong ext λ _ →
                                                                         from-isomorphism (F.inverse $ erased Erased↔))
                                                              ext) ⟩
    (∃ λ x → Erased ((y : A) → Erased (erased x ≡ y)))  ↝⟨ (∃-cong λ _ →
                                                            Erased-cong?
                                                              (λ ext → Π-cong ext (F.inverse $ erased Erased↔) λ _ →
                                                                         from-isomorphism Erased-≡↔[]≡[])
                                                              ext) ⟩□
    (∃ λ x → Erased ((y : Erased A) → x ≡ y))           □

  ----------------------------------------------------------------------
  -- More conversion lemmas

  -- An isomorphism relating _⁻¹ᴱ_ to _⁻¹_.

  ⁻¹ᴱ[]↔⁻¹[] :
    {@0 B : Set b} {f : A → Erased B} {@0 y : B} →
    f ⁻¹ᴱ [ y ] ↔ f ⁻¹ [ y ]
  ⁻¹ᴱ[]↔⁻¹[] {f = f} {y = y} =
    (∃ λ x → Erased (f x ≡ [ y ]))       ↔⟨ (∃-cong λ _ → Erased-cong-≃ (Eq.≃-≡ $ Eq.↔⇒≃ $ F.inverse $ erased Erased↔)) ⟩
    (∃ λ x → Erased (erased (f x) ≡ y))  ↝⟨ (∃-cong λ _ → Erased-≡↔[]≡[]) ⟩□
    (∃ λ x → f x ≡ [ y ])                □

  -- An isomorphism relating Contractibleᴱ to Contractible.

  Contractibleᴱ-Erased↔Contractible-Erased :
    {@0 A : Set a} →
    Extensionality? k a a →
    Contractibleᴱ (Erased A) ↝[ k ] Contractible (Erased A)
  Contractibleᴱ-Erased↔Contractible-Erased {A = A} ext =
    Contractibleᴱ (Erased A)  ↝⟨ inverse-ext? Erased-Contractibleᴱ↔Contractibleᴱ-Erased ext ⟩
    Erased (Contractibleᴱ A)  ↔⟨ Erased-Contractibleᴱ↔Erased-Contractible ⟩
    Erased (Contractible A)   ↝⟨ Erased-H-level↔H-level ext 0 ⟩□
    Contractible (Erased A)   □

  -- Some isomorphisms relating Is-equivalenceᴱ to Is-equivalence.

  Erased-Is-equivalenceᴱ↔Erased-Is-equivalence :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Is-equivalenceᴱ f) ↝[ k ] Erased (Is-equivalence f)
  Erased-Is-equivalenceᴱ↔Erased-Is-equivalence
    {a = a} {k = k} {f = f} ext =
    Erased (∀ x → Contractibleᴱ (f ⁻¹ᴱ x))           ↔⟨ Erased-Π↔Π-Erased ⟩
    (∀ x → Erased (Contractibleᴱ (f ⁻¹ᴱ erased x)))  ↝⟨ (∀-cong ext′ λ _ → from-bijection Erased-Contractibleᴱ↔Erased-Contractible) ⟩
    (∀ x → Erased (Contractible (f ⁻¹ᴱ erased x)))   ↝⟨ (∀-cong ext′ λ _ → Erased-H-level↔H-level ext 0) ⟩
    (∀ x → Contractible (Erased (f ⁻¹ᴱ erased x)))   ↝⟨ (∀-cong ext′ λ _ → H-level-cong ext 0 Erased-⁻¹ᴱ↔Erased-⁻¹) ⟩
    (∀ x → Contractible (Erased (f ⁻¹ erased x)))    ↝⟨ (∀-cong ext′ λ _ → inverse-ext? (flip Erased-H-level↔H-level 0) ext) ⟩
    (∀ x → Erased (Contractible (f ⁻¹ erased x)))    ↔⟨ F.inverse Erased-Π↔Π-Erased ⟩□
    Erased (∀ x → Contractible (f ⁻¹ x))             □
    where
    ext′ = lower-extensionality? k a lzero ext

  Is-equivalenceᴱ↔Is-equivalence :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Is-equivalenceᴱ (map f) ↝[ k ] Is-equivalence (map f)
  Is-equivalenceᴱ↔Is-equivalence
    {a = a} {k = k} {f = f} ext =
    (∀ y → Contractibleᴱ (map f ⁻¹ᴱ y))                            ↔⟨⟩
    (∀ y → Contractibleᴱ (∃ λ x → Erased ([ f (erased x) ] ≡ y)))  ↝⟨ (∀-cong ext′ λ _ → Contractibleᴱ-cong ext (Eq.↔⇒≃ $ F.inverse Erased-Σ↔Σ)) ⟩
    (∀ y → Contractibleᴱ (Erased (∃ λ x → [ f x ] ≡ y)))           ↝⟨ (∀-cong ext′ λ _ → Contractibleᴱ-Erased↔Contractible-Erased ext) ⟩
    (∀ y → Contractible (Erased (∃ λ x → [ f x ] ≡ y)))            ↝⟨ (∀-cong ext′ λ _ → H-level-cong ext 0 Erased-Σ↔Σ) ⟩
    (∀ y → Contractible (∃ λ x → Erased (map f x ≡ y)))            ↔⟨⟩
    (∀ y → Contractible (map f ⁻¹ᴱ y))                             ↝⟨ (∀-cong ext′ λ _ → H-level-cong ext 0 ⁻¹ᴱ[]↔⁻¹[]) ⟩□
    (∀ y → Contractible (map f ⁻¹ y))                              □
    where
    ext′ = lower-extensionality? k a lzero ext

  ----------------------------------------------------------------------
  -- Erased "commutes" with some type formers

  -- Erased "commutes" with _⁻¹ᴱ_.

  Erased-⁻¹ᴱ :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} {@0 y : B} →
    Erased (f ⁻¹ᴱ y) ↔ map f ⁻¹ᴱ [ y ]
  Erased-⁻¹ᴱ {f = f} {y = y} =
    Erased (f ⁻¹ᴱ y)  ↝⟨ Erased-⁻¹ᴱ↔Erased-⁻¹ ⟩
    Erased (f ⁻¹ y)   ↝⟨ Erased-⁻¹ ⟩
    map f ⁻¹ [ y ]    ↝⟨ F.inverse ⁻¹ᴱ[]↔⁻¹[] ⟩□
    map f ⁻¹ᴱ [ y ]   □

  -- Erased "commutes" with Is-equivalenceᴱ (assuming extensionality).

  Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ :
    {@0 A : Set a} {@0 B : Set b} {@0 f : A → B} →
    Extensionality? k (a ⊔ b) (a ⊔ b) →
    Erased (Is-equivalenceᴱ f) ↝[ k ] Is-equivalenceᴱ (map f)
  Erased-Is-equivalenceᴱ↔Is-equivalenceᴱ {a = a} {k = k} {f = f} ext =
    Erased (Is-equivalenceᴱ f)  ↝⟨ Erased-Is-equivalenceᴱ↔Erased-Is-equivalence ext ⟩
    Erased (Is-equivalence f)   ↝⟨ Erased-Is-equivalence↔Is-equivalence ext ⟩
    Is-equivalence (map f)      ↝⟨ inverse-ext? Is-equivalenceᴱ↔Is-equivalence ext ⟩□
    Is-equivalenceᴱ (map f)     □

  ----------------------------------------------------------------------
  -- Variants of some lemmas proved above

  -- Is-equivalenceᴱ f is a proposition if the domain of f is Erased A
  -- (assuming extensional equality).

  Is-equivalenceᴱ-propositional-for-Erased :
    Extensionality (a ⊔ b) (a ⊔ b) →
    {@0 A : Set a} {B : Set b} (f : Erased A → B) →
    Is-proposition (Is-equivalenceᴱ f)
  Is-equivalenceᴱ-propositional-for-Erased {a} ext f =
    Π-closure (lower-extensionality a lzero ext) 1 λ _ →
    H-level.respects-surjection (surj _) 1 $
    H-level-propositional ext 0
    where
    surj :
      ∀ y →
      Contractible (Erased (f ⊚ [_]→ ⁻¹ y)) ↠ Contractibleᴱ (f ⁻¹ᴱ y)
    surj y =
      Contractible (Erased (f ⊚ [_]→ ⁻¹ y))         ↔⟨ F.inverse $ Contractibleᴱ-Erased↔Contractible-Erased {k = equivalence} ext ⟩
      Contractibleᴱ (Erased (f ⊚ [_]→ ⁻¹ y))        ↔⟨⟩
      Contractibleᴱ (Erased (∃ λ x → f [ x ] ≡ y))  ↔⟨ Contractibleᴱ-cong {k′ = equivalence} ext $ Eq.↔⇒≃ Erased-Σ↔Σ ⟩
      Contractibleᴱ (∃ λ x → Erased (f x ≡ y))      ↔⟨⟩
      Contractibleᴱ (f ⁻¹ᴱ y)                       □

  -- A variant of to≡to→≡ that is not defined in an erased context.
  -- Note that one side of the equivalence is Erased A.

  to≡to→≡-Erased :
    {@0 A : Set a} {B : Set b} {p q : Erased A ≃ᴱ B} →
    Extensionality (a ⊔ b) (a ⊔ b) →
    _≃ᴱ_.to p ≡ _≃ᴱ_.to q → p ≡ q
  to≡to→≡-Erased {p = ⟨ f , f-eq ⟩} {q = ⟨ g , g-eq ⟩} ext f≡g =
    elim (λ {f g} f≡g → ∀ f-eq g-eq → ⟨ f , f-eq ⟩ ≡ ⟨ g , g-eq ⟩)
         (λ f _ _ →
            cong ⟨ f ,_⟩
              (Is-equivalenceᴱ-propositional-for-Erased ext _ _ _))
         f≡g f-eq g-eq

  -- If f is an equivalence (with erased proofs) from Erased A to B,
  -- then x ≡ y is equivalent (with erased proofs) to f x ≡ f y.

  to≡to≃ᴱ≡-Erased :
    (A≃B : Erased A ≃ᴱ B) →
    (_≃ᴱ_.to A≃B x ≡ _≃ᴱ_.to A≃B y) ≃ᴱ (x ≡ y)
  to≡to≃ᴱ≡-Erased {A = A} {B = B} {x = x} {y = y} A≃B =
    [≃]→≃ᴱ ([proofs] ≡≃≡)
    where
    @0 ≡≃≡ : (_≃ᴱ_.to A≃B x ≡ _≃ᴱ_.to A≃B y) ≃ (x ≡ y)
    ≡≃≡ =
      Eq.with-other-function
        (Eq.≃-≡ (≃ᴱ→≃ A≃B))
        (λ eq →
           x                              ≡⟨ sym $ []-cong [ cong erased (_≃ᴱ_.left-inverse-of A≃B x) ] ⟩
           _≃ᴱ_.from A≃B (_≃ᴱ_.to A≃B x)  ≡⟨ cong (_≃ᴱ_.from A≃B) eq ⟩
           _≃ᴱ_.from A≃B (_≃ᴱ_.to A≃B y)  ≡⟨ []-cong [ cong erased (_≃ᴱ_.left-inverse-of A≃B y) ] ⟩∎
           y                              ∎)
        (λ eq →
           let f = _≃ᴱ_.left-inverse-of A≃B in
           trans (sym (f x)) (trans (cong (_≃ᴱ_.from A≃B) eq) (f y))  ≡⟨ cong₂ (λ p q → trans (sym p) (trans (cong (_≃ᴱ_.from A≃B) eq) q))
                                                                           (sym $ _≃_.right-inverse-of ≡≃[]≡[] _)
                                                                           (sym $ _≃_.right-inverse-of ≡≃[]≡[] _) ⟩∎
           trans (sym ([]-cong [ cong erased (f x) ]))
              (trans (cong (_≃ᴱ_.from A≃B) eq)
                 ([]-cong [ cong erased (f y) ]))                     ∎)
