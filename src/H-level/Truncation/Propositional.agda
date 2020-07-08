------------------------------------------------------------------------
-- Propositional truncation
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- Partly following the HoTT book.

-- The module is parametrised by a notion of equality. The higher
-- constructor of the HIT defining the propositional truncation uses
-- path equality, but the supplied notion of equality is used for many
-- other things.

import Equality.Path as P

module H-level.Truncation.Propositional
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq hiding (elim)

open import Prelude
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J as Embedding hiding (id; _∘_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq hiding (id; _∘_; inverse)
open import Equivalence.Erased equality-with-J using (_≃ᴱ_)
open import Equivalence-relation equality-with-J
open import Erased.Basics equality-with-J as EB using (Erased)
import Erased.Stability equality-with-J as ES
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
import H-level.Truncation.Church equality-with-J as Trunc
open import Injection equality-with-J using (_↣_)
open import Monad equality-with-J
open import Preimage equality-with-J as Preimage using (_⁻¹_)
open import Surjection equality-with-J using (_↠_; Split-surjective)

private
  variable
    a b c d f p r ℓ     : Level
    A A₁ A₂ B B₁ B₂ C D : Set a
    P Q                 : A → Set p
    R                   : A → A → Set r
    k x                 : A

-- Propositional truncation.

data ∥_∥ (A : Set a) : Set a where
  ∣_∣                        : A → ∥ A ∥
  truncation-is-propositionᴾ : P.Is-proposition ∥ A ∥

-- The truncation produces propositions.

truncation-is-proposition : Is-proposition ∥ A ∥
truncation-is-proposition =
  _↔_.from (H-level↔H-level 1) truncation-is-propositionᴾ

-- A dependent eliminator, expressed using paths.

elimᴾ′ :
  (P : ∥ A ∥ → Set p) →
  ((x : A) → P ∣ x ∣) →
  ({x y : ∥ A ∥} (p : P x) (q : P y) →
   P.[ (λ i → P (truncation-is-propositionᴾ x y i)) ] p ≡ q) →
  (x : ∥ A ∥) → P x
elimᴾ′ P f p ∣ x ∣                             = f x
elimᴾ′ P f p (truncation-is-propositionᴾ x y i) =
  p (elimᴾ′ P f p x) (elimᴾ′ P f p y) i

-- A possibly more useful dependent eliminator, expressed using paths.

elimᴾ :
  (P : ∥ A ∥ → Set p) →
  (∀ x → P.Is-proposition (P x)) →
  ((x : A) → P ∣ x ∣) →
  (x : ∥ A ∥) → P x
elimᴾ P p f = elimᴾ′ P f (λ _ _ → P.heterogeneous-irrelevance p)

-- A non-dependent eliminator, expressed using paths.

recᴾ : P.Is-proposition B → (A → B) → ∥ A ∥ → B
recᴾ p = elimᴾ _ (λ _ → p)

-- A dependently typed eliminator.

elim :
  (P : ∥ A ∥ → Set p) →
  (∀ x → Is-proposition (P x)) →
  ((x : A) → P ∣ x ∣) →
  (x : ∥ A ∥) → P x
elim P p = elimᴾ P (_↔_.to (H-level↔H-level 1) ∘ p)

-- Primitive "recursion".

rec : Is-proposition B → (A → B) → ∥ A ∥ → B
rec p = recᴾ (_↔_.to (H-level↔H-level 1) p)

-- A map function.

∥∥-map : (A → B) → ∥ A ∥ → ∥ B ∥
∥∥-map f = rec truncation-is-proposition (∣_∣ ∘ f)

-- The propositional truncation defined here is isomorphic to the one
-- defined in H-level.Truncation.Church.

∥∥↔∥∥ :
  ∀ ℓ {a} {A : Set a} →
  ∥ A ∥ ↔ Trunc.∥ A ∥ 1 (a ⊔ ℓ)
∥∥↔∥∥ ℓ = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec (Trunc.truncation-has-correct-h-level 1 ext)
                   Trunc.∣_∣₁
      ; from = lower {ℓ = ℓ} ∘
               Trunc.rec 1
                         (↑-closure 1 truncation-is-proposition)
                         (lift ∘ ∣_∣)
      }
    ; right-inverse-of = λ _ →
        Trunc.truncation-has-correct-h-level 1 ext _ _
    }
  ; left-inverse-of = λ _ → truncation-is-proposition _ _
  }

mutual

  -- If A and B are logically equivalent, then functions of any kind can
  -- be constructed from ∥ A ∥ to ∥ B ∥.

  ∥∥-cong-⇔ : ∀ {k} → A ⇔ B → ∥ A ∥ ↝[ k ] ∥ B ∥
  ∥∥-cong-⇔ A⇔B = ∥∥-cong-⇔′ (∣_∣ ∘ _⇔_.to A⇔B) (∣_∣ ∘ _⇔_.from A⇔B)

  -- A variant of the previous result.

  ∥∥-cong-⇔′ : ∀ {k} → (A → ∥ B ∥) → (B → ∥ A ∥) → ∥ A ∥ ↝[ k ] ∥ B ∥
  ∥∥-cong-⇔′ A→∥B∥ B→∥A∥ =
    from-equivalence $
    _↠_.from (≃↠⇔ truncation-is-proposition truncation-is-proposition)
      (record
         { to   = rec truncation-is-proposition A→∥B∥
         ; from = rec truncation-is-proposition B→∥A∥
         })

-- The truncation operator preserves all kinds of functions.

private

  ∥∥-cong-↣ : A ↣ B → ∥ A ∥ ↣ ∥ B ∥
  ∥∥-cong-↣ f = record
    { to        = ∥∥-map (_↣_.to f)
    ; injective = λ _ → truncation-is-proposition _ _
    }

∥∥-cong : A ↝[ k ] B → ∥ A ∥ ↝[ k ] ∥ B ∥
∥∥-cong {k = implication}         = ∥∥-map
∥∥-cong {k = logical-equivalence} = ∥∥-cong-⇔
∥∥-cong {k = surjection}          = ∥∥-cong-⇔ ∘ _↠_.logical-equivalence
∥∥-cong {k = bijection}           = ∥∥-cong-⇔ ∘ from-isomorphism
∥∥-cong {k = equivalence}         = ∥∥-cong-⇔ ∘ from-isomorphism
∥∥-cong {k = equivalenceᴱ}        = ∥∥-cong-⇔ ∘ _≃ᴱ_.logical-equivalence
∥∥-cong {k = injection}           = ∥∥-cong-↣
∥∥-cong {k = embedding}           =
  _↔_.to (↣↔Embedding ext
            (mono₁ 1 truncation-is-proposition)
            (mono₁ 1 truncation-is-proposition)) ∘
  ∥∥-cong-↣ ∘ Embedding.injection

-- A form of idempotence for binary sums.

idempotent : ∥ A ⊎ A ∥ ↔ ∥ A ∥
idempotent = ∥∥-cong-⇔ (record { to = [ id , id ]; from = inj₁ })

-- A generalised flattening lemma.

flatten′ :
  (F : (Set ℓ → Set ℓ) → Set f) →
  (∀ {G H} → (∀ {A} → G A → H A) → F G → F H) →
  (F ∥_∥ → ∥ F id ∥) →
  ∥ F ∥_∥ ∥ ↔ ∥ F id ∥
flatten′ _ map f = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec truncation-is-proposition f
      ; from = ∥∥-map (map ∣_∣)
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ → truncation-is-proposition _ _
  }

-- Nested truncations can be flattened.

flatten : ∥ ∥ A ∥ ∥ ↔ ∥ A ∥
flatten {A = A} = flatten′ (λ F → F A) (λ f → f) id

private

  -- Another flattening lemma, given as an example of how flatten′ can
  -- be used.

  ∥∃∥∥∥↔∥∃∥ : {B : A → Set b} →
              ∥ ∃ (∥_∥ ∘ B) ∥ ↔ ∥ ∃ B ∥
  ∥∃∥∥∥↔∥∃∥ {B = B} =
    flatten′ (λ F → ∃ (F ∘ B))
             (λ f → Σ-map id f)
             (uncurry λ x → ∥∥-map (x ,_))

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
x >>=′ f = _↔_.to flatten (∥∥-map f x)

-- The universe-polymorphic variant of bind is associative.

>>=′-associative :
  (x : ∥ A ∥) {f : A → ∥ B ∥} {g : B → ∥ C ∥} →
  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
>>=′-associative x {f} {g} = elim
  (λ x → x >>=′ (λ x₁ → f x₁ >>=′ g) ≡ x >>=′ f >>=′ g)
  (λ _ → ⇒≡ 1 truncation-is-proposition)
  (λ _ → refl _)
  x

instance

  -- The propositional truncation operator is a monad.

  raw-monad : ∀ {ℓ} → Raw-monad (∥_∥ {a = ℓ})
  Raw-monad.return raw-monad = ∣_∣
  Raw-monad._>>=_  raw-monad = _>>=′_

  monad : ∀ {ℓ} → Monad (∥_∥ {a = ℓ})
  Monad.raw-monad monad           = raw-monad
  Monad.left-identity monad x f   = refl _
  Monad.associativity monad x _ _ = >>=′-associative x
  Monad.right-identity monad      = elim
    _
    (λ _ → ⇒≡ 1 truncation-is-proposition)
    (λ _ → refl _)

-- Surjectivity.

Surjective :
  {A : Set a} {B : Set b} →
  (A → B) → Set (a ⊔ b)
Surjective f = ∀ b → ∥ f ⁻¹ b ∥

-- The property Surjective f is a proposition.

Surjective-propositional : {f : A → B} → Is-proposition (Surjective f)
Surjective-propositional =
  Π-closure ext 1 λ _ →
  truncation-is-proposition

-- The function ∣_∣ is surjective.

∣∣-surjective : Surjective (∣_∣ {A = A})
∣∣-surjective = elim
  _
  (λ _ → truncation-is-proposition)
  (λ x → ∣ x , refl _ ∣)

-- Split surjective functions are surjective.

Split-surjective→Surjective :
  {f : A → B} → Split-surjective f → Surjective f
Split-surjective→Surjective s = λ b → ∣ s b ∣

-- Being both surjective and an embedding is equivalent to being an
-- equivalence.
--
-- This is Corollary 4.6.4 from the first edition of the HoTT book
-- (the proof is perhaps not quite identical).

surjective×embedding≃equivalence :
  {f : A → B} →
  (Surjective f × Is-embedding f) ≃ Is-equivalence f
surjective×embedding≃equivalence {f = f} =
  (Surjective f × Is-embedding f)          ↔⟨ ∀-cong ext (λ _ → ∥∥↔∥∥ lzero) ×-cong F.id ⟩
  (Trunc.Surjective _ f × Is-embedding f)  ↝⟨ Trunc.surjective×embedding≃equivalence lzero ext ⟩□
  Is-equivalence f                         □

-- If the underlying type is a proposition, then truncations of the
-- type are isomorphic to the type itself.

∥∥↔ : Is-proposition A → ∥ A ∥ ↔ A
∥∥↔ A-prop = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec A-prop id
      ; from = ∣_∣
      }
    ; right-inverse-of = λ _ → refl _
    }
  ; left-inverse-of = λ _ → truncation-is-proposition _ _
  }

-- A type is a proposition if it is equivalent to the propositional
-- truncation of some type.

≃∥∥→Is-proposition : A ≃ ∥ B ∥ → Is-proposition A
≃∥∥→Is-proposition A≃∥B∥ a₁ a₂ =     $⟨ truncation-is-proposition _ _ ⟩
  _≃_.to A≃∥B∥ a₁ ≡ _≃_.to A≃∥B∥ a₂  ↝⟨ Eq.≃-≡ A≃∥B∥ ⟩□
  a₁ ≡ a₂                            □

-- A simple isomorphism involving propositional truncation.

∥∥×↔ : ∥ A ∥ × A ↔ A
∥∥×↔ =
  drop-⊤-left-× λ a →
  _⇔_.to contractible⇔↔⊤ $
    propositional⇒inhabited⇒contractible
      truncation-is-proposition
      ∣ a ∣

-- A variant of ∥∥×↔, introduced to ensure that the right-inverse-of
-- proof is, by definition, simple.

∥∥×≃ : (∥ A ∥ × A) ≃ A
∥∥×≃ =
  ⟨ proj₂
  , (λ a → propositional⇒inhabited⇒contractible
             (mono₁ 0 $
                Preimage.bijection⁻¹-contractible ∥∥×↔ a)
             ((∣ a ∣ , a) , refl _))
  ⟩

_ : _≃_.right-inverse-of ∥∥×≃ x ≡ refl _
_ = refl _

-- A variant of ∥∥×≃.

Erased-∥∥×≃ : (Erased ∥ A ∥ × A) ≃ A
Erased-∥∥×≃ =
  ⟨ proj₂
  , (λ a → propositional⇒inhabited⇒contractible
             (mono₁ 0 $
                Preimage.bijection⁻¹-contractible
                  (record
                     { surjection = record
                       { logical-equivalence = record
                         { from = λ a → EB.[ ∣ a ∣ ] , a
                         }
                       ; right-inverse-of = refl
                       }
                     ; left-inverse-of = λ (x , y) →
                         cong₂ _,_
                           (EB.[]-cong-axiomatisation.[]-cong
                              (ES.Extensionality→[]-cong ext)
                              EB.[ truncation-is-proposition _ _ ])
                           (refl _)
                     })
                  a)
             ((EB.[ ∣ a ∣ ] , a) , refl _))
  ⟩

_ : _≃_.right-inverse-of Erased-∥∥×≃ x ≡ refl _
_ = refl _

-- ∥_∥ commutes with _×_.

∥∥×∥∥↔∥×∥ : (∥ A ∥ × ∥ B ∥) ↔ ∥ A × B ∥
∥∥×∥∥↔∥×∥ = record
  { surjection = record
    { logical-equivalence = record
      { from = λ p → ∥∥-map proj₁ p , ∥∥-map proj₂ p
      ; to   = λ { (x , y) →
                   rec truncation-is-proposition
                       (λ x → rec truncation-is-proposition
                                  (λ y → ∣ x , y ∣)
                                  y)
                       x }
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      ×-closure 1 truncation-is-proposition
                  truncation-is-proposition
        _ _
  }

-- Variants of proj₁-closure.

private

  H-level-×₁-lemma :
    (A → ∥ B ∥) →
    ∀ n → H-level (suc n) (A × B) → H-level (suc n) A
  H-level-×₁-lemma inhabited n h =
    [inhabited⇒+]⇒+ n λ a →
    rec (H-level-propositional ext (suc n))
        (λ b → proj₁-closure (λ _ → b) (suc n) h)
        (inhabited a)

H-level-×₁ :
  (A → ∥ B ∥) →
  ∀ n → H-level n (A × B) → H-level n A
H-level-×₁ inhabited zero h =
  propositional⇒inhabited⇒contractible
    (H-level-×₁-lemma inhabited 0 (mono₁ 0 h))
    (proj₁ (proj₁ h))
H-level-×₁ inhabited (suc n) =
  H-level-×₁-lemma inhabited n

H-level-×₂ :
  (B → ∥ A ∥) →
  ∀ n → H-level n (A × B) → H-level n B
H-level-×₂ {B = B} {A = A} inhabited n =
  H-level n (A × B)  ↝⟨ H-level.respects-surjection (from-bijection ×-comm) n ⟩
  H-level n (B × A)  ↝⟨ H-level-×₁ inhabited n ⟩□
  H-level n B        □

-- If A is merely inhabited, then the truncation of A is isomorphic to
-- the unit type.

inhabited⇒∥∥↔⊤ : ∥ A ∥ → ∥ A ∥ ↔ ⊤
inhabited⇒∥∥↔⊤ ∥a∥ =
  _⇔_.to contractible⇔↔⊤ $
    propositional⇒inhabited⇒contractible
      truncation-is-proposition
      ∥a∥

-- If A is not inhabited, then the propositional truncation of A is
-- isomorphic to the empty type.

not-inhabited⇒∥∥↔⊥ : ¬ A → ∥ A ∥ ↔ ⊥ {ℓ = ℓ}
not-inhabited⇒∥∥↔⊥ {A = A} =
  ¬ A        ↝⟨ (λ ¬a ∥a∥ → rec ⊥-propositional ¬a ∥a∥) ⟩
  ¬ ∥ A ∥    ↝⟨ inverse ∘ Bijection.⊥↔uninhabited ⟩□
  ∥ A ∥ ↔ ⊥  □

-- The negation of the truncation of A is isomorphic to the negation
-- of A.

¬∥∥↔¬ : ¬ ∥ A ∥ ↔ ¬ A
¬∥∥↔¬ {A = A} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f ∘ ∣_∣
      ; from = rec ⊥-propositional
      }
    ; right-inverse-of = λ _ → ¬-propositional ext _ _
    }
  ; left-inverse-of = λ _ → ¬-propositional ext _ _
  }

-- The function λ R x y → ∥ R x y ∥ preserves Is-equivalence-relation.

∥∥-preserves-Is-equivalence-relation :
  Is-equivalence-relation R →
  Is-equivalence-relation (λ x y → ∥ R x y ∥)
∥∥-preserves-Is-equivalence-relation R-equiv = record
  { reflexive  = ∣ reflexive ∣
  ; symmetric  = symmetric ⟨$⟩_
  ; transitive = λ p q → transitive ⟨$⟩ p ⊛ q
  }
  where
  open Is-equivalence-relation R-equiv

mutual

  -- The propositional truncation's universal property.

  universal-property :
    Is-proposition B →
    (∥ A ∥ → B) ≃ (A → B)
  universal-property B-prop = universal-property-Π (λ _ → B-prop)

  -- A generalisation of the universal property.

  universal-property-Π :
    (∀ x → Is-proposition (P x)) →
    ((x : ∥ A ∥) → P x) ≃ ((x : A) → P ∣ x ∣)
  universal-property-Π {A = A} {P = P} P-prop =
    ((x : ∥ A ∥) → P x)      ↝⟨ _↠_.from (≃↠⇔ prop truncation-is-proposition)
                                  (record { to   = λ f → ∣ f ∘ ∣_∣ ∣
                                          ; from = rec prop (elim _ P-prop)
                                          }) ⟩
    ∥ ((x : A) → P ∣ x ∣) ∥  ↔⟨ ∥∥↔ (Π-closure ext 1 λ _ → P-prop _) ⟩□
    ((x : A) → P ∣ x ∣)      □
    where
    prop = Π-closure ext 1 λ _ → P-prop _

private

  -- The universal property computes in the right way.

  _ :
    (B-prop : Is-proposition B)
    (f : ∥ A ∥ → B) →
    _≃_.to (universal-property B-prop) f ≡ f ∘ ∣_∣
  _ = λ _ _ → refl _

  _ :
    (B-prop : Is-proposition B)
    (f : A → B) (x : A) →
    _≃_.from (universal-property B-prop) f ∣ x ∣ ≡ f x
  _ = λ _ _ _ → refl _

-- If there is a function f : A → ∥ B ∥, then f is an equivalence if
-- and only if the second projection from A × B is an equivalence.

equivalence-to-∥∥≃proj₂-equivalence :
  (f : A → ∥ B ∥) →
  Is-equivalence f ≃ Is-equivalence (proj₂ ⦂ (A × B → B))
equivalence-to-∥∥≃proj₂-equivalence {A = A} {B = B} f = Eq.⇔→≃
  (Eq.propositional ext _)
  (Eq.propositional ext _)
  (λ eq → _≃_.is-equivalence
            (A × B      ↝⟨ (×-cong₁ λ _ → Eq.⟨ _ , eq ⟩) ⟩
             ∥ B ∥ × B  ↝⟨ ∥∥×≃ ⟩□
             B          □))
  from
  where
  from : Is-equivalence proj₂ → Is-equivalence f
  from eq = _≃_.is-equivalence $ Eq.⇔→≃
    A-prop
    truncation-is-proposition
    _
    (rec A-prop (proj₁ ∘ _≃_.from Eq.⟨ _ , eq ⟩))
    where
    A-prop₁ : B → Is-proposition A
    A-prop₁ b a₁ a₂ =                  $⟨ refl _ ⟩
      b ≡ b                            ↔⟨⟩
      proj₂ (a₁ , b) ≡ proj₂ (a₂ , b)  ↔⟨ Eq.≃-≡ Eq.⟨ _ , eq ⟩ ⟩
      (a₁ , b) ≡ (a₂ , b)              ↝⟨ cong proj₁ ⟩□
      a₁ ≡ a₂                          □

    A-prop : Is-proposition A
    A-prop = [inhabited⇒+]⇒+ 0
      (A                 ↝⟨ f ⟩
       ∥ B ∥             ↝⟨ rec (H-level-propositional ext 1) A-prop₁ ⟩□
       Is-proposition A  □)

-- There is an equivalence between "A is equivalent to ∥ B ∥" and
-- "there is a function from A to ∥ B ∥ and the second projection is
-- an equivalence from A × B to B".

≃∥∥≃→∥∥×proj₂-equivalence :
  (A ≃ ∥ B ∥) ≃ ((A → ∥ B ∥) × Is-equivalence (proj₂ ⦂ (A × B → B)))
≃∥∥≃→∥∥×proj₂-equivalence {A = A} {B = B} =
  A ≃ ∥ B ∥                                           ↔⟨ Eq.≃-as-Σ ⟩
  (∃ λ (f : A → ∥ B ∥) → Is-equivalence f)            ↝⟨ ∃-cong equivalence-to-∥∥≃proj₂-equivalence ⟩□
  (A → ∥ B ∥) × Is-equivalence (proj₂ ⦂ (A × B → B))  □

-- The following three results come from "Generalizations of Hedberg's
-- Theorem" by Kraus, Escardó, Coquand and Altenkirch.

-- Types with constant endofunctions are "h-stable" (meaning that
-- "mere inhabitance" implies inhabitance).

constant-endofunction⇒h-stable : {f : A → A} → Constant f → ∥ A ∥ → A
constant-endofunction⇒h-stable {A = A} {f = f} c =
  ∥ A ∥                    ↝⟨ rec (fixpoint-lemma f c) (λ x → f x , c (f x) x) ⟩
  (∃ λ (x : A) → f x ≡ x)  ↝⟨ proj₁ ⟩□
  A                        □

-- Having a constant endofunction is logically equivalent to being
-- h-stable.

constant-endofunction⇔h-stable :
  (∃ λ (f : A → A) → Constant f) ⇔ (∥ A ∥ → A)
constant-endofunction⇔h-stable = record
  { to = λ { (_ , c) → constant-endofunction⇒h-stable c }
  ; from = λ f → f ∘ ∣_∣ , λ x y →

      f ∣ x ∣  ≡⟨ cong f $ truncation-is-proposition _ _ ⟩∎
      f ∣ y ∣  ∎
  }

-- A type is a set if and only if it is "h-separated" (which means
-- that all its equality types are h-stable).

Is-set⇔h-separated :
  Is-set A ⇔ ((x y : A) → ∥ x ≡ y ∥ → x ≡ y)
Is-set⇔h-separated {A = A} = record
  { to   = λ A-set _ _ → rec A-set id
  ; from =
      ((x y : A) → ∥ x ≡ y ∥ → x ≡ y)                     ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ →
                                                              _⇔_.from constant-endofunction⇔h-stable) ⟩
      ((x y : A) → ∃ λ (f : x ≡ y → x ≡ y) → Constant f)  ↝⟨ constant⇒set ⟩□
      Is-set A                                            □
  }

-- Variants of the following two lemmas were communicated to me by
-- Nicolai Kraus. They are closely related to Lemma 2.1 in his paper
-- "The General Universal Property of the Propositional Truncation".

-- A variant of ∥∥×≃.

drop-∥∥ :
  {B : A → Set b} →
  (A → ∥ C ∥) →
  (∥ C ∥ → ∀ x → B x) ≃ (∀ x → B x)
drop-∥∥ {C = C} {B = B} inh =
  Eq.with-other-inverse
    ((∥ C ∥ → ∀ a → B a)  ↔⟨ Π-comm ⟩
     (∀ a → ∥ C ∥ → B a)  ↝⟨ (∀-cong ext λ a → drop-⊤-left-Π ext (inhabited⇒∥∥↔⊤ (inh a))) ⟩□
     (∀ a → B a)          □)
    (λ f _ → f)
    (λ f → ⟨ext⟩ λ _ → ⟨ext⟩ λ a →
       _    ≡⟨ subst-const _ ⟩∎
       f a  ∎)

-- Another variant of ∥∥×≃.

push-∥∥ :
  {B : A → Set b} {C : (∀ x → B x) → Set c} →
  (A → ∥ D ∥) →
  (∥ D ∥ → ∃ λ (f : ∀ x → B x) → C f) ≃
  (∃ λ (f : ∀ x → B x) → ∥ D ∥ → C f)
push-∥∥ {D = D} {B = B} {C = C} inh =
  (∥ D ∥ → ∃ λ (f : ∀ c → B c) → C f)            ↔⟨ ΠΣ-comm ⟩
  (∃ λ (f : ∥ D ∥ → ∀ c → B c) → ∀ b → C (f b))  ↝⟨ (Σ-cong-contra (inverse $ drop-∥∥ inh) λ _ → F.id) ⟩□
  (∃ λ (f : ∀ c → B c) → ∥ D ∥ → C f)            □

-- Having a coherently constant function into a groupoid is equivalent
-- to having a function from a propositionally truncated type into the
-- groupoid. This result is Proposition 2.3 in "The General Universal
-- Property of the Propositional Truncation" by Kraus.

Coherently-constant : {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Coherently-constant f =
  ∃ λ (c : Constant f) →
  ∀ a₁ a₂ a₃ → trans (c a₁ a₂) (c a₂ a₃) ≡ c a₁ a₃

coherently-constant-function≃∥inhabited∥⇒inhabited :
  {A : Set a} {B : Set b} →
  H-level 3 B →
  (∃ λ (f : A → B) → Coherently-constant f) ≃ (∥ A ∥ → B)
coherently-constant-function≃∥inhabited∥⇒inhabited
  {a = a} {b = b} {A = A} {B} B-groupoid =

  (∃ λ (f : A → B) → Coherently-constant f)  ↝⟨ Trunc.coherently-constant-function≃∥inhabited∥⇒inhabited lzero ext B-groupoid ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)                ↝⟨ →-cong₁ ext (inverse $ ∥∥↔∥∥ (a ⊔ b)) ⟩□
  (∥ A ∥ → B)                                □

private

  -- One direction of the proposition above computes in the right way.

  to-coherently-constant-function≃∥inhabited∥⇒inhabited :
    (h : H-level 3 B)
    (f : ∃ λ (f : A → B) → Coherently-constant f) (x : A) →
    _≃_.to (coherently-constant-function≃∥inhabited∥⇒inhabited h)
      f ∣ x ∣ ≡
    proj₁ f x
  to-coherently-constant-function≃∥inhabited∥⇒inhabited _ _ _ = refl _

-- Having a constant function into a set is equivalent to having a
-- function from a propositionally truncated type into the set. The
-- statement of this result is that of Proposition 2.2 in "The General
-- Universal Property of the Propositional Truncation" by Kraus, but
-- it uses a different proof: as observed by Kraus this result follows
-- from Proposition 2.3.

constant-function≃∥inhabited∥⇒inhabited :
  {A : Set a} {B : Set b} →
  Is-set B →
  (∃ λ (f : A → B) → Constant f) ≃ (∥ A ∥ → B)
constant-function≃∥inhabited∥⇒inhabited
  {a = a} {b = b} {A = A} {B} B-set =

  (∃ λ (f : A → B) → Constant f)  ↝⟨ Trunc.constant-function≃∥inhabited∥⇒inhabited lzero ext B-set ⟩
  (Trunc.∥ A ∥ 1 (a ⊔ b) → B)     ↝⟨ →-cong₁ ext (inverse $ ∥∥↔∥∥ (a ⊔ b)) ⟩□
  (∥ A ∥ → B)                     □

private

  -- One direction of the proposition above computes in the right way.

  to-constant-function≃∥inhabited∥⇒inhabited :
    (B-set : Is-set B)
    (f : ∃ λ (f : A → B) → Constant f) (x : A) →
    _≃_.to (constant-function≃∥inhabited∥⇒inhabited B-set) f ∣ x ∣ ≡
    proj₁ f x
  to-constant-function≃∥inhabited∥⇒inhabited _ _ _ = refl _

-- The axiom of choice, in one of the alternative forms given in the
-- HoTT book (§3.8).

Axiom-of-choice : (a b : Level) → Set (lsuc (a ⊔ b))
Axiom-of-choice a b =
  {A : Set a} {B : A → Set b} →
  Is-set A → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- The axiom of choice can be turned into a bijection.

choice-bijection :
  {A : Set a} {B : A → Set b} →
  Axiom-of-choice a b → Is-set A →
  (∀ x → ∥ B x ∥) ↔ ∥ (∀ x → B x) ∥
choice-bijection choice A-set = record
  { surjection = record
    { logical-equivalence = record
      { to   = choice A-set
      ; from = λ f x → ∥∥-map (_$ x) f
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      (Π-closure ext 1 λ _ →
       truncation-is-proposition) _ _
  }

-- The axiom of countable choice, stated in a corresponding way.

Axiom-of-countable-choice : (b : Level) → Set (lsuc b)
Axiom-of-countable-choice b =
  {B : ℕ → Set b} → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥

-- The axiom of countable choice can be turned into a bijection.

countable-choice-bijection :
  {B : ℕ → Set b} →
  Axiom-of-countable-choice b →
  (∀ x → ∥ B x ∥) ↔ ∥ (∀ x → B x) ∥
countable-choice-bijection cc = record
  { surjection = record
    { logical-equivalence = record
      { to   = cc
      ; from = λ f x → ∥∥-map (_$ x) f
      }
    ; right-inverse-of = λ _ → truncation-is-proposition _ _
    }
  ; left-inverse-of = λ _ →
      (Π-closure ext 1 λ _ →
       truncation-is-proposition) _ _
  }

------------------------------------------------------------------------
-- Definitions related to truncated binary sums

-- Truncated binary sums.

infixr 1 _∥⊎∥_

_∥⊎∥_ : Set a → Set b → Set (a ⊔ b)
A ∥⊎∥ B = ∥ A ⊎ B ∥

-- Introduction rules.

∣inj₁∣ : A → A ∥⊎∥ B
∣inj₁∣ = ∣_∣ ∘ inj₁

∣inj₂∣ : B → A ∥⊎∥ B
∣inj₂∣ = ∣_∣ ∘ inj₂

-- _∥⊎∥_ is pointwise propositional.

∥⊎∥-propositional : Is-proposition (A ∥⊎∥ B)
∥⊎∥-propositional = truncation-is-proposition

-- _∥⊎∥_ preserves all kinds of functions.

infixr 1 _∥⊎∥-cong_

_∥⊎∥-cong_ : A₁ ↝[ k ] A₂ → B₁ ↝[ k ] B₂ → A₁ ∥⊎∥ B₁ ↝[ k ] A₂ ∥⊎∥ B₂
A₁↝A₂ ∥⊎∥-cong B₁↝B₂ = ∥∥-cong (A₁↝A₂ ⊎-cong B₁↝B₂)

-- _∥⊎∥_ is commutative.

∥⊎∥-comm : A ∥⊎∥ B ↔ B ∥⊎∥ A
∥⊎∥-comm = ∥∥-cong ⊎-comm

-- If one truncates the types to the left or right of _∥⊎∥_, then one
-- ends up with an isomorphic type.

truncate-left-∥⊎∥ : A ∥⊎∥ B ↔ ∥ A ∥ ∥⊎∥ B
truncate-left-∥⊎∥ =
  inverse $ flatten′ (λ F → F _ ⊎ _) (λ f → ⊎-map f id) [ ∥∥-map inj₁ , ∣inj₂∣ ]

truncate-right-∥⊎∥ : A ∥⊎∥ B ↔ A ∥⊎∥ ∥ B ∥
truncate-right-∥⊎∥ {A = A} {B = B} =
  A ∥⊎∥ B      ↝⟨ ∥⊎∥-comm ⟩
  B ∥⊎∥ A      ↝⟨ truncate-left-∥⊎∥ ⟩
  ∥ B ∥ ∥⊎∥ A  ↝⟨ ∥⊎∥-comm ⟩□
  A ∥⊎∥ ∥ B ∥  □

-- _∥⊎∥_ is associative.

∥⊎∥-assoc : A ∥⊎∥ (B ∥⊎∥ C) ↔ (A ∥⊎∥ B) ∥⊎∥ C
∥⊎∥-assoc {A = A} {B = B} {C = C} =
  ∥ A ⊎ ∥ B ⊎ C ∥ ∥  ↝⟨ inverse truncate-right-∥⊎∥ ⟩
  ∥ A ⊎ B ⊎ C ∥      ↝⟨ ∥∥-cong ⊎-assoc ⟩
  ∥ (A ⊎ B) ⊎ C ∥    ↝⟨ truncate-left-∥⊎∥ ⟩□
  ∥ ∥ A ⊎ B ∥ ⊎ C ∥  □

-- ⊥ is a left and right identity of _∥⊎∥_ if the other argument is a
-- proposition.

∥⊎∥-left-identity : Is-proposition A → ⊥ {ℓ = ℓ} ∥⊎∥ A ↔ A
∥⊎∥-left-identity {A = A} A-prop =
  ∥ ⊥ ⊎ A ∥  ↝⟨ ∥∥-cong ⊎-left-identity ⟩
  ∥ A ∥      ↝⟨ ∥∥↔ A-prop ⟩□
  A          □

∥⊎∥-right-identity : Is-proposition A → A ∥⊎∥ ⊥ {ℓ = ℓ} ↔ A
∥⊎∥-right-identity {A = A} A-prop =
  A ∥⊎∥ ⊥  ↔⟨ ∥⊎∥-comm ⟩
  ⊥ ∥⊎∥ A  ↔⟨ ∥⊎∥-left-identity A-prop ⟩□
  A        □

-- _∥⊎∥_ is idempotent for propositions.

∥⊎∥-idempotent : Is-proposition A → A ∥⊎∥ A ↔ A
∥⊎∥-idempotent {A = A} A-prop =
  ∥ A ⊎ A ∥  ↝⟨ idempotent ⟩
  ∥ A ∥      ↝⟨ ∥∥↔ A-prop ⟩□
  A          □

-- Sometimes a truncated binary sum is isomorphic to one of its
-- summands.

drop-left-∥⊎∥ :
  Is-proposition B → (A → B) → A ∥⊎∥ B ↔ B
drop-left-∥⊎∥ B-prop A→B =
  _≃_.bijection $
  _↠_.from (≃↠⇔ ∥⊎∥-propositional B-prop)
    (record
      { to   = rec B-prop [ to-implication A→B , id ]
      ; from = ∣inj₂∣
      })

drop-right-∥⊎∥ :
  Is-proposition A → (B → A) → A ∥⊎∥ B ↔ A
drop-right-∥⊎∥ {A = A} {B = B} A-prop B→A =
  A ∥⊎∥ B  ↝⟨ ∥⊎∥-comm ⟩
  B ∥⊎∥ A  ↝⟨ drop-left-∥⊎∥ A-prop B→A ⟩□
  A        □

drop-⊥-right-∥⊎∥ :
  Is-proposition A → ¬ B → A ∥⊎∥ B ↔ A
drop-⊥-right-∥⊎∥ A-prop ¬B =
  drop-right-∥⊎∥ A-prop (⊥-elim ∘ ¬B)

drop-⊥-left-∥⊎∥ :
  Is-proposition B → ¬ A → A ∥⊎∥ B ↔ B
drop-⊥-left-∥⊎∥ B-prop ¬A =
  drop-left-∥⊎∥ B-prop (⊥-elim ∘ ¬A)

-- A type of functions from a truncated binary sum to a family of
-- propositions can be expressed as a binary product of function
-- types.

Π∥⊎∥↔Π×Π :
  (∀ x → Is-proposition (P x)) →
  ((x : A ∥⊎∥ B) → P x)
    ↔
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))
Π∥⊎∥↔Π×Π {A = A} {B = B} {P = P} P-prop =
  ((x : A ∥⊎∥ B) → P x)                                ↔⟨ universal-property-Π P-prop ⟩
  ((x : A ⊎ B) → P ∣ x ∣)                              ↝⟨ Π⊎↔Π×Π ext ⟩□
  ((x : A) → P (∣inj₁∣ x)) × ((y : B) → P (∣inj₂∣ y))  □

-- Two distributivity laws for Σ and _∥⊎∥_.

Σ-∥⊎∥-distrib-left :
  Is-proposition A →
  Σ A (λ x → P x ∥⊎∥ Q x) ↔ Σ A P ∥⊎∥ Σ A Q
Σ-∥⊎∥-distrib-left {P = P} {Q = Q} A-prop =
  (∃ λ x → ∥ P x ⊎ Q x ∥)      ↝⟨ inverse $ ∥∥↔ (Σ-closure 1 A-prop λ _ → ∥⊎∥-propositional) ⟩
  ∥ (∃ λ x → ∥ P x ⊎ Q x ∥) ∥  ↝⟨ flatten′ (λ F → (∃ λ x → F (P x ⊎ Q x))) (λ f → Σ-map id f) (uncurry λ x → ∥∥-map (x ,_)) ⟩
  ∥ (∃ λ x → P x ⊎ Q x) ∥      ↝⟨ ∥∥-cong ∃-⊎-distrib-left ⟩□
  ∥ ∃ P ⊎ ∃ Q ∥                □

Σ-∥⊎∥-distrib-right :
  (∀ x → Is-proposition (P x)) →
  Σ (A ∥⊎∥ B) P ↔ Σ A (P ∘ ∣inj₁∣) ∥⊎∥ Σ B (P ∘ ∣inj₂∣)
Σ-∥⊎∥-distrib-right {A = A} {B = B} {P = P} P-prop =
  _≃_.bijection $
  _↠_.from (≃↠⇔ prop₂ prop₁)
    (record
      { to   = uncurry $
               elim _ (λ _ → Π-closure ext 1 λ _ → prop₁) λ where
                 (inj₁ x) y → ∣ inj₁ (x , y) ∣
                 (inj₂ x) y → ∣ inj₂ (x , y) ∣
      ; from = rec prop₂ [ Σ-map ∣inj₁∣ id , Σ-map ∣inj₂∣ id ]
      })
  where
  prop₁ = ∥⊎∥-propositional
  prop₂ = Σ-closure 1 ∥⊎∥-propositional P-prop

-- A variant of one of De Morgan's laws.

¬∥⊎∥¬↔¬× :
  Dec A → Dec B →
  ¬ A ∥⊎∥ ¬ B ↔ ¬ (A × B)
¬∥⊎∥¬↔¬× {A = A} {B = B} dec-A dec-B = record
  { surjection = record
    { logical-equivalence = record
      { to   = rec (¬-propositional ext) ¬⊎¬→×¬
      ; from = ∣_∣ ∘ _↠_.from (¬⊎¬↠¬× ext dec-A dec-B)
      }
    ; right-inverse-of = λ _ → ¬-propositional ext _ _
    }
  ; left-inverse-of = λ _ → ∥⊎∥-propositional _ _
  }
