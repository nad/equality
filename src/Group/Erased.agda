------------------------------------------------------------------------
-- Groups with erased "proofs"
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Group.Erased
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; _∘_) renaming (_×_ to _⊗_)

import Bijection eq as B
open import Equivalence eq as Eq using (_≃_)
open import Equivalence.Erased eq as EEq using (_≃ᴱ_)
open import Erased.Level-1 eq as Erased
open import Extensionality eq
open import Function-universe eq as F hiding (id; _∘_)
open import Group eq using (Group)
open import Groupoid eq using (Groupoid)
open import H-level eq
open import H-level.Closure eq
open import Integer.Basics eq using (+_; -[1+_])
open import Univalence-axiom eq

private
  module @0 BC {a} =
    Erased.[]-cong₁ (erased-instance-of-[]-cong-axiomatisation {a = a})

private variable
  a g₁ g₂ : Level
  A       : Type _
  g x y   : A
  k       : Kind

------------------------------------------------------------------------
-- Groups

-- Groups with erased "proofs".
--
-- Note that the carrier type is required to be a set (following the
-- HoTT book).

record Groupᴱ g : Type (lsuc g) where
  infix  8 _⁻¹
  infixr 7 _∘_

  field
    Carrier           : Type g
    @0 Carrier-is-set : Is-set Carrier
    _∘_               : Carrier → Carrier → Carrier
    id                : Carrier
    _⁻¹               : Carrier → Carrier
    @0 left-identity  : ∀ x → (id ∘ x) ≡ x
    @0 right-identity : ∀ x → (x ∘ id) ≡ x
    @0 assoc          : ∀ x y z → (x ∘ (y ∘ z)) ≡ ((x ∘ y) ∘ z)
    @0 left-inverse   : ∀ x → ((x ⁻¹) ∘ x) ≡ id
    @0 right-inverse  : ∀ x → (x ∘ (x ⁻¹)) ≡ id

  -- Groups are groupoids.

  @0 groupoid : Groupoid lzero g
  groupoid = record
    { Object         = ⊤
    ; _∼_            = λ _ _ → Carrier
    ; id             = id
    ; _∘_            = _∘_
    ; _⁻¹            = _⁻¹
    ; left-identity  = left-identity
    ; right-identity = right-identity
    ; assoc          = assoc
    ; left-inverse   = left-inverse
    ; right-inverse  = right-inverse
    }

  private
    open module @0 G = Groupoid groupoid public
      hiding (Object; _∼_; id; _∘_; _⁻¹; left-identity; right-identity;
              assoc; left-inverse; right-inverse)

private variable
  G G₁ G₁′ G₂ G₂′ G₃ : Groupᴱ g

-- The type of groups can be expressed using a nested Σ-type.

Groupᴱ-as-Σ :
  Groupᴱ g ≃
  ∃ λ (A : Type g) →
  ∃ λ (_∘_ : A → A → A) →
  ∃ λ (id : A) →
  ∃ λ (_⁻¹ : A → A) →
  Erased
    (Is-set A ⊗
     (∀ x → (id ∘ x) ≡ x) ⊗
     (∀ x → (x ∘ id) ≡ x) ⊗
     (∀ x y z → (x ∘ (y ∘ z)) ≡ ((x ∘ y) ∘ z)) ⊗
     (∀ x → ((x ⁻¹) ∘ x) ≡ id) ⊗
     (∀ x → (x ∘ (x ⁻¹)) ≡ id))
Groupᴱ-as-Σ =
  Eq.↔→≃
    (λ G → let open Groupᴱ G in
         Carrier
       , _∘_
       , id
       , _⁻¹
       , [ ( Carrier-is-set
           , left-identity
           , right-identity
           , assoc
           , left-inverse
           , right-inverse
           )
         ])
    (λ { (_ , _ , _ , _ , [ _ ]) → _ })
    (λ { (_ , _ , _ , _ , [ _ ]) → refl _ })
    refl

------------------------------------------------------------------------
-- A conversion function

-- Groups with non-erased proofs can be converted into groups with
-- erased proofs.

Group→Groupᴱ : Group g → Groupᴱ g
Group→Groupᴱ G = record
  { Carrier        = Carrier
  ; Carrier-is-set = Carrier-is-set
  ; _∘_            = _∘_
  ; id             = id
  ; _⁻¹            = _⁻¹
  ; left-identity  = left-identity
  ; right-identity = right-identity
  ; assoc          = assoc
  ; left-inverse   = left-inverse
  ; right-inverse  = right-inverse
  }
  where
  open Group G

-- In erased contexts Groupᴱ g is equivalent to Group g.

@0 Groupᴱ≃Group : Groupᴱ g ≃ Group g
Groupᴱ≃Group = Eq.↔→≃ _ Group→Groupᴱ refl refl

------------------------------------------------------------------------
-- Group homomorphisms and isomorphisms

-- Group homomorphisms (generalised to several kinds of underlying
-- "functions").

record Homomorphic (k : Kind) (G₁ : Groupᴱ g₁) (G₂ : Groupᴱ g₂) :
                   Type (g₁ ⊔ g₂) where
  private
    module G₁ = Groupᴱ G₁
    module G₂ = Groupᴱ G₂

  field
    related : G₁.Carrier ↝[ k ] G₂.Carrier

  to : G₁.Carrier → G₂.Carrier
  to = to-implication related

  field
    @0 homomorphic :
      ∀ x y → to (x G₁.∘ y) ≡ to x G₂.∘ to y

open Homomorphic public using (related; homomorphic)
open Homomorphic using (to)

-- The type of (generalised) group homomorphisms can be expressed
-- using a nested Σ-type.

Homomorphic-as-Σ :
  {G₁ : Groupᴱ g₁} {G₂ : Groupᴱ g₂} →
  Homomorphic k G₁ G₂ ≃
  let module G₁ = Groupᴱ G₁
      module G₂ = Groupᴱ G₂
  in
  ∃ λ (f : G₁.Carrier ↝[ k ] G₂.Carrier) →
    Erased
      (∀ x y →
       to-implication f (x G₁.∘ y) ≡
       to-implication f x G₂.∘ to-implication f y)
Homomorphic-as-Σ =
  Eq.↔→≃
    (λ G₁↝G₂ → G₁↝G₂ .related , [ G₁↝G₂ .homomorphic ])
    (λ { (_ , [ _ ]) → _ })
    (λ { (_ , [ _ ]) → refl _ })
    refl

-- A variant of Homomorphic.

infix 4 _↝[_]ᴳ_

_↝[_]ᴳ_ : Groupᴱ g₁ → Kind → Groupᴱ g₂ → Type (g₁ ⊔ g₂)
_↝[_]ᴳ_ = flip Homomorphic

-- Group homomorphisms.

infix 4 _→ᴳ_

_→ᴳ_ : Groupᴱ g₁ → Groupᴱ g₂ → Type (g₁ ⊔ g₂)
_→ᴳ_ = _↝[ implication ]ᴳ_

-- Group isomorphisms.

infix 4 _≃ᴳ_

_≃ᴳ_ : Groupᴱ g₁ → Groupᴱ g₂ → Type (g₁ ⊔ g₂)
_≃ᴳ_ = _↝[ equivalenceᴱ ]ᴳ_

-- "Functions" of type G₁ ↝[ k ]ᴳ G₂ can be converted to group
-- homomorphisms.

↝ᴳ→→ᴳ : G₁ ↝[ k ]ᴳ G₂ → G₁ →ᴳ G₂
↝ᴳ→→ᴳ f .related     = to f
↝ᴳ→→ᴳ f .homomorphic = f .homomorphic

-- _↝[ k ]ᴳ_ is reflexive.

↝ᴳ-refl : G ↝[ k ]ᴳ G
↝ᴳ-refl         .related         = F.id
↝ᴳ-refl {G} {k} .homomorphic x y =
  to-implication {k = k} F.id (x ∘ y)  ≡⟨ cong (_$ _) $ to-implication-id k ⟩

  x ∘ y                                ≡⟨ sym $ cong₂ (λ f g → f _ ∘ g _)
                                            (to-implication-id k)
                                            (to-implication-id k) ⟩∎
  to-implication {k = k} F.id x ∘
  to-implication {k = k} F.id y        ∎
  where
  open Groupᴱ G

-- _↝[ k ]ᴳ_ is transitive.

↝ᴳ-trans : G₁ ↝[ k ]ᴳ G₂ → G₂ ↝[ k ]ᴳ G₃ → G₁ ↝[ k ]ᴳ G₃
↝ᴳ-trans {G₁} {k} {G₂} {G₃} G₁↝G₂ G₂↝G₃ = λ where
    .related         → G₂↝G₃ .related F.∘ G₁↝G₂ .related
    .homomorphic x y →
      to-implication (G₂↝G₃ .related F.∘ G₁↝G₂ .related) (x G₁.∘ y)  ≡⟨ cong (_$ _) $ to-implication-∘ k ⟩

      to G₂↝G₃ (to G₁↝G₂ (x G₁.∘ y))                                 ≡⟨ cong (to G₂↝G₃) $ homomorphic G₁↝G₂ _ _ ⟩

      to G₂↝G₃ (to G₁↝G₂ x G₂.∘ to G₁↝G₂ y)                          ≡⟨ homomorphic G₂↝G₃ _ _ ⟩

      to G₂↝G₃ (to G₁↝G₂ x) G₃.∘ to G₂↝G₃ (to G₁↝G₂ y)               ≡⟨ sym $ cong₂ (λ f g → f _ G₃.∘ g _)
                                                                          (to-implication-∘ k)
                                                                          (to-implication-∘ k) ⟩∎
      to-implication (G₂↝G₃ .related F.∘ G₁↝G₂ .related) x G₃.∘
      to-implication (G₂↝G₃ .related F.∘ G₁↝G₂ .related) y           ∎
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂
  module G₃ = Groupᴱ G₃

-- _≃ᴳ_ is symmetric.

≃ᴳ-sym : G₁ ≃ᴳ G₂ → G₂ ≃ᴳ G₁
≃ᴳ-sym {G₁} {G₂} G₁≃G₂ = λ where
    .related         → inverse (G₁≃G₂ .related)
    .homomorphic x y → _≃ᴱ_.injective (G₁≃G₂ .related)
      (to G₁≃G₂ (_≃ᴱ_.from (G₁≃G₂ .related) (x G₂.∘ y))  ≡⟨ _≃ᴱ_.right-inverse-of (G₁≃G₂ .related) _ ⟩

       x G₂.∘ y                                          ≡⟨ sym $ cong₂ G₂._∘_
                                                              (_≃ᴱ_.right-inverse-of (G₁≃G₂ .related) _)
                                                              (_≃ᴱ_.right-inverse-of (G₁≃G₂ .related) _) ⟩
       to G₁≃G₂ (_≃ᴱ_.from (G₁≃G₂ .related) x) G₂.∘
       to G₁≃G₂ (_≃ᴱ_.from (G₁≃G₂ .related) y)           ≡⟨ sym $ G₁≃G₂ .homomorphic _ _ ⟩∎

       to G₁≃G₂
         (_≃ᴱ_.from (G₁≃G₂ .related) x G₁.∘
          _≃ᴱ_.from (G₁≃G₂ .related) y)                  ∎)
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

-- Group homomorphisms preserve identity elements.

@0 →ᴳ-id :
  (G₁↝G₂ : G₁ ↝[ k ]ᴳ G₂) →
  to G₁↝G₂ (Groupᴱ.id G₁) ≡ Groupᴱ.id G₂
→ᴳ-id {G₁} {G₂} G₁↝G₂ =
  G₂.idempotent⇒≡id
    (to G₁↝G₂ G₁.id G₂.∘ to G₁↝G₂ G₁.id  ≡⟨ sym $ G₁↝G₂ .homomorphic _ _ ⟩
     to G₁↝G₂ (G₁.id G₁.∘ G₁.id)         ≡⟨ cong (to G₁↝G₂) $ G₁.left-identity _ ⟩∎
     to G₁↝G₂ G₁.id                      ∎)
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

-- Group homomorphisms are homomorphic with respect to the inverse
-- operators.

@0 →ᴳ-⁻¹ :
  ∀ (G₁↝G₂ : G₁ ↝[ k ]ᴳ G₂) x →
  to G₁↝G₂ (Groupᴱ._⁻¹ G₁ x) ≡ Groupᴱ._⁻¹ G₂ (to G₁↝G₂ x)
→ᴳ-⁻¹ {G₁} {G₂} G₁↝G₂ x = G₂.⁻¹∘≡id→≡
  (to G₁↝G₂ x G₂.⁻¹ G₂.⁻¹ G₂.∘ to G₁↝G₂ (x G₁.⁻¹)  ≡⟨ cong (G₂._∘ to G₁↝G₂ (x G₁.⁻¹)) $ G₂.involutive _ ⟩
   to G₁↝G₂ x G₂.∘ to G₁↝G₂ (x G₁.⁻¹)              ≡⟨ sym $ G₁↝G₂ .homomorphic _ _ ⟩
   to G₁↝G₂ (x G₁.∘ x G₁.⁻¹)                       ≡⟨ cong (to G₁↝G₂) (G₁.right-inverse _) ⟩
   to G₁↝G₂ G₁.id                                  ≡⟨ →ᴳ-id G₁↝G₂ ⟩∎
   G₂.id                                           ∎)
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

-- Group homomorphisms are homomorphic with respect to exponentiation.

@0 →ᴳ-^ :
  ∀ (G₁↝G₂ : G₁ ↝[ k ]ᴳ G₂) x i →
  to G₁↝G₂ (Groupᴱ._^_ G₁ x i) ≡
  Groupᴱ._^_ G₂ (to G₁↝G₂ x) i
→ᴳ-^ {G₁} {G₂} G₁↝G₂ x = lemma₂
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

  lemma₁ : ∀ n → to G₁↝G₂ (y G₁.^+ n) ≡ to G₁↝G₂ y G₂.^+ n
  lemma₁ zero =
    to G₁↝G₂ G₁.id  ≡⟨ →ᴳ-id G₁↝G₂ ⟩∎
    G₂.id    ∎
  lemma₁ {y} (suc n) =
    to G₁↝G₂ (y G₁.∘ y G₁.^+ n)           ≡⟨ G₁↝G₂ .homomorphic _ _ ⟩
    to G₁↝G₂ y G₂.∘ to G₁↝G₂ (y G₁.^+ n)  ≡⟨ cong (_ G₂.∘_) $ lemma₁ n ⟩∎
    to G₁↝G₂ y G₂.∘ to G₁↝G₂ y G₂.^+ n    ∎

  lemma₂ : ∀ i → to G₁↝G₂ (x G₁.^ i) ≡ to G₁↝G₂ x G₂.^ i
  lemma₂ (+ n)    = lemma₁ n
  lemma₂ -[1+ n ] =
    to G₁↝G₂ ((x G₁.⁻¹) G₁.^+ suc n)  ≡⟨ lemma₁ (suc n) ⟩
    to G₁↝G₂ (x G₁.⁻¹) G₂.^+ suc n    ≡⟨ cong (G₂._^+ suc n) $ →ᴳ-⁻¹ G₁↝G₂ _ ⟩∎
    (to G₁↝G₂ x G₂.⁻¹) G₂.^+ suc n    ∎

-- Group equality can be expressed in terms of equality of pairs of
-- carrier types and binary operators (assuming function
-- extensionality).

@0 ≡≃,∘≡,∘ :
  {G₁ G₂ : Groupᴱ g} →
  Extensionality g g →
  let module G₁ = Groupᴱ G₁
      module G₂ = Groupᴱ G₂
  in
  (G₁ ≡ G₂) ≃
  (_≡_ {A = ∃ λ A → A → A → A}
     (G₁.Carrier , G₁._∘_) (G₂.Carrier , G₂._∘_))
≡≃,∘≡,∘ {g} {G₁} {G₂} ext =
  G₁ ≡ G₂                                                    ↝⟨ inverse $ Eq.≃-≡ Groupᴱ≃ ⟩

  ((G₁.Carrier , G₁._∘_) , _) ≡ ((G₂.Carrier , G₂._∘_) , _)  ↔⟨ (inverse $
                                                                 ignore-propositional-component $
                                                                 The-rest-propositional _) ⟩□
  (G₁.Carrier , G₁._∘_) ≡ (G₂.Carrier , G₂._∘_)              □
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

  Carrier-∘ = ∃ λ (C : Type g) → (C → C → C)

  The-rest : Carrier-∘ → Type g
  The-rest (C , _∘_) =
    ∃ λ ((id , _⁻¹) : C ⊗ (C → C)) →
      Erased
        (Is-set C ⊗
        (∀ x → (id ∘ x) ≡ x) ⊗
        (∀ x → (x ∘ id) ≡ x) ⊗
        (∀ x y z → (x ∘ (y ∘ z)) ≡ ((x ∘ y) ∘ z)) ⊗
        (∀ x → ((x ⁻¹) ∘ x) ≡ id) ⊗
        (∀ x → (x ∘ (x ⁻¹)) ≡ id))

  Groupᴱ≃ : Groupᴱ g ≃ Σ Carrier-∘ The-rest
  Groupᴱ≃ = Eq.↔→≃
    (λ G → let open Groupᴱ G in
         (Carrier , _∘_)
       , (id , _⁻¹)
       , [ (Carrier-is-set , left-identity , right-identity , assoc ,
            left-inverse , right-inverse)
         ])
    (λ { (_ , _ , [ _ ]) → _ })
    (λ { (_ , _ , [ _ ]) → refl _ })
    refl

  The-rest-propositional : ∀ C → Is-proposition (The-rest C)
  The-rest-propositional C R₁@(_ , [ _ ]) R₂@(_ , [ _ ]) =
    Σ-≡,≡→≡
      (cong₂ _,_ id-unique inverse-unique)
      ((BC.H-level-Erased 1
          (×-closure 1 (H-level-propositional ext 2) $
           ×-closure 1 (Π-closure ext 1 λ _ →
                        G₂′.Carrier-is-set) $
           ×-closure 1 (Π-closure ext 1 λ _ →
                        G₂′.Carrier-is-set) $
           ×-closure 1 (Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        Π-closure ext 1 λ _ →
                        G₂′.Carrier-is-set) $
           ×-closure 1 (Π-closure ext 1 λ _ →
                        G₂′.Carrier-is-set) $
                       (Π-closure ext 1 λ _ →
                        G₂′.Carrier-is-set)))
         _ _)
    where
    module G₁′ = Groupᴱ (_≃_.from Groupᴱ≃ (C , R₁))
    module G₂′ = Groupᴱ (_≃_.from Groupᴱ≃ (C , R₂))

    id-unique : G₁′.id ≡ G₂′.id
    id-unique = G₂′.idempotent⇒≡id (G₁′.left-identity G₁′.id)

    inverse-unique : G₁′._⁻¹ ≡ G₂′._⁻¹
    inverse-unique = apply-ext ext λ x → G₂′.⁻¹-unique-right
      (x G₁′.∘ x G₁′.⁻¹  ≡⟨ G₁′.right-inverse _ ⟩
       G₁′.id            ≡⟨ id-unique ⟩∎
       G₂′.id            ∎)

-- Group isomorphisms are equivalent to equalities (assuming function
-- extensionality and univalence).

@0 ≃ᴳ≃≡ :
  {G₁ G₂ : Groupᴱ g} →
  Extensionality g g →
  Univalence g →
  (G₁ ≃ᴳ G₂) ≃ (G₁ ≡ G₂)
≃ᴳ≃≡ {G₁} {G₂} ext univ =
  G₁ ≃ᴳ G₂                                                              ↝⟨ Homomorphic-as-Σ ⟩

  (∃ λ (eq : G₁.Carrier ≃ᴱ G₂.Carrier) →
     Erased
       (∀ x y →
        _≃ᴱ_.to eq (x G₁.∘ y) ≡ _≃ᴱ_.to eq x G₂.∘ _≃ᴱ_.to eq y))        ↔⟨ Σ-cong (inverse EEq.≃≃≃ᴱ) (λ _ → erased Erased↔) ⟩

  (∃ λ (eq : G₁.Carrier ≃ G₂.Carrier) →
     ∀ x y →
     _≃_.to eq (x G₁.∘ y) ≡ _≃_.to eq x G₂.∘ _≃_.to eq y)               ↝⟨ (∃-cong λ eq → Π-cong ext eq λ _ → Π-cong ext eq λ _ →
                                                                            ≡⇒≃ $ sym $ cong (_≡ _≃_.to eq _ G₂.∘ _≃_.to eq _) $ cong (_≃_.to eq) $
                                                                            cong₂ G₁._∘_
                                                                              (_≃_.left-inverse-of eq _)
                                                                              (_≃_.left-inverse-of eq _)) ⟩
  (∃ λ (eq : G₁.Carrier ≃ G₂.Carrier) →
     ∀ x y → _≃_.to eq (_≃_.from eq x G₁.∘ _≃_.from eq y) ≡ x G₂.∘ y)   ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ →
                                                                            Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (eq : G₁.Carrier ≃ G₂.Carrier) →
     ∀ x →
     (λ y → _≃_.to eq (_≃_.from eq x G₁.∘ _≃_.from eq y)) ≡ (x G₂.∘_))  ↝⟨ (∃-cong λ _ →
                                                                            Eq.extensionality-isomorphism ext) ⟩
  (∃ λ (eq : G₁.Carrier ≃ G₂.Carrier) →
     (λ x y → _≃_.to eq (_≃_.from eq x G₁.∘ _≃_.from eq y)) ≡ G₂._∘_)   ↝⟨ (∃-cong λ eq → ≡⇒≃ $ cong (_≡ _) $ sym $ lemma eq) ⟩

  (∃ λ (eq : G₁.Carrier ≃ G₂.Carrier) →
     subst (λ A → A → A → A) (≃⇒≡ univ eq) G₁._∘_ ≡ G₂._∘_)             ↝⟨ (Σ-cong (inverse $ ≡≃≃ univ) λ _ → Eq.id) ⟩

  (∃ λ (eq : G₁.Carrier ≡ G₂.Carrier) →
     subst (λ A → A → A → A) eq G₁._∘_ ≡ G₂._∘_)                        ↔⟨ B.Σ-≡,≡↔≡ ⟩

  ((G₁.Carrier , G₁._∘_) ≡ (G₂.Carrier , G₂._∘_))                       ↝⟨ inverse $ ≡≃,∘≡,∘ ext ⟩□

  G₁ ≡ G₂                                                               □
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

  lemma : ∀ _ → _
  lemma = λ eq → apply-ext ext λ x → apply-ext ext λ y →
    subst (λ A → A → A → A) (≃⇒≡ univ eq) G₁._∘_ x y      ≡⟨ cong (_$ y) subst-→ ⟩

    subst (λ A → A → A) (≃⇒≡ univ eq)
      (subst P.id (sym (≃⇒≡ univ eq)) x G₁.∘_) y          ≡⟨ subst-→ ⟩

    subst P.id (≃⇒≡ univ eq)
      (subst P.id (sym (≃⇒≡ univ eq)) x G₁.∘
       subst P.id (sym (≃⇒≡ univ eq)) y)                  ≡⟨ cong₂ (λ f g → f (g x G₁.∘ g y))
                                                               (trans (apply-ext ext λ _ → subst-id-in-terms-of-≡⇒↝ equivalence) $
                                                                cong _≃_.to $ _≃_.right-inverse-of (≡≃≃ univ) _)
                                                               (trans (apply-ext ext λ _ → subst-id-in-terms-of-inverse∘≡⇒↝ equivalence) $
                                                                cong _≃_.from $ _≃_.right-inverse-of (≡≃≃ univ) _) ⟩∎
    _≃_.to eq (_≃_.from eq x G₁.∘ _≃_.from eq y)          ∎

------------------------------------------------------------------------
-- Abelian groups

-- The property of being abelian.

Abelian : Groupᴱ g → Type g
Abelian G =
  Erased (∀ x y → x ∘ y ≡ y ∘ x)
  where
  open Groupᴱ G

-- If two groups are isomorphic, and one is abelian, then the other
-- one is abelian.

@0 ≃ᴳ→Abelian→Abelian : G₁ ≃ᴳ G₂ → Abelian G₁ → Abelian G₂
≃ᴳ→Abelian→Abelian {G₁} {G₂} G₁≃G₂ ∘-comm =
  [ (λ x y →
       _≃ᴱ_.injective (G₂≃G₁ .related)
         (to G₂≃G₁ (x G₂.∘ y)         ≡⟨ G₂≃G₁ .homomorphic _ _ ⟩
          to G₂≃G₁ x G₁.∘ to G₂≃G₁ y  ≡⟨ ∘-comm .erased _ _ ⟩
          to G₂≃G₁ y G₁.∘ to G₂≃G₁ x  ≡⟨ sym $ G₂≃G₁ .homomorphic _ _ ⟩∎
          to G₂≃G₁ (y G₂.∘ x)         ∎))
  ]
  where
  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

  G₂≃G₁ = ≃ᴳ-sym G₁≃G₂

------------------------------------------------------------------------
-- A group construction

-- The direct product of two groups.

infixr 2 _×_

_×_ : Groupᴱ g₁ → Groupᴱ g₂ → Groupᴱ (g₁ ⊔ g₂)
G₁ × G₂ = λ where
    .Carrier          → G₁.Carrier ⊗ G₂.Carrier
    .Carrier-is-set   → ×-closure 2 G₁.Carrier-is-set G₂.Carrier-is-set
    ._∘_              → Σ-zip G₁._∘_ G₂._∘_
    .id               → G₁.id , G₂.id
    ._⁻¹              → Σ-map G₁._⁻¹ G₂._⁻¹
    .left-identity _  → cong₂ _,_
                          (G₁.left-identity _) (G₂.left-identity _)
    .right-identity _ → cong₂ _,_
                          (G₁.right-identity _) (G₂.right-identity _)
    .assoc _ _ _      → cong₂ _,_ (G₁.assoc _ _ _) (G₂.assoc _ _ _)
    .left-inverse _   → cong₂ _,_
                          (G₁.left-inverse _) (G₂.left-inverse _)
    .right-inverse _  → cong₂ _,_
                          (G₁.right-inverse _) (G₂.right-inverse _)
  where
  open Groupᴱ

  module G₁ = Groupᴱ G₁
  module G₂ = Groupᴱ G₂

-- The direct product operator preserves group homomorphisms.

↝-× :
  G₁ ↝[ k ]ᴳ G₂ → G₁′ ↝[ k ]ᴳ G₂′ →
  (G₁ × G₁′) ↝[ k ]ᴳ (G₂ × G₂′)
↝-× {G₁} {k} {G₂} {G₁′} {G₂′} G₁↝G₂ G₁′↝G₂′ = λ where
  .related →
    G₁↝G₂ .related ×-cong G₁′↝G₂′ .related
  .homomorphic x@(x₁ , x₂) y@(y₁ , y₂) →
    to-implication (G₁↝G₂ .related ×-cong G₁′↝G₂′ .related)
      (Σ-zip (Groupᴱ._∘_ G₁) (Groupᴱ._∘_ G₁′) x y)                 ≡⟨ cong (_$ _) $ to-implication-×-cong k ⟩

    Σ-map (to G₁↝G₂) (to G₁′↝G₂′)
      (Σ-zip (Groupᴱ._∘_ G₁) (Groupᴱ._∘_ G₁′) x y)                 ≡⟨⟩

    to G₁↝G₂   (Groupᴱ._∘_ G₁  x₁ y₁) ,
    to G₁′↝G₂′ (Groupᴱ._∘_ G₁′ x₂ y₂)                              ≡⟨ cong₂ _,_
                                                                        (G₁↝G₂   .homomorphic _ _)
                                                                        (G₁′↝G₂′ .homomorphic _ _) ⟩
    Groupᴱ._∘_ G₂  (to G₁↝G₂   x₁) (to G₁↝G₂   y₁) ,
    Groupᴱ._∘_ G₂′ (to G₁′↝G₂′ x₂) (to G₁′↝G₂′ y₂)                 ≡⟨⟩

    Groupᴱ._∘_ (G₂ × G₂′)
      (to G₁↝G₂ x₁ , to G₁′↝G₂′ x₂)
      (to G₁↝G₂ y₁ , to G₁′↝G₂′ y₂)                                ≡⟨ sym $ cong₂ (λ f g → Groupᴱ._∘_ (G₂ × G₂′) (f _) (g _))
                                                                        (to-implication-×-cong k)
                                                                        (to-implication-×-cong k) ⟩∎
    Groupᴱ._∘_ (G₂ × G₂′)
      (to-implication (G₁↝G₂ .related ×-cong G₁′↝G₂′ .related) x)
      (to-implication (G₁↝G₂ .related ×-cong G₁′↝G₂′ .related) y)  ∎

-- Exponentiation for the direct product of G₁ and G₂ can be expressed
-- in terms of exponentiation for G₁ and exponentiation for G₂.

@0 ^-× :
  ∀ (G₁ : Groupᴱ g₁) (G₂ : Groupᴱ g₂) {x y} i →
  Groupᴱ._^_ (G₁ × G₂) (x , y) i ≡
  (Groupᴱ._^_ G₁ x i , Groupᴱ._^_ G₂ y i)
^-× G₁ G₂ = helper
  where
  module G₁  = Groupᴱ G₁
  module G₂  = Groupᴱ G₂
  module G₁₂ = Groupᴱ (G₁ × G₂)

  +-helper : ∀ n → (x , y) G₁₂.^+ n ≡ (x G₁.^+ n , y G₂.^+ n)
  +-helper         zero    = refl _
  +-helper {x} {y} (suc n) =
    (x , y) G₁₂.∘ (x , y) G₁₂.^+ n         ≡⟨ cong (_ G₁₂.∘_) $ +-helper n ⟩
    (x , y) G₁₂.∘ (x G₁.^+ n , y G₂.^+ n)  ≡⟨⟩
    (x G₁.∘ x G₁.^+ n , y G₂.∘ y G₂.^+ n)  ∎

  helper : ∀ i → (x , y) G₁₂.^ i ≡ (x G₁.^ i , y G₂.^ i)
  helper (+ n)    = +-helper n
  helper -[1+ n ] = +-helper (suc n)

------------------------------------------------------------------------
-- The centre of a group

-- Centre ext G is the centre of the group G, sometimes denoted Z(G),
-- but expressed using erasure.

Centre :
  @0 Extensionality g g →
  Groupᴱ g → Groupᴱ g
Centre ext G = λ where
    .Carrier        → ∃ λ (x : Carrier) → Erased (∀ y → x ∘ y ≡ y ∘ x)
    .Carrier-is-set → Σ-closure 2 Carrier-is-set λ _ →
                      BC.H-level-Erased 2
                        (Π-closure ext 2 λ _ →
                         mono₁ 2 Carrier-is-set)
    ._∘_            → Σ-zip _∘_ λ {x y} →
                      Erased.zip
                        (λ hyp₁ hyp₂ z →
                           (x ∘ y) ∘ z  ≡⟨ sym $ assoc _ _ _ ⟩
                           x ∘ (y ∘ z)  ≡⟨ cong (x ∘_) $ hyp₂ z ⟩
                           x ∘ (z ∘ y)  ≡⟨ assoc _ _ _ ⟩
                           (x ∘ z) ∘ y  ≡⟨ cong (_∘ y) $ hyp₁ z ⟩
                           (z ∘ x) ∘ y  ≡⟨ sym $ assoc _ _ _ ⟩∎
                           z ∘ (x ∘ y)  ∎)
    .id             → id
                    , [ (λ x →
                           id ∘ x  ≡⟨ left-identity _ ⟩
                           x       ≡⟨ sym $ right-identity _ ⟩∎
                           x ∘ id  ∎)
                      ]
    ._⁻¹            → Σ-map _⁻¹ λ {x} →
                      Erased.map
                        (λ hyp y →
                           x ⁻¹ ∘ y        ≡⟨ cong (x ⁻¹ ∘_) $ sym $ involutive _ ⟩
                           x ⁻¹ ∘ y ⁻¹ ⁻¹  ≡⟨ sym ∘⁻¹ ⟩
                           (y ⁻¹ ∘ x) ⁻¹   ≡⟨ cong _⁻¹ $ sym $ hyp (y ⁻¹) ⟩
                           (x ∘ y ⁻¹) ⁻¹   ≡⟨ ∘⁻¹ ⟩
                           y ⁻¹ ⁻¹ ∘ x ⁻¹  ≡⟨ cong (_∘ x ⁻¹) $ involutive _ ⟩∎
                           y ∘ x ⁻¹        ∎)
    .left-identity  → λ _ →     Σ-≡,≡→≡ (left-identity _)  (prop _ _)
    .right-identity → λ _ →     Σ-≡,≡→≡ (right-identity _) (prop _ _)
    .assoc          → λ _ _ _ → Σ-≡,≡→≡ (assoc _ _ _)      (prop _ _)
    .left-inverse   → λ _ →     Σ-≡,≡→≡ (left-inverse _)   (prop _ _)
    .right-inverse  → λ _ →     Σ-≡,≡→≡ (right-inverse _)  (prop _ _)
  where
  open Groupᴱ G

  @0 prop :
    {f g : Carrier → Carrier} →
    Is-proposition (Erased (∀ x → f x ≡ g x))
  prop =
    BC.H-level-Erased 1
      (Π-closure ext 1 λ _ → Carrier-is-set)

-- The centre of an abelian group is isomorphic to the group (if
-- []-cong is available).

Abelian→Centre≃ :
  []-cong-axiomatisation g →
  (@0 ext : Extensionality g g)
  (G : Groupᴱ g) →
  Abelian G → Centre ext G ≃ᴳ G
Abelian→Centre≃ ax ext G abelian = ≃ᴳ-sym λ where
    .Homomorphic.related →
      Carrier                                             ↔⟨ inverse (drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ contr) ⟩□
      (∃ λ (x : Carrier) → Erased (∀ y → x ∘ y ≡ y ∘ x))  □
    .Homomorphic.homomorphic _ _ →
      cong (_ ,_) (mono₁ 0 contr _ _)
  where
  open Erased.[]-cong₁ ax
  open Groupᴱ G

  contr : Contractible (Erased (∀ y → x ∘ y ≡ y ∘ x))
  contr =
    H-level-Erased 0
      (Π-closure ext 0 λ _ →
       propositional⇒inhabited⇒contractible Carrier-is-set
         (abelian .erased _ _))

------------------------------------------------------------------------
-- Converting to another carrier set

-- Given a group and an equivalence between the group's carrier set
-- and a type A one can form a group where the carrier set is A.

with-other-carrier :
  {A : Type a}
  (G : Groupᴱ g) → Groupᴱ.Carrier G ≃ A → Groupᴱ a
with-other-carrier {a} {A} G ≃A = G′
  where
  open Groupᴱ G
  open _≃_ ≃A renaming (to to to′)

  G′ : Groupᴱ a
  G′ .Groupᴱ.Carrier         = A
  G′ .Groupᴱ.Carrier-is-set  = H-level-cong _ 2 ≃A Carrier-is-set
  G′ .Groupᴱ._∘_ x y         = to′ (from x ∘ from y)
  G′ .Groupᴱ.id              = to′ id
  G′ .Groupᴱ._⁻¹ x           = to′ (from x ⁻¹)
  G′ .Groupᴱ.left-identity x =
    to′ (from (to′ id) ∘ from x)  ≡⟨ cong (to′ P.∘ (_∘ from _)) $ left-inverse-of _ ⟩
    to′ (id ∘ from x)             ≡⟨ cong to′ $ left-identity _ ⟩
    to′ (from x)                  ≡⟨ right-inverse-of _ ⟩∎
    x                             ∎
  G′ .Groupᴱ.right-identity x =
    to′ (from x ∘ from (to′ id))  ≡⟨ cong (to′ P.∘ (from _ ∘_)) $ left-inverse-of _ ⟩
    to′ (from x ∘ id)             ≡⟨ cong to′ $ right-identity _ ⟩
    to′ (from x)                  ≡⟨ right-inverse-of _ ⟩∎
    x                             ∎
  G′ .Groupᴱ.assoc x y z =
    to′ (from x ∘ from (to′ (from y ∘ from z)))  ≡⟨ cong (to′ P.∘ (from _ ∘_)) $ left-inverse-of _ ⟩
    to′ (from x ∘ (from y ∘ from z))             ≡⟨ cong to′ $ assoc _ _ _ ⟩
    to′ ((from x ∘ from y) ∘ from z)             ≡⟨ cong (to′ P.∘ (_∘ from _)) $ sym $ left-inverse-of _ ⟩
    to′ (from (to′ (from x ∘ from y)) ∘ from z)  ∎
  G′ .Groupᴱ.left-inverse x =
    to′ (from (to′ (from x ⁻¹)) ∘ from x)  ≡⟨ cong (to′ P.∘ (_∘ from _)) $ left-inverse-of _ ⟩
    to′ (from x ⁻¹ ∘ from x)               ≡⟨ cong to′ $ left-inverse _ ⟩
    to′ id                                 ∎
  G′ .Groupᴱ.right-inverse x =
    to′ (from x ∘ from (to′ (from x ⁻¹)))  ≡⟨ cong (to′ P.∘ (from _ ∘_)) $ left-inverse-of _ ⟩
    to′ (from x ∘ from x ⁻¹)               ≡⟨ cong to′ $ right-inverse _ ⟩
    to′ id                                 ∎

-- The resulting group has the correct carrier set.

_ :
  {G : Groupᴱ g} {≃A : Groupᴱ.Carrier G ≃ A} →
  Groupᴱ.Carrier (with-other-carrier G ≃A) ≡ A
_ = refl _

------------------------------------------------------------------------
-- Converting groupoids to groups

-- For each object x in a groupoid for which x ∼ x is a set one
-- obtains a group.

group-for :
  (G : Groupoid g₁ g₂)
  (x : Groupoid.Object G) →
  Is-set (Groupoid._∼_ G x x) →
  Groupᴱ g₂
group-for {g₂} G x set = G′
  where
  open Groupoid G

  G′ : Groupᴱ g₂
  G′ .Groupᴱ.Carrier        = x ∼ x
  G′ .Groupᴱ.Carrier-is-set = set
  G′ .Groupᴱ._∘_            = _∘_
  G′ .Groupᴱ.id             = id
  G′ .Groupᴱ._⁻¹            = _⁻¹
  G′ .Groupᴱ.left-identity  = left-identity
  G′ .Groupᴱ.right-identity = right-identity
  G′ .Groupᴱ.assoc          = assoc
  G′ .Groupᴱ.left-inverse   = left-inverse
  G′ .Groupᴱ.right-inverse  = right-inverse
