------------------------------------------------------------------------
-- Groups
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

import Equality.Path as P

module Group
  {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Prelude as P hiding (id; _∘_; _^_) renaming (_×_ to _⊗_)

import Bijection equality-with-J as B
open import Equality.Path.Isomorphisms eq hiding (univ)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import Groupoid equality-with-J as G using (Groupoid)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Integer.Basics equality-with-J as Int using (ℤ; +_; -[1+_])
open import H-level.Truncation.Propositional eq as T using (∥_∥)
open import Univalence-axiom equality-with-J

private
  variable
    a g₁ g₁′ g₂ g₂′ g₃ : Level
    A                  : Type a
    g x y z            : A
    k                  : Kind

------------------------------------------------------------------------
-- Groups

-- Groups.
--
-- Note that the carrier type is required to be a set (following the
-- HoTT book).

record Group g : Type (lsuc g) where
  infix  8 _⁻¹
  infixr 7 _∘_

  field
    Carrier        : Type g
    Carrier-is-set : Is-set Carrier
    _∘_            : Carrier → Carrier → Carrier
    id             : Carrier
    _⁻¹            : Carrier → Carrier
    left-identity  : ∀ x → (id ∘ x) ≡ x
    right-identity : ∀ x → (x ∘ id) ≡ x
    assoc          : ∀ x y z → (x ∘ (y ∘ z)) ≡ ((x ∘ y) ∘ z)
    left-inverse   : ∀ x → ((x ⁻¹) ∘ x) ≡ id
    right-inverse  : ∀ x → (x ∘ (x ⁻¹)) ≡ id

  -- Groups are groupoids.

  groupoid : Groupoid lzero g
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

  open Groupoid groupoid public
    hiding (Object; _∼_; id; _∘_; _⁻¹; left-identity; right-identity;
            assoc; left-inverse; right-inverse)

private
  variable
    G G₁ G₁′ G₂ G₂′ G₃ : Group g

-- The type of groups can be expressed using a nested Σ-type.

Group-as-Σ :
  Group g ≃
  ∃ λ (A : Set g) →
  let A = ⌞ A ⌟ in
  ∃ λ (_∘_ : A → A → A) →
  ∃ λ (id : A) →
  ∃ λ (_⁻¹ : A → A) →
    (∀ x → (id ∘ x) ≡ x) ⊗
    (∀ x → (x ∘ id) ≡ x) ⊗
    (∀ x y z → (x ∘ (y ∘ z)) ≡ ((x ∘ y) ∘ z)) ⊗
    (∀ x → ((x ⁻¹) ∘ x) ≡ id) ⊗
    (∀ x → (x ∘ (x ⁻¹)) ≡ id)
Group-as-Σ =
  Eq.↔→≃
    (λ G → let open Group G in
         (Carrier , Carrier-is-set)
       , _∘_
       , id
       , _⁻¹
       , left-identity
       , right-identity
       , assoc
       , left-inverse
       , right-inverse)
    _
    refl
    refl

------------------------------------------------------------------------
-- Group homomorphisms and isomorphisms

-- Group homomorphisms (generalised to several kinds of underlying
-- "functions").

record Homomorphic (k : Kind) (G₁ : Group g₁) (G₂ : Group g₂) :
                   Type (g₁ ⊔ g₂) where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  field
    related : G₁.Carrier ↝[ k ] G₂.Carrier

  to : G₁.Carrier → G₂.Carrier
  to = to-implication related

  field
    homomorphic :
      ∀ x y → to (x G₁.∘ y) ≡ to x G₂.∘ to y

open Homomorphic

-- The type of (generalised) group homomorphisms can be expressed
-- using a nested Σ-type.

Homomorphic-as-Σ :
  {G₁ : Group g₁} {G₂ : Group g₂} →
  Homomorphic k G₁ G₂ ≃
  let module G₁ = Group G₁
      module G₂ = Group G₂
  in
  ∃ λ (f : G₁.Carrier ↝[ k ] G₂.Carrier) →
    ∀ x y →
    to-implication f (x G₁.∘ y) ≡
    to-implication f x G₂.∘ to-implication f y
Homomorphic-as-Σ =
  Eq.↔→≃
    (λ G₁↝G₂ → G₁↝G₂ .related , G₁↝G₂ .homomorphic)
    _
    refl
    refl

-- A variant of Homomorphic.

infix 4 _↝[_]ᴳ_ _→ᴳ_ _≃ᴳ_

_↝[_]ᴳ_ : Group g₁ → Kind → Group g₂ → Type (g₁ ⊔ g₂)
_↝[_]ᴳ_ = flip Homomorphic

-- Group homomorphisms.

_→ᴳ_ : Group g₁ → Group g₂ → Type (g₁ ⊔ g₂)
_→ᴳ_ = _↝[ implication ]ᴳ_

-- Group isomorphisms.

_≃ᴳ_ : Group g₁ → Group g₂ → Type (g₁ ⊔ g₂)
_≃ᴳ_ = _↝[ equivalence ]ᴳ_

-- _↝[ k ]ᴳ_ is reflexive.

↝ᴳ-refl : G ↝[ k ]ᴳ G
↝ᴳ-refl                 .related         = F.id
↝ᴳ-refl {G = G} {k = k} .homomorphic x y =
  to-implication {k = k} F.id (x ∘ y)  ≡⟨ cong (_$ _) $ to-implication-id k ⟩

  x ∘ y                                ≡⟨ sym $ cong₂ (λ f g → f _ ∘ g _)
                                            (to-implication-id k)
                                            (to-implication-id k) ⟩∎
  to-implication {k = k} F.id x ∘
  to-implication {k = k} F.id y        ∎
  where
  open Group G

-- _↝[ k ]ᴳ_ is transitive.

↝ᴳ-trans : G₁ ↝[ k ]ᴳ G₂ → G₂ ↝[ k ]ᴳ G₃ → G₁ ↝[ k ]ᴳ G₃
↝ᴳ-trans {G₁ = G₁} {k = k} {G₂ = G₂} {G₃ = G₃}
  G₁↝G₂ G₂↝G₃ = λ where
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
  module G₁ = Group G₁
  module G₂ = Group G₂
  module G₃ = Group G₃

-- _≃ᴳ_ is symmetric.

≃ᴳ-sym : G₁ ≃ᴳ G₂ → G₂ ≃ᴳ G₁
≃ᴳ-sym {G₁ = G₁} {G₂ = G₂} G₁≃G₂ = λ where
    .related         → inverse (G₁≃G₂ .related)
    .homomorphic x y → _≃_.injective (G₁≃G₂ .related)
      (to G₁≃G₂ (_≃_.from (G₁≃G₂ .related) (x G₂.∘ y))                   ≡⟨ _≃_.right-inverse-of (G₁≃G₂ .related) _ ⟩

       x G₂.∘ y                                                          ≡⟨ sym $ cong₂ G₂._∘_
                                                                              (_≃_.right-inverse-of (G₁≃G₂ .related) _)
                                                                              (_≃_.right-inverse-of (G₁≃G₂ .related) _) ⟩
       to G₁≃G₂ (_≃_.from (G₁≃G₂ .related) x) G₂.∘
       to G₁≃G₂ (_≃_.from (G₁≃G₂ .related) y)                            ≡⟨ sym $ G₁≃G₂ .homomorphic _ _ ⟩∎

       to G₁≃G₂
         (_≃_.from (G₁≃G₂ .related) x G₁.∘ _≃_.from (G₁≃G₂ .related) y)  ∎)
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

-- Group homomorphisms preserve identity elements.

→ᴳ-id :
  (G₁↝G₂ : G₁ ↝[ k ]ᴳ G₂) →
  to G₁↝G₂ (Group.id G₁) ≡ Group.id G₂
→ᴳ-id {G₁ = G₁} {G₂ = G₂} G₁↝G₂ =
  G₂.idempotent⇒≡id
    (to G₁↝G₂ G₁.id G₂.∘ to G₁↝G₂ G₁.id  ≡⟨ sym $ G₁↝G₂ .homomorphic _ _ ⟩
     to G₁↝G₂ (G₁.id G₁.∘ G₁.id)         ≡⟨ cong (to G₁↝G₂) $ G₁.left-identity _ ⟩∎
     to G₁↝G₂ G₁.id                      ∎)
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

-- Group homomorphisms are homomorphic with respect to the inverse
-- operators.

→ᴳ-⁻¹ :
  ∀ (G₁↝G₂ : G₁ ↝[ k ]ᴳ G₂) x →
  to G₁↝G₂ (Group._⁻¹ G₁ x) ≡ Group._⁻¹ G₂ (to G₁↝G₂ x)
→ᴳ-⁻¹ {G₁ = G₁} {G₂ = G₂} G₁↝G₂ x = G₂.⁻¹∘≡id→≡
  (to G₁↝G₂ x G₂.⁻¹ G₂.⁻¹ G₂.∘ to G₁↝G₂ (x G₁.⁻¹)  ≡⟨ cong (G₂._∘ to G₁↝G₂ (x G₁.⁻¹)) $ G₂.involutive _ ⟩
   to G₁↝G₂ x G₂.∘ to G₁↝G₂ (x G₁.⁻¹)              ≡⟨ sym $ G₁↝G₂ .homomorphic _ _ ⟩
   to G₁↝G₂ (x G₁.∘ x G₁.⁻¹)                       ≡⟨ cong (to G₁↝G₂) (G₁.right-inverse _) ⟩
   to G₁↝G₂ G₁.id                                  ≡⟨ →ᴳ-id G₁↝G₂ ⟩∎
   G₂.id                                           ∎)
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

-- Group homomorphisms are homomorphic with respect to exponentiation.

→ᴳ-^ :
  ∀ (G₁↝G₂ : G₁ ↝[ k ]ᴳ G₂) x i →
  to G₁↝G₂ (Group._^_ G₁ x i) ≡
  Group._^_ G₂ (to G₁↝G₂ x) i
→ᴳ-^ {G₁ = G₁} {G₂ = G₂} G₁↝G₂ x = lemma₂
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

  lemma₁ : ∀ n → to G₁↝G₂ (y G₁.^+ n) ≡ to G₁↝G₂ y G₂.^+ n
  lemma₁ zero =
    to G₁↝G₂ G₁.id  ≡⟨ →ᴳ-id G₁↝G₂ ⟩∎
    G₂.id    ∎
  lemma₁ {y = y} (suc n) =
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
-- carrier types and binary operators.

≡≃,∘≡,∘ :
  {G₁ G₂ : Group g} →
  let module G₁ = Group G₁
      module G₂ = Group G₂
  in
  (G₁ ≡ G₂) ≃ ((G₁.Carrier , G₁._∘_) ≡ (G₂.Carrier , G₂._∘_))
≡≃,∘≡,∘ {g = g} {G₁ = G₁} {G₂ = G₂} =
  G₁ ≡ G₂                                                    ↝⟨ inverse $ Eq.≃-≡ Group≃ ⟩

  ((G₁.Carrier , G₁._∘_) , _) ≡ ((G₂.Carrier , G₂._∘_) , _)  ↔⟨ (inverse $
                                                                 ignore-propositional-component $
                                                                 The-rest-propositional _) ⟩□
  (G₁.Carrier , G₁._∘_) ≡ (G₂.Carrier , G₂._∘_)              □
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

  Carrier-∘ = ∃ λ (C : Type g) → (C → C → C)

  The-rest : Carrier-∘ → Type g
  The-rest (C , _∘_) =
    ∃ λ ((id , _⁻¹) : C ⊗ (C → C)) →
      Is-set C ⊗
      (∀ x → (id ∘ x) ≡ x) ⊗
      (∀ x → (x ∘ id) ≡ x) ⊗
      (∀ x y z → (x ∘ (y ∘ z)) ≡ ((x ∘ y) ∘ z)) ⊗
      (∀ x → ((x ⁻¹) ∘ x) ≡ id) ⊗
      (∀ x → (x ∘ (x ⁻¹)) ≡ id)

  Group≃ : Group g ≃ Σ Carrier-∘ The-rest
  Group≃ = Eq.↔→≃
    (λ G → let open Group G in
         (Carrier , _∘_)
       , (id , _⁻¹)
       , Carrier-is-set , left-identity , right-identity , assoc
       , left-inverse , right-inverse)
    _
    refl
    refl

  The-rest-propositional : ∀ C → Is-proposition (The-rest C)
  The-rest-propositional C R₁ R₂ =
    Σ-≡,≡→≡
      (cong₂ _,_ id-unique inverse-unique)
      ((×-closure 1 (H-level-propositional ext 2) $
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
                     G₂′.Carrier-is-set))
         _ _)
    where
    module G₁′ = Group (_≃_.from Group≃ (C , R₁))
    module G₂′ = Group (_≃_.from Group≃ (C , R₂))

    id-unique : G₁′.id ≡ G₂′.id
    id-unique = G₂′.idempotent⇒≡id (G₁′.left-identity G₁′.id)

    inverse-unique : G₁′._⁻¹ ≡ G₂′._⁻¹
    inverse-unique = apply-ext ext λ x → G₂′.⁻¹-unique-right
      (x G₁′.∘ x G₁′.⁻¹  ≡⟨ G₁′.right-inverse _ ⟩
       G₁′.id            ≡⟨ id-unique ⟩∎
       G₂′.id            ∎)

-- Group isomorphisms are equivalent to equalities (assuming
-- univalence).

≃ᴳ≃≡ :
  {G₁ G₂ : Group g} →
  Univalence g →
  (G₁ ≃ᴳ G₂) ≃ (G₁ ≡ G₂)
≃ᴳ≃≡ {G₁ = G₁} {G₂ = G₂} univ =
  G₁ ≃ᴳ G₂                                                              ↝⟨ Homomorphic-as-Σ ⟩

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

  ((G₁.Carrier , G₁._∘_) ≡ (G₂.Carrier , G₂._∘_))                       ↝⟨ inverse ≡≃,∘≡,∘ ⟩□

  G₁ ≡ G₂                                                               □
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

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
-- Some properties of groups

-- The property of being generated by an element.

Generated-by : (G : Group g) → Group.Carrier G → Type g
Generated-by G g =
  (x : Carrier) → ∥ (∃ λ (i : ℤ) → x ≡ g ^ i) ∥
  where
  open Group G

-- The property of being cyclic.

Cyclic : Group g → Type g
Cyclic G = ∥ ∃ (Generated-by G) ∥

-- The property of being abelian.

Abelian : Group g → Type g
Abelian G =
  ∀ x y → x ∘ y ≡ y ∘ x
  where
  open Group G

-- Cyclic groups are abelian.

Cyclic→Abelian : (G : Group g) → Cyclic G → Abelian G
Cyclic→Abelian G c x y =
  flip (T.rec Carrier-is-set) c          λ (g , gen-by) →
  flip (T.rec Carrier-is-set) (gen-by x) λ (i , x≡) →
  flip (T.rec Carrier-is-set) (gen-by y) λ (j , y≡) →
    x ∘ y            ≡⟨ cong₂ _∘_ x≡ y≡ ⟩
    g ^ i ∘ g ^ j    ≡⟨ ^∘^ i ⟩
    g ^ (i Int.+ j)  ≡⟨ cong (g ^_) $ Int.+-comm i ⟩
    g ^ (j Int.+ i)  ≡⟨ sym $ ^∘^ j ⟩
    g ^ j ∘ g ^ i    ≡⟨ sym $ cong₂ _∘_ y≡ x≡ ⟩∎
    y ∘ x            ∎
  where
  open Group G

------------------------------------------------------------------------
-- Some preservation results

-- If two groups are isomorphic, and one is generated by g, then the
-- other is generated by the image of g under the isomorphism.

≃ᴳ→Generated-by→Generated-by :
  (G₁≃G₂ : G₁ ≃ᴳ G₂) →
  Generated-by G₁ g →
  Generated-by G₂ (to G₁≃G₂ g)
≃ᴳ→Generated-by→Generated-by
  {G₁ = G₁} {G₂ = G₂} {g = g} G₁≃G₂ gen-by x =
  flip T.∥∥-map (gen-by (_≃_.from (G₁≃G₂ .related) x)) λ (i , x≡) →
    i
  , (x                    ≡⟨ sym $ _≃_.from-to (G₁≃G₂ .related) x≡ ⟩
     to G₁≃G₂ (g G₁.^ i)  ≡⟨ →ᴳ-^ G₁≃G₂ g i ⟩∎
     to G₁≃G₂ g G₂.^ i    ∎)
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

-- If two groups are isomorphic, and one is cyclic, then the other one
-- is cyclic.

≃ᴳ→Cyclic→Cyclic : G₁ ≃ᴳ G₂ → Cyclic G₁ → Cyclic G₂
≃ᴳ→Cyclic→Cyclic G₁≃G₂ =
  T.∥∥-map λ (_ , gen-by) →
    _ , ≃ᴳ→Generated-by→Generated-by G₁≃G₂ gen-by

-- If two groups are isomorphic, and one is abelian, then the other
-- one is abelian.

≃ᴳ→Abelian→Abelian : G₁ ≃ᴳ G₂ → Abelian G₁ → Abelian G₂
≃ᴳ→Abelian→Abelian {G₁ = G₁} {G₂ = G₂} G₁≃G₂ ∘-comm x y =
  _≃_.injective (G₂≃G₁ .related)
    (to G₂≃G₁ (x G₂.∘ y)         ≡⟨ G₂≃G₁ .homomorphic _ _ ⟩
     to G₂≃G₁ x G₁.∘ to G₂≃G₁ y  ≡⟨ ∘-comm _ _ ⟩
     to G₂≃G₁ y G₁.∘ to G₂≃G₁ x  ≡⟨ sym $ G₂≃G₁ .homomorphic _ _ ⟩∎
     to G₂≃G₁ (y G₂.∘ x)         ∎)
  where
  module G₁ = Group G₁
  module G₂ = Group G₂

  G₂≃G₁ = ≃ᴳ-sym G₁≃G₂

------------------------------------------------------------------------
-- A group construction

-- The direct product of two groups.

infixr 2 _×_

_×_ : Group g₁ → Group g₂ → Group (g₁ ⊔ g₂)
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
  open Group

  module G₁ = Group G₁
  module G₂ = Group G₂

-- The direct product operator preserves group homomorphisms.

↝-× :
  G₁ ↝[ k ]ᴳ G₂ → G₁′ ↝[ k ]ᴳ G₂′ →
  (G₁ × G₁′) ↝[ k ]ᴳ (G₂ × G₂′)
↝-× {G₁ = G₁} {k = k} {G₂ = G₂} {G₁′ = G₁′} {G₂′ = G₂′}
  G₁↝G₂ G₁′↝G₂′ = λ where
  .related →
    G₁↝G₂ .related ×-cong G₁′↝G₂′ .related
  .homomorphic x@(x₁ , x₂) y@(y₁ , y₂) →
    to-implication (G₁↝G₂ .related ×-cong G₁′↝G₂′ .related)
      (Σ-zip (Group._∘_ G₁) (Group._∘_ G₁′) x y)                   ≡⟨ cong (_$ _) $ to-implication-×-cong k ⟩

    Σ-map (to G₁↝G₂) (to G₁′↝G₂′)
      (Σ-zip (Group._∘_ G₁) (Group._∘_ G₁′) x y)                   ≡⟨⟩

    to G₁↝G₂   (Group._∘_ G₁  x₁ y₁) ,
    to G₁′↝G₂′ (Group._∘_ G₁′ x₂ y₂)                               ≡⟨ cong₂ _,_
                                                                        (G₁↝G₂   .homomorphic _ _)
                                                                        (G₁′↝G₂′ .homomorphic _ _) ⟩
    Group._∘_ G₂  (to G₁↝G₂   x₁) (to G₁↝G₂   y₁) ,
    Group._∘_ G₂′ (to G₁′↝G₂′ x₂) (to G₁′↝G₂′ y₂)                  ≡⟨⟩

    Group._∘_ (G₂ × G₂′)
      (to G₁↝G₂ x₁ , to G₁′↝G₂′ x₂)
      (to G₁↝G₂ y₁ , to G₁′↝G₂′ y₂)                                ≡⟨ sym $ cong₂ (λ f g → Group._∘_ (G₂ × G₂′) (f _) (g _))
                                                                        (to-implication-×-cong k)
                                                                        (to-implication-×-cong k) ⟩∎
    Group._∘_ (G₂ × G₂′)
      (to-implication (G₁↝G₂ .related ×-cong G₁′↝G₂′ .related) x)
      (to-implication (G₁↝G₂ .related ×-cong G₁′↝G₂′ .related) y)  ∎

-- Exponentiation for the direct product of G₁ and G₂ can be expressed
-- in terms of exponentiation for G₁ and exponentiation for G₂.

^-× :
  ∀ (G₁ : Group g₁) (G₂ : Group g₂) {x y} i →
  Group._^_ (G₁ × G₂) (x , y) i ≡
  (Group._^_ G₁ x i , Group._^_ G₂ y i)
^-× G₁ G₂ = helper
  where
  module G₁  = Group G₁
  module G₂  = Group G₂
  module G₁₂ = Group (G₁ × G₂)

  +-helper : ∀ n → (x , y) G₁₂.^+ n ≡ (x G₁.^+ n , y G₂.^+ n)
  +-helper                 zero    = refl _
  +-helper {x = x} {y = y} (suc n) =
    (x , y) G₁₂.∘ (x , y) G₁₂.^+ n         ≡⟨ cong (_ G₁₂.∘_) $ +-helper n ⟩
    (x , y) G₁₂.∘ (x G₁.^+ n , y G₂.^+ n)  ≡⟨⟩
    (x G₁.∘ x G₁.^+ n , y G₂.∘ y G₂.^+ n)  ∎

  helper : ∀ i → (x , y) G₁₂.^ i ≡ (x G₁.^ i , y G₂.^ i)
  helper (+ n)    = +-helper n
  helper -[1+ n ] = +-helper (suc n)
