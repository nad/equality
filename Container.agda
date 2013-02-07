------------------------------------------------------------------------
-- Containers, including a definition of bag equivalence
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container where

open import Bag-equivalence using (Kind); open Bag-equivalence.Kind
open import Equivalence hiding (id; _∘_; inverse)
open import Equality.Propositional
open import Prelude hiding (id; List; map; lookup)

open import Bijection equality-with-J as Bijection
  using (_↔_; module _↔_)
open import Function-universe equality-with-J as Function-universe
  hiding (inverse; Kind) renaming (_∘_ to _⟨∘⟩_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (module _↠_)
open import Weak-equivalence equality-with-J as Weak
  using (Is-weak-equivalence; _≃_; weq; module _≃_)

------------------------------------------------------------------------
-- Containers

record Container c : Set (lsuc c) where
  constructor _▷_
  field
    Shape    : Set c
    Position : Shape → Set c

open Container public

-- Interpretation of containers.

⟦_⟧ : ∀ {c ℓ} → Container c → Set ℓ → Set _
⟦ S ▷ P ⟧ A = ∃ λ (s : S) → (P s → A)

------------------------------------------------------------------------
-- Some projections

-- The shape of something.

shape : ∀ {a c} {A : Set a} {C : Container c} → ⟦ C ⟧ A → Shape C
shape = proj₁

-- A lookup function.

lookup : ∀ {a c} {A : Set a} {C : Container c}
         (xs : ⟦ C ⟧ A) → Position C (shape xs) → A
lookup = proj₂

------------------------------------------------------------------------
-- Map

-- Containers are functors.

map : ∀ {c x y} {C : Container c} {X : Set x} {Y : Set y} →
      (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Σ-map id (λ g → f ∘ g)

module Map where

  identity : ∀ {c x} {C : Container c} {X : Set x}
             (xs : ⟦ C ⟧ X) → map id xs ≡ xs
  identity xs = refl

  composition : ∀ {c x y z}
                  {C : Container c} {X : Set x} {Y : Set y} {Z : Set z}
                (f : Y → Z) (g : X → Y) (xs : ⟦ C ⟧ X) →
                map f (map g xs) ≡ map (f ∘ g) xs
  composition f g xs = refl

-- Naturality.

Natural : ∀ {c₁ c₂ a} {C₁ : Container c₁} {C₂ : Container c₂} →
          ({A : Set a} → ⟦ C₁ ⟧ A → ⟦ C₂ ⟧ A) → Set (c₁ ⊔ c₂ ⊔ lsuc a)
Natural function =
  ∀ {A B} (f : A → B) xs →
  map f (function xs) ≡ function (map f xs)

-- Natural transformations.

infixr 4 _[_]⟶_

record _[_]⟶_ {c₁ c₂} (C₁ : Container c₁) ℓ (C₂ : Container c₂) :
              Set (c₁ ⊔ c₂ ⊔ lsuc ℓ) where
  field
    function : {A : Set ℓ} → ⟦ C₁ ⟧ A → ⟦ C₂ ⟧ A
    natural  : Natural function

-- Natural isomorphisms.

record _[_]↔_ {c₁ c₂} (C₁ : Container c₁) ℓ (C₂ : Container c₂) :
              Set (c₁ ⊔ c₂ ⊔ lsuc ℓ) where
  field
    isomorphism : {A : Set ℓ} → ⟦ C₁ ⟧ A ↔ ⟦ C₂ ⟧ A
    natural     : Natural (_↔_.to isomorphism)

  -- Natural isomorphisms are natural transformations.

  natural-transformation : C₁ [ ℓ ]⟶ C₂
  natural-transformation = record
    { function = _↔_.to isomorphism
    ; natural  = natural
    }

  -- Natural isomorphisms can be inverted.

  inverse : C₂ [ ℓ ]↔ C₁
  inverse = record
    { isomorphism = Function-universe.inverse isomorphism
    ; natural     = λ f xs →
        map f (from xs)              ≡⟨ sym $ left-inverse-of _ ⟩
        from (to (map f (from xs)))  ≡⟨ sym $ cong from $ natural f (from xs) ⟩
        from (map f (to (from xs)))  ≡⟨ cong (from ∘ map f) $ right-inverse-of _ ⟩∎
        from (map f xs)              ∎
    }
    where open module I {A : Set ℓ} = _↔_ (isomorphism {A = A})

open Function-universe using (inverse)

------------------------------------------------------------------------
-- Any, _∈_, bag equivalence and similar relations

-- Definition of Any for containers.

Any : ∀ {a c p} {A : Set a} {C : Container c} →
      (A → Set p) → (⟦ C ⟧ A → Set (c ⊔ p))
Any {C = S ▷ P} Q (s , f) = ∃ λ (p : P s) → Q (f p)

-- Membership predicate.

infix 4 _∈_

_∈_ : ∀ {a c} {A : Set a} {C : Container c} → A → ⟦ C ⟧ A → Set _
x ∈ xs = Any (λ y → x ≡ y) xs

-- Bag equivalence etc. Note that the containers can be different as
-- long as the elements they contain have equal types.

infix 4 _∼[_]_

_∼[_]_ : ∀ {a c₁ c₂}
           {A : Set a} {C₁ : Container c₁} {C₂ : Container c₂} →
         ⟦ C₁ ⟧ A → Kind → ⟦ C₂ ⟧ A → Set _
xs ∼[ k ] ys = ∀ z → z ∈ xs ↝[ k ] z ∈ ys

-- Bag equivalence.

infix 4 _≈-bag_

_≈-bag_ : ∀ {a c₁ c₂}
            {A : Set a} {C₁ : Container c₁} {C₂ : Container c₂} →
          ⟦ C₁ ⟧ A → ⟦ C₂ ⟧ A → Set _
xs ≈-bag ys = xs ∼[ bag ] ys

------------------------------------------------------------------------
-- Various properties related to Any, _∈_ and _∼[_]_

-- Lemma relating Any to map.

Any-map : ∀ {a b c p} {A : Set a} {B : Set b} {C : Container c}
          (P : B → Set p) (f : A → B) (xs : ⟦ C ⟧ A) →
          Any P (map f xs) ↔ Any (P ∘ f) xs
Any-map P f xs = Any P (map f xs) □

-- Any can be expressed using _∈_.

Any-∈ : ∀ {a c p} {A : Set a} {C : Container c}
        (P : A → Set p) (xs : ⟦ C ⟧ A) →
        Any P xs ↔ ∃ λ x → P x × x ∈ xs
Any-∈ P (s , f) =
  (∃ λ p → P (f p))                ↔⟨ ∃-cong (λ p → ∃-intro P (f p)) ⟩
  (∃ λ p → ∃ λ x → P x × x ≡ f p)  ↔⟨ ∃-comm ⟩
  (∃ λ x → ∃ λ p → P x × x ≡ f p)  ↔⟨ ∃-cong (λ _ → ∃-comm) ⟩
  (∃ λ x → P x × ∃ λ p → x ≡ f p)  □

-- Using this property we can prove that Any and _⊎_ commute.

Any-⊎ : ∀ {a c p q} {A : Set a} {C : Container c}
        (P : A → Set p) (Q : A → Set q) (xs : ⟦ C ⟧ A) →
        Any (λ x → P x ⊎ Q x) xs ↔ Any P xs ⊎ Any Q xs
Any-⊎ P Q xs =
  Any (λ x → P x ⊎ Q x) xs                         ↔⟨ Any-∈ (λ x → P x ⊎ Q x) xs ⟩
  (∃ λ x → (P x ⊎ Q x) × x ∈ xs)                   ↔⟨ ∃-cong (λ x → ×-⊎-distrib-right) ⟩
  (∃ λ x → P x × x ∈ xs ⊎ Q x × x ∈ xs)            ↔⟨ ∃-⊎-distrib-left ⟩
  (∃ λ x → P x × x ∈ xs) ⊎ (∃ λ x → Q x × x ∈ xs)  ↔⟨ inverse $ Any-∈ P xs ⊎-cong Any-∈ Q xs ⟩
  Any P xs ⊎ Any Q xs                              □

-- Any preserves functions of various kinds and respects bag
-- equivalence and similar relations.

Any-cong : ∀ {k a c d p q}
             {A : Set a} {C : Container c} {D : Container d}
           (P : A → Set p) (Q : A → Set q)
           (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
           (∀ x → P x ↝[ k ] Q x) → xs ∼[ k ] ys →
           Any P xs ↝[ k ] Any Q ys
Any-cong P Q xs ys P↔Q xs∼ys =
  Any P xs                ↔⟨ Any-∈ P xs ⟩
  (∃ λ z → P z × z ∈ xs)  ↝⟨ ∃-cong (λ z → P↔Q z ×-cong xs∼ys z) ⟩
  (∃ λ z → Q z × z ∈ ys)  ↔⟨ inverse (Any-∈ Q ys) ⟩
  Any Q ys                □

-- Map preserves the relations.

map-cong : ∀ {k a b c d}
             {A : Set a} {B : Set b} {C : Container c} {D : Container d}
           (f : A → B)
           (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
           xs ∼[ k ] ys → map f xs ∼[ k ] map f ys
map-cong f xs ys xs∼ys = λ z →
  z ∈ map f xs            ↔⟨ Any-map (_≡_ z) f xs ⟩
  Any (λ x → z ≡ f x) xs  ↝⟨ Any-cong _ _ xs ys (λ x → z ≡ f x □) xs∼ys ⟩
  Any (λ x → z ≡ f x) ys  ↔⟨ inverse (Any-map (_≡_ z) f ys) ⟩
  z ∈ map f ys            □

-- Lemma relating Any to if_then_else_.

Any-if : ∀ {a c p} {A : Set a} {C : Container c}
         (P : A → Set p) (xs ys : ⟦ C ⟧ A) b →
         Any P (if b then xs else ys) ↔
         T b × Any P xs ⊎ T (not b) × Any P ys
Any-if P xs ys =
  inverse ∘ if-lemma (λ b → Any P (if b then xs else ys)) id id

-- One can reconstruct (up to natural isomorphism) the shape set and
-- the position predicate from the interpretation and the Any
-- predicate transformer.
--
-- (The following lemmas were suggested by an anonymous reviewer.)

Shape′ : ∀ {c} → (Set → Set c) → Set c
Shape′ F = F ⊤

Shape-⟦⟧ : ∀ {c} (C : Container c) →
           Shape C ↔ Shape′ ⟦ C ⟧
Shape-⟦⟧ C =
  Shape C                                 ↔⟨ inverse ×-right-identity ⟩
  Shape C × ⊤                             ↔⟨ ∃-cong (λ _ → inverse →-right-zero) ⟩
  (∃ λ (s : Shape C) → Position C s → ⊤)  □

Position′ : ∀ {c} (F : Set → Set c) →
            ({A : Set} → (A → Set) → (F A → Set c)) →
            Shape′ F → Set c
Position′ _ Any = Any (λ (_ : ⊤) → ⊤)

Position-Any : ∀ {c} {C : Container c} (s : Shape C) →
               Position C s ↔
               Position′ ⟦ C ⟧ Any (_↔_.to (Shape-⟦⟧ C) s)
Position-Any {C = C} s =
  Position C s      ↔⟨ inverse ×-right-identity ⟩
  Position C s × ⊤  □

expressed-in-terms-of-interpretation-and-Any :
  ∀ {c ℓ} (C : Container c) →
  C [ ℓ ]↔ (⟦ C ⟧ ⊤ ▷ Any (λ _ → ⊤))
expressed-in-terms-of-interpretation-and-Any C = record
  { isomorphism = λ {A} →
      (∃ λ (s : Shape C) → Position C s → A)                ↔⟨ Σ-cong (Shape-⟦⟧ C) (λ _ → lemma) ⟩
      (∃ λ (s : Shape′ ⟦ C ⟧) → Position′ ⟦ C ⟧ Any s → A)  □
  ; natural = λ _ _ → refl
  }
  where
  -- If equality of functions had been extensional, then the following
  -- lemma could have been replaced by a congruence lemma applied to
  -- Position-Any.
  lemma : ∀ {a b} {A : Set a} {B : Set b} → (B → A) ↔ (B × ⊤ → A)
  lemma = record
    { surjection = record
      { equivalence = record
        { to   = λ { f (p , tt) → f p }
        ; from = λ f p → f (p , tt)
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

------------------------------------------------------------------------
-- Alternative definition of bag equivalence

-- Two things are bag equal if there is a bijection (or weak
-- equivalence) between their positions which relates equal things.

infix 4 _≈[_]′_

_≈[_]′_ : ∀ {a c d} {A : Set a} {C : Container c} {D : Container d} →
          ⟦ C ⟧ A → Isomorphism-kind → ⟦ D ⟧ A → Set _
_≈[_]′_ {C = C} {D} (s , f) k (s′ , f′) =
  ∃ λ (P↔P : Position C s ↔[ k ] Position D s′) →
      (∀ p → f p ≡ f′ (to-implication P↔P p))

-- If the position sets are sets (have H-level two), then the two
-- instantiations of _≈[_]′_ are isomorphic (assuming extensionality).

≈′↔≈′ : ∀ {a c d} {A : Set a} {C : Container c} {D : Container d} →
        Extensionality (c ⊔ d) (c ⊔ d) →
        (∀ s → Is-set (Position C s)) →
        (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
        xs ≈[ bag ]′ ys ↔ xs ≈[ bag-with-weak-equivalence ]′ ys
≈′↔≈′ ext P-set (s , f) (s′ , f′) =
  (∃ λ P↔P → ∀ p → f p ≡ f′ (to-implication P↔P p))  ↔⟨ Σ-cong (Weak.↔↔≃ ext (P-set s)) (λ _ → Bijection.id) ⟩
  (∃ λ P↔P → ∀ p → f p ≡ f′ (to-implication P↔P p))  □

-- The definition _≈[_]′_ is also equivalent to the one given above.
-- The proof is very similar to the one given in Bag-equivalence.

-- Membership can be expressed as "there is an index which points to
-- the element". In fact, membership /is/ expressed in this way, so
-- this proof is unnecessary.

∈-lookup : ∀ {a c} {A : Set a} {C : Container c} {z}
           (xs : ⟦ C ⟧ A) → z ∈ xs ↔ ∃ λ p → z ≡ lookup xs p
∈-lookup {z = z} xs = z ∈ xs □

-- The index which points to the element (not used below).

index : ∀ {a c} {A : Set a} {C : Container c} {z}
        (xs : ⟦ C ⟧ A) → z ∈ xs → Position C (shape xs)
index xs = proj₁ ∘ to-implication (∈-lookup xs)

-- The positions for a given shape can be expressed in terms of the
-- membership predicate.

Position-shape : ∀ {a c} {A : Set a} {C : Container c} (xs : ⟦ C ⟧ A) →
                 (∃ λ z → z ∈ xs) ↔ Position C (shape xs)
Position-shape {C = C} (s , f) =
  (∃ λ z → ∃ λ p → z ≡ f p)  ↔⟨ ∃-comm ⟩
  (∃ λ p → ∃ λ z → z ≡ f p)  ↔⟨⟩
  (∃ λ p → Singleton (f p))  ↔⟨ ∃-cong (λ _ → contractible↔⊤ (singleton-contractible _)) ⟩
  Position C s × ⊤           ↔⟨ ×-right-identity ⟩
  Position C s               □

-- Position _ ∘ shape respects the various relations.

Position-shape-cong :
  ∀ {k a c d} {A : Set a} {C : Container c} {D : Container d}
  (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
  xs ∼[ k ] ys → Position C (shape xs) ↝[ k ] Position D (shape ys)
Position-shape-cong {C = C} {D} xs ys xs∼ys =
  Position C (shape xs)  ↔⟨ inverse $ Position-shape xs ⟩
  ∃ (λ z → z ∈ xs)       ↝⟨ ∃-cong xs∼ys ⟩
  ∃ (λ z → z ∈ ys)       ↔⟨ Position-shape ys ⟩
  Position D (shape ys)  □

-- Furthermore Position-shape-cong relates equal elements.

Position-shape-cong-relates :
  ∀ {k a c d} {A : Set a} {C : Container c} {D : Container d}
  (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) (xs≈ys : xs ∼[ k ] ys) p →
  lookup xs p ≡
    lookup ys (to-implication (Position-shape-cong xs ys xs≈ys) p)
Position-shape-cong-relates {bag} xs ys xs≈ys p =
  lookup xs p                                                     ≡⟨ proj₂ $ to-implication (xs≈ys (lookup xs p)) (p , refl) ⟩
  lookup ys (proj₁ $ to-implication (xs≈ys (lookup xs p))
                                    (p , refl))                   ≡⟨ refl ⟩
  lookup ys (_↔_.to (Position-shape ys) $
             Σ-map id (λ {z} → to-implication (xs≈ys z)) $
             _↔_.from (Position-shape xs) $ p)                    ≡⟨ refl ⟩
  lookup ys (_↔_.to (Position-shape ys) $
             to-implication (∃-cong xs≈ys) $
             _↔_.from (Position-shape xs) $ p)                    ≡⟨ refl ⟩
  lookup ys (to-implication
               ((from-bijection (Position-shape ys) ⟨∘⟩
                 ∃-cong xs≈ys) ⟨∘⟩
                from-bijection (inverse $ Position-shape xs))
               p)                                                 ≡⟨ refl ⟩∎
  lookup ys (to-implication (Position-shape-cong xs ys xs≈ys) p)  ∎

Position-shape-cong-relates {bag-with-weak-equivalence} xs ys xs≈ys p =
  proj₂ $ to-implication (xs≈ys (lookup xs p)) (p , refl)
Position-shape-cong-relates {subbag} xs ys xs≈ys p =
  proj₂ $ to-implication (xs≈ys (lookup xs p)) (p , refl)
Position-shape-cong-relates {set} xs ys xs≈ys p =
  proj₂ $ to-implication (xs≈ys (lookup xs p)) (p , refl)
Position-shape-cong-relates {subset} xs ys xs≈ys p =
  proj₂ $ to-implication (xs≈ys (lookup xs p)) (p , refl)
Position-shape-cong-relates {surjection} xs ys xs≈ys p =
  proj₂ $ to-implication (xs≈ys (lookup xs p)) (p , refl)

-- We get that the two definitions of bag equivalence are equivalent.

≈⇔≈′ : ∀ {k a c d} {A : Set a} {C : Container c} {D : Container d}
       (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
       xs ∼[ ⌊ k ⌋-iso ] ys ⇔ xs ≈[ k ]′ ys
≈⇔≈′ {k} xs ys = record
  { to   = λ xs≈ys → ( Position-shape-cong xs ys xs≈ys
                     , Position-shape-cong-relates xs ys xs≈ys
                     )
  ; from = from
  }
  where
  from : xs ≈[ k ]′ ys → xs ∼[ ⌊ k ⌋-iso ] ys
  from (P↔P , related) = λ z →
    z ∈ xs                     ↔⟨⟩
    ∃ (λ p → z ≡ lookup xs p)  ↔⟨ Σ-cong P↔P (λ p → _↠_.from (Π≡↔≡-↠-≡ k _ _) (related p) z) ⟩
    ∃ (λ p → z ≡ lookup ys p)  ↔⟨⟩
    z ∈ ys                     □

-- If weak equivalences are used, then the definitions are isomorphic
-- (assuming extensionality).
--
-- Thierry Coquand helped me with this proof: At first I wasn't sure
-- if it was true or not, but then I managed to prove it for singleton
-- lists, Thierry found a proof for lists of length two, I found one
-- for streams, and finally I could complete the proof below.

≈↔≈′ : ∀ {a c d} {A : Set a} {C : Container c} {D : Container d} →
       Extensionality (a ⊔ c ⊔ d) (a ⊔ c ⊔ d) →
       (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
       xs ∼[ bag-with-weak-equivalence ] ys ↔
       xs ≈[ bag-with-weak-equivalence ]′ ys
≈↔≈′ {a} {c} {d} {C = C} {D} ext xs ys = record
  { surjection = record
    { equivalence      = equiv
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  equiv = ≈⇔≈′ {k = weak-equivalence} xs ys

  open _⇔_ equiv

  from∘to : ∀ xs≈ys → from (to xs≈ys) ≡ xs≈ys
  from∘to xs≈ys =
    lower-extensionality (c ⊔ d) a ext λ z →
      Weak.lift-equality ext $
        lower-extensionality d c ext λ { (p , z≡xs[p]) →

            let xs[p]≡ys[-] : ∃ λ p′ → lookup xs p ≡ lookup ys p′
                xs[p]≡ys[-] = _≃_.to (xs≈ys (lookup xs p)) (p , refl) in

          Σ-map id (trans z≡xs[p]) xs[p]≡ys[-]      ≡⟨ elim₁ (λ {z} z≡xs[p] → Σ-map id (trans z≡xs[p]) xs[p]≡ys[-] ≡
                                                                        _≃_.to (xs≈ys z) (p , z≡xs[p]))
            (Σ-map id (trans refl) xs[p]≡ys[-]               ≡⟨ cong (_,_ _) (trans-reflˡ _) ⟩∎
             xs[p]≡ys[-]                                        ∎)
                                                             z≡xs[p] ⟩∎
          _≃_.to (xs≈ys z) (p , z≡xs[p])            ∎ }

  to∘from : ∀ xs≈ys → to (from xs≈ys) ≡ xs≈ys
  to∘from (weq f f-weq , related) = Σ-≡,≡→≡ f≡f
    (subst (P ∘ _≃_.to) f≡f (trans refl ∘ related)  ≡⟨ cong (subst (P ∘ _≃_.to) f≡f)
                                                            (lower-extensionality (a ⊔ d) (c ⊔ d) ext λ _ → trans-reflˡ _) ⟩
     subst (P ∘ _≃_.to) f≡f related                 ≡⟨ subst-∘ P _≃_.to f≡f ⟩
     subst P (cong _≃_.to f≡f) related              ≡⟨ cong (λ eq → subst P eq related) cong-to-f≡f ⟩
     subst P refl related                           ≡⟨ subst-refl P {x = f} related ⟩∎
     related                                        ∎)
    where
    P : (Position C (shape xs) → Position D (shape ys)) → Set (a ⊔ c)
    P f = ∀ p → lookup xs p ≡ lookup ys (f p)

    f-weq′ : Is-weak-equivalence f
    f-weq′ = _≃_.is-weak-equivalence $
             Position-shape-cong xs ys $
             from (weq f f-weq , related)

    abstract
      irr : f-weq′ ≡ f-weq
      irr = proj₁ $
        Weak.propositional (lower-extensionality a a ext) f _ _

      f≡f : weq f f-weq′ ≡ weq f f-weq
      f≡f = cong (weq f) irr

      cong-to-f≡f : cong _≃_.to f≡f ≡ refl {x = f}
      cong-to-f≡f =
        cong _≃_.to f≡f            ≡⟨ cong-∘ _≃_.to (weq f) irr ⟩
        cong (_≃_.to ∘ weq f) irr  ≡⟨ cong-const irr ⟩∎
        refl                       ∎

------------------------------------------------------------------------
-- Another alternative definition of bag equivalence

-- A higher-order variant of _∼[_]_. Note that this definition is
-- large (due to the quantification over predicates).

infix 4 _∼[_]″_

_∼[_]″_ : ∀ {a c d} {A : Set a} {C : Container c} {D : Container d} →
          ⟦ C ⟧ A → Kind → ⟦ D ⟧ A → Set (lsuc a ⊔ c ⊔ d)
_∼[_]″_ {a} {A = A} xs k ys =
  (P : A → Set a) → Any P xs ↝[ k ] Any P ys

-- This definition is equivalent to _∼[_]_.

∼⇔∼″ : ∀ {k a c d} {A : Set a} {C : Container c} {D : Container d}
       (xs : ⟦ C ⟧ A) (ys : ⟦ D ⟧ A) →
       xs ∼[ k ] ys ⇔ xs ∼[ k ]″ ys
∼⇔∼″ xs ys = record
  { to   = λ xs∼ys P → Any-cong P P xs ys (λ _ → id) xs∼ys
  ; from = λ Any-xs↝Any-ys z → Any-xs↝Any-ys (λ x → z ≡ x)
  }
