------------------------------------------------------------------------
-- Permutations
--
-- An experiment inspired by a talk that Patrik Jansson gave on
-- 2025-05-09. The talk was based on work done with Wouter Swierstra.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality

module Permutation.Jansson-Swierstra
  {c⁺} (eq : ∀ {a p} → Equality-with-J a p c⁺) where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection eq using (_↔_)
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Extensionality eq
open import Fin eq
open import Function-universe eq as F hiding (id; _∘_)
open import Group eq hiding (_×_)

private variable
  n   : ℕ
  ext : Extensionality _ _

------------------------------------------------------------------------
-- Permutations

-- Permutations, defined roughly as in Jansson's talk (if I remember
-- correctly).

Perm : ℕ → Type
Perm zero    = ⊤
Perm (suc n) = Fin (suc n) × Perm n

private variable
  p : Perm _

------------------------------------------------------------------------
-- Some equivalences

opaque

  -- Perm n is equivalent to Fin (n !).

  Perm≃Fin-! : Perm n ≃ Fin (n !)
  Perm≃Fin-! {n = zero} =
    Perm 0     ↔⟨⟩
    ⊤          ↔⟨ inverse ⊎-right-identity ⟩
    ⊤ ⊎ ⊥      ↔⟨⟩
    Fin 1      ↔⟨⟩
    Fin (0 !)  □
  Perm≃Fin-! {n = suc n} =
    Perm (suc n)             ↔⟨⟩
    Fin (suc n) × Perm n     ↝⟨ F.id ×-cong Perm≃Fin-! ⟩
    Fin (suc n) × Fin (n !)  ↔⟨ Fin×Fin↔Fin* _ _ ⟩
    Fin (suc n * n !)        ↔⟨⟩
    Fin (suc n !)            □

opaque

  -- Perm n is equivalent to Fin n ≃ Fin n, assuming function
  -- extensionality.
  --
  -- Note that the proof also shows that Perm n is logically
  -- equivalent to Fin n ≃ Fin n, without any assumption of function
  -- extensionality.

  Perm≃[Fin≃Fin] : Perm n ↝[ lzero ∣ lzero ] (Fin n ≃ Fin n)
  Perm≃[Fin≃Fin] {n} ext =
    Perm n         ↔⟨ Perm≃Fin-! ⟩
    Fin (n !)      ↝⟨ inverse-ext? ([Fin≃Fin]≃Fin! _) ext ⟩
    Fin n ≃ Fin n  □

------------------------------------------------------------------------
-- Permutation combinators

-- Jansson defined these operators without converting to
-- automorphisms. I think the intention was partly to avoid the use of
-- function extensionality. I do use function extensionality in some
-- definitions below.

opaque

  -- Identity permutations.

  idᴾ : Perm n
  idᴾ = _⇔_.from (Perm≃[Fin≃Fin] _) F.id

opaque

  -- Inversion for permutations.

  infix 10 _⁻¹ᴾ

  _⁻¹ᴾ : Perm n → Perm n
  f ⁻¹ᴾ = _⇔_.from (Perm≃[Fin≃Fin] _) (inverse (Perm≃[Fin≃Fin] _ f))

opaque

  -- Composition of permutations.

  infixr 9 _∘ᴾ_

  _∘ᴾ_ : Perm n → Perm n → Perm n
  p₁ ∘ᴾ p₂ =
    _⇔_.from (Perm≃[Fin≃Fin] _)
      (Perm≃[Fin≃Fin] _ p₁ F.∘ Perm≃[Fin≃Fin] _ p₂)

------------------------------------------------------------------------
-- Conversion to functions

opaque

  -- Converts permutations to functions.

  ⟦_⟧ : Perm n → Fin n → Fin n
  ⟦_⟧ = _≃_.to ∘ Perm≃[Fin≃Fin] _

opaque

  -- Converts permutations to functions going in the other direction.

  ⟦_⁻¹⟧ : Perm n → Fin n → Fin n
  ⟦_⁻¹⟧ = _≃_.from ∘ Perm≃[Fin≃Fin] _

private opaque
  unfolding ⟦_⟧ Perm≃[Fin≃Fin] Perm≃Fin-! idᴾ

  -- Note that the obtained functions might not match those obtained
  -- by Jansson. I seem to recall that with Jansson's semantics
  -- "2 , idᴾ : Perm 3" maps 0 to 2, 1 to 0 and 2 to 1. However, if
  -- ⟦_⟧ is used, then 0 is mapped to 2, 1 to 1, and 2 to 0. For the
  -- permutation i , idᴾ all values are mapped to themselves except
  -- (possibly) for i and 0, which are swapped, see ⟦,idᴾ⟧ below.

  example : Perm 3
  example = fsuc (fsuc fzero) , idᴾ

  _ : ⟦ example ⟧ fzero               ≡ fsuc (fsuc fzero)
  _ = refl _

  _ : ⟦ example ⟧ (fsuc fzero)        ≡ fsuc fzero
  _ = refl _

  _ : ⟦ example ⟧ (fsuc (fsuc fzero)) ≡ fzero
  _ = refl _

private opaque
  unfolding ⟦_⟧ Perm≃[Fin≃Fin] Perm≃Fin-!

  -- A lemma used below.

  ⟦⟧≡ :
    {i : Fin (suc n)} →
    ⟦ p ⟧ i ≡
    _↔_.to
      (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
       Σ-map id (_≃_.bijection ∘ Perm≃[Fin≃Fin] _) p)
      i
  ⟦⟧≡ {p} {i} =
    ⟦ p ⟧ i                                              ≡⟨⟩

    _↔_.to
      (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
       Σ-map id
         (_≃_.bijection ∘
          _⇔_.from ([Fin≃Fin]≃Fin! _ _)) $
       _↔_.from (Fin×Fin↔Fin* _ _) $
       _↔_.to (Fin×Fin↔Fin* _ _) $
       Σ-map id (_≃_.to Perm≃Fin-!) p)
      i                                                  ≡⟨ cong
                                                              (flip _↔_.to i ∘
                                                               _⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) ∘
                                                               Σ-map id
                                                                 (_≃_.bijection ∘
                                                                  _⇔_.from ([Fin≃Fin]≃Fin! _ _))) $
                                                            _↔_.left-inverse-of (Fin×Fin↔Fin* _ _) _ ⟩
    _↔_.to
      (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
       Σ-map id
         (_≃_.bijection ∘
          _⇔_.from ([Fin≃Fin]≃Fin! _ _) ∘
          _≃_.to Perm≃Fin-!)
         p)
      i                                                  ≡⟨⟩

    _↔_.to
      (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
       Σ-map id (_≃_.bijection ∘ Perm≃[Fin≃Fin] _) p)
      i                                                  ∎

opaque
  unfolding ⟦_⟧

  -- A characterisation of ⟦_⟧ for "non-empty" permutations.

  ⟦,⟧≡ :
    {i j : Fin (suc n)} →
    ⟦ i , p ⟧ j ≡
    [ (λ _ → i)
    , (λ j →
         let k = fsuc (⟦ p ⟧ j) in
         if k Fin.≟ i then fzero else k)
    ] j
  ⟦,⟧≡ {j = fzero}  = ⟦⟧≡
  ⟦,⟧≡ {j = fsuc _} = ⟦⟧≡

------------------------------------------------------------------------
-- Some lemmas used to convert between applications of Perm≃[Fin≃Fin]
-- that involve function extensionality and applications that do not
-- (necessarily) involve function extensionality

-- These lemmas could perhaps have been avoided if _↝[_∣_]_ had been
-- defined in a different way.

private opaque
  unfolding Perm≃[Fin≃Fin]

  -- A lemma.

  add-ext-to :
    {p : Perm n} →
    Perm≃[Fin≃Fin] _ p ≡ _≃_.to (Perm≃[Fin≃Fin] ext) p
  add-ext-to {ext} {p} = lemma _
    where
    lemma :
      ∀ n {p : Fin (n !)} →
      _⇔_.from ([Fin≃Fin]≃Fin! n _) p ≡
      _↔_.from ([Fin≃Fin]≃Fin! n ext) p
    lemma zero    = refl _
    lemma (suc n) =
      Eq.lift-equality ext $
      cong
        (_↔_.to ∘ _⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) ∘ _,_ _ ∘
         _≃_.bijection) $
      lemma n

private opaque
  unfolding Perm≃[Fin≃Fin]

  -- A lemma.

  add-ext-from :
    {p : Fin n ≃ Fin n} →
    _⇔_.from (Perm≃[Fin≃Fin] _) p ≡ _≃_.from (Perm≃[Fin≃Fin] ext) p
  add-ext-from {p} = cong (_≃_.from Perm≃Fin-!) (lemma _ p)
    where
    lemma :
      ∀ n (p : Fin n ≃ Fin n) →
      _⇔_.to ([Fin≃Fin]≃Fin! _ _) p ≡ _↔_.to ([Fin≃Fin]≃Fin! _ ext) p
    lemma zero    _ = refl _
    lemma (suc n) p =
      cong (_↔_.to (Fin×Fin↔Fin* _ _)) $
      cong (proj₁ ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _ (_≃_.bijection p)) ,_) $
      lemma n _

private opaque

  -- A lemma.

  remove-conversion :
    {p : Fin n ≃ Fin n} →
    Extensionality lzero lzero →
    _≃_.to (Perm≃[Fin≃Fin] _ (_⇔_.from (Perm≃[Fin≃Fin] _) p)) ≡
    _≃_.to p
  remove-conversion {p} ext =
    cong _≃_.to
      ((Perm≃[Fin≃Fin] _ (_⇔_.from (Perm≃[Fin≃Fin] _) p))               ≡⟨ add-ext-to ⟩
       (_≃_.to (Perm≃[Fin≃Fin] ext) (_⇔_.from (Perm≃[Fin≃Fin] _) p))    ≡⟨ cong (_≃_.to (Perm≃[Fin≃Fin] _)) add-ext-from ⟩
       (_≃_.to (Perm≃[Fin≃Fin] ext) (_≃_.from (Perm≃[Fin≃Fin] ext) p))  ≡⟨ _≃_.right-inverse-of (Perm≃[Fin≃Fin] _) _ ⟩∎
       p                                                                ∎)

------------------------------------------------------------------------
-- Permutation groups

private

  -- The type Fin n ≃ Fin n forms a group, assuming function
  -- extensionality.

  group′ :
    Extensionality lzero lzero →
    ℕ → Group lzero
  group′ ext n =
    group-for (Eq.groupoid ext) (Fin n)
      (Eq.h-level-closure ext 2 (Fin-set _) (Fin-set _))

-- The type Perm n forms a group, assuming function extensionality.

group :
  Extensionality lzero lzero →
  ℕ → Group lzero
group ext n =
  with-other-carrier (group′ ext n) (inverse (Perm≃[Fin≃Fin] ext))

opaque

  -- The group's carrier type is correct.

  _ : Group.Carrier (group ext n) ≡ Perm n
  _ = refl _

opaque
  unfolding idᴾ

  -- The group's identity is idᴾ.

  id≡idᴾ : Group.id (group ext n) ≡ idᴾ
  id≡idᴾ {ext} =
    _≃_.from (Perm≃[Fin≃Fin] ext) F.id  ≡⟨ sym add-ext-from ⟩
    _⇔_.from (Perm≃[Fin≃Fin] _) F.id    ≡⟨⟩
    idᴾ                                 ∎

opaque
  unfolding _⁻¹ᴾ

  -- The group's inversion operator is _⁻¹ᴾ.

  ⁻¹≡⁻¹ᴾ : Group._⁻¹ (group ext n) ≡ _⁻¹ᴾ
  ⁻¹≡⁻¹ᴾ {ext} =
    apply-ext ext λ p →
    _≃_.from (Perm≃[Fin≃Fin] ext)
      (inverse (_≃_.to (Perm≃[Fin≃Fin] ext) p))                 ≡⟨ sym add-ext-from ⟩

    _⇔_.from (Perm≃[Fin≃Fin] _)
      (inverse (_≃_.to (Perm≃[Fin≃Fin] ext) p))                 ≡⟨ cong (_⇔_.from (Perm≃[Fin≃Fin] _)) $ sym $
                                                                   cong inverse add-ext-to ⟩

    _⇔_.from (Perm≃[Fin≃Fin] _) (inverse (Perm≃[Fin≃Fin] _ p))  ≡⟨⟩

    p ⁻¹ᴾ                                                       ∎

opaque
  unfolding _∘ᴾ_

  -- The group's composition operator is _∘ᴾ_.

  ∘≡∘ᴾ : Group._∘_ (group ext n) ≡ _∘ᴾ_
  ∘≡∘ᴾ {ext} =
    apply-ext ext λ p₁ → apply-ext ext λ p₂ →
    _≃_.from (Perm≃[Fin≃Fin] ext)
      (_≃_.to (Perm≃[Fin≃Fin] ext) p₁ F.∘
       _≃_.to (Perm≃[Fin≃Fin] ext) p₂)               ≡⟨ sym add-ext-from ⟩

    _⇔_.from (Perm≃[Fin≃Fin] _)
      (_≃_.to (Perm≃[Fin≃Fin] ext) p₁ F.∘
       _≃_.to (Perm≃[Fin≃Fin] ext) p₂)               ≡⟨ cong (_⇔_.from (Perm≃[Fin≃Fin] _)) $ sym $
                                                        cong₂ F._∘_ add-ext-to add-ext-to ⟩
    _⇔_.from (Perm≃[Fin≃Fin] _)
      (Perm≃[Fin≃Fin] _ p₁ F.∘ Perm≃[Fin≃Fin] _ p₂)  ≡⟨⟩

    p₁ ∘ᴾ p₂                                         ∎

------------------------------------------------------------------------
-- Correctness properties for the permutation combinators

opaque
  unfolding ⟦_⟧ idᴾ

  -- The identity permutations are correctly defined (assuming
  -- function extensionality).

  ⟦⟧-idᴾ :
    Extensionality lzero lzero →
    ⟦ idᴾ {n = n} ⟧ ≡ id
  ⟦⟧-idᴾ ext =
    ⟦ idᴾ ⟧                                                       ≡⟨⟩
    _≃_.to (Perm≃[Fin≃Fin] _ (_⇔_.from (Perm≃[Fin≃Fin] _) F.id))  ≡⟨ remove-conversion ext ⟩∎
    id                                                            ∎

opaque
  unfolding ⟦_⟧ idᴾ Perm≃[Fin≃Fin] Perm≃Fin-!

  -- A variant of ⟦⟧-idᴾ without the assumption of function
  -- extensionality. This property can be proved, but I prefer the
  -- proof of ⟦⟧-idᴾ above to the proof I have given here.

  ⟦⟧-idᴾ′ : {i : Fin n} → ⟦ idᴾ ⟧ i ≡ i
  ⟦⟧-idᴾ′ = ⟦⟧-idᴾ″
    where
    ⟦⟧-idᴾ″ :
      {i : Fin n} {ok : Eq.Is-equivalence id} →
      ⟦ _⇔_.from (Perm≃[Fin≃Fin] _) Eq.⟨ id , ok ⟩ ⟧ i ≡ i
    ⟦⟧-idᴾ″ {n = suc n} {i} {ok} =
      ⟦ _⇔_.from (Perm≃[Fin≃Fin] _) Eq.⟨ id , ok ⟩ ⟧ i      ≡⟨ ⟦⟧≡ {i = i} ⟩

      _↔_.to
        (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
         Σ-map id (_≃_.bijection ∘ Perm≃[Fin≃Fin] _) $
         _⇔_.from (Perm≃[Fin≃Fin] _) Eq.⟨ id , ok ⟩)
        i                                                   ≡⟨⟩

      _↔_.to
        (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
         Σ-map id
           (_≃_.bijection ∘
            Perm≃[Fin≃Fin] _ ∘
            _≃_.from Perm≃Fin-!) $
         _↔_.from (Fin×Fin↔Fin* _ _) $
         _↔_.to (Fin×Fin↔Fin* _ _) $
         Σ-map id (_⇔_.to ([Fin≃Fin]≃Fin! _ _) ∘ Eq.↔⇒≃) $
         _⇔_.to ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
         _≃_.bijection Eq.⟨ id , ok ⟩)
        i                                                   ≡⟨ cong
                                                                 (flip _↔_.to i ∘
                                                                  _⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) ∘
                                                                  Σ-map id (_≃_.bijection ∘ Perm≃[Fin≃Fin] _ ∘ _≃_.from Perm≃Fin-!)) $
                                                               _↔_.left-inverse-of (Fin×Fin↔Fin* _ _) _ ⟩
      _↔_.to
        (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
         Σ-map id
           (_≃_.bijection ∘
            Perm≃[Fin≃Fin] _ ∘
            _⇔_.from (Perm≃[Fin≃Fin] _) ∘
            Eq.↔⇒≃) $
         _⇔_.to ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
         _≃_.bijection Eq.⟨ id , ok ⟩)
        i                                                   ≡⟨ lemma _ ⟩∎

      i                                                     ∎
      where
      lemma :
        (i : Fin (suc n)) →
        _↔_.to
          (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
           Σ-map id
             (_≃_.bijection ∘
              Perm≃[Fin≃Fin] _ ∘
              _⇔_.from (Perm≃[Fin≃Fin] _) ∘
              Eq.↔⇒≃) $
           _⇔_.to ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
           _≃_.bijection Eq.⟨ id , ok ⟩)
          i ≡
        i
      lemma fzero    = refl _
      lemma (fsuc i) =
        _↔_.to
          (_⇔_.from ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
           Σ-map id
             (_≃_.bijection ∘
              Perm≃[Fin≃Fin] _ ∘
              _⇔_.from (Perm≃[Fin≃Fin] _) ∘
              Eq.↔⇒≃) $
           _⇔_.to ([⊤⊎↔⊤⊎]↔[⊤⊎×↔] Fin._≟_ _) $
           _≃_.bijection Eq.⟨ id , ok ⟩)
          (fsuc i)                                              ≡⟨⟩

        fsuc (⟦ _⇔_.from (Perm≃[Fin≃Fin] _) Eq.⟨ id , _ ⟩ ⟧ i)  ≡⟨ cong fsuc ⟦⟧-idᴾ″ ⟩

        fsuc i                                                  ∎

opaque
  unfolding ⟦_⟧ ⟦_⁻¹⟧ _⁻¹ᴾ

  -- Inversion is correctly defined (assuming function
  -- extensionality).

  ⟦⟧-⁻¹ᴾ :
    {p : Perm n} →
    Extensionality lzero lzero →
    ⟦ p ⁻¹ᴾ ⟧ ≡ ⟦ p ⁻¹⟧
  ⟦⟧-⁻¹ᴾ {p} ext =
    ⟦ p ⁻¹ᴾ ⟧                                            ≡⟨⟩

    _≃_.to
      (Perm≃[Fin≃Fin] _ $ _⇔_.from (Perm≃[Fin≃Fin] _) $
       inverse (Perm≃[Fin≃Fin] _ p))                     ≡⟨ remove-conversion ext ⟩

    _≃_.to (inverse (Perm≃[Fin≃Fin] _ p))                ≡⟨⟩

    ⟦ p ⁻¹⟧                                              ∎

opaque
  unfolding ⟦_⟧ _∘ᴾ_

  -- Composition is correctly defined (assuming function
  -- extensionality).

  ⟦⟧-∘ᴾ :
    {p₁ p₂ : Perm n} →
    Extensionality lzero lzero →
    ⟦ p₁ ∘ᴾ p₂ ⟧ ≡ ⟦ p₁ ⟧ ∘ ⟦ p₂ ⟧
  ⟦⟧-∘ᴾ = remove-conversion

------------------------------------------------------------------------
-- A lemma related to ⟦ i , idᴾ ⟧

opaque

  -- The function ⟦ i , idᴾ ⟧ swaps 0 and i and leaves all other
  -- values unchanged.

  ⟦,idᴾ⟧ :
    {i j : Fin (suc n)} →
    ⟦ i , idᴾ ⟧ j ≡
    if j Fin.≟ fzero then i     else
    if j Fin.≟ i     then fzero else
    j
  ⟦,idᴾ⟧     {j = fzero}  = ⟦,⟧≡
  ⟦,idᴾ⟧ {i} {j = fsuc j} =
    ⟦ i , idᴾ ⟧ (fsuc j)                      ≡⟨ ⟦,⟧≡ ⟩

    (let k = fsuc (⟦ idᴾ ⟧ j) in
     if k Fin.≟ i then fzero else k)          ≡⟨ cong (λ k → if fsuc k Fin.≟ i then fzero else fsuc k)
                                                 ⟦⟧-idᴾ′ ⟩

    if fsuc j Fin.≟ i then fzero else fsuc j  ≡⟨⟩

    if fsuc j Fin.≟ fzero then i else
    if fsuc j Fin.≟ i then fzero else fsuc j  ∎
