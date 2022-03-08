------------------------------------------------------------------------
-- Joins
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

import Equality.Path as P

module Join {e⁺} (eq : ∀ {a p} → P.Equality-with-paths a p e⁺) where

open P.Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)
open import Prelude

import Accessibility equality-with-J as A
open import Bijection equality-with-J as B using (_↔_)
open import Embedding equality-with-J as Emb
  using (Embedding; Is-embedding)
open import Equality.Decision-procedures equality-with-J
open import Equality.Path.Isomorphisms eq
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Equivalence.Erased equality-with-J as EEq using (_≃ᴱ_)
open import Equivalence.Path-split equality-with-J as PS
  using (Is-∞-extendable-along-[_])
open import Excluded-middle equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (_↣_; Injective)
open import Modality equality-with-J
import Modality.Very-modal equality-with-J as Very-modal
open import Pushout eq as PO
open import Surjection equality-with-J using (_↠_)

private
  variable
    a b c d ℓ p : Level
    A B C D     : Type a
    P           : A → Type p

------------------------------------------------------------------------
-- The join type former

-- The span used to define Join.

Join-span : Type a → Type b → Span a b (a ⊔ b)
Join-span A B = record
  { Middle = A × B
  ; left   = proj₁
  ; right  = proj₂
  }

-- Joins.
--
-- This definition is taken from the HoTT book.

Join : Type a → Type b → Type (a ⊔ b)
Join A B = Pushout (Join-span A B)

------------------------------------------------------------------------
-- Some simple properties

-- Join is symmetric.

Join-symmetric : Join A B ≃ Join B A
Join-symmetric = Eq.↔→≃
  to
  to
  to-to
  to-to
  where
  to : Join A B → Join B A
  to = rec inr inl (sym ∘ glue ∘ swap)

  to-to : (x : Join A B) → to (to x) ≡ x
  to-to =
    PO.elim _ (λ _ → refl _) (λ _ → refl _)
      (λ p →
         subst (λ x → to (to x) ≡ x) (glue p) (refl _)         ≡⟨ subst-in-terms-of-trans-and-cong ⟩

         trans (sym (cong (to ∘ to) (glue p)))
           (trans (refl _) (cong id (glue p)))                 ≡⟨ cong₂ (trans ∘ sym)
                                                                    (sym $ cong-∘ _ _ _)
                                                                    (trans (trans-reflˡ _) $
                                                                     sym $ cong-id _) ⟩

         trans (sym (cong to (cong to (glue p)))) (glue p)     ≡⟨ cong (flip trans _) $ cong (sym ∘ cong to) rec-glue ⟩

         trans (sym (cong to (sym (glue (swap p))))) (glue p)  ≡⟨ cong (flip trans _) $ cong sym $ cong-sym _ _ ⟩

         trans (sym (sym (cong to (glue (swap p))))) (glue p)  ≡⟨ cong (flip trans _) $ sym-sym _ ⟩

         trans (cong to (glue (swap p))) (glue p)              ≡⟨ cong (flip trans _) rec-glue ⟩

         trans (sym (glue (swap (swap p)))) (glue p)           ≡⟨⟩

         trans (sym (glue p)) (glue p)                         ≡⟨ trans-symˡ _ ⟩∎

         refl _                                                ∎)

-- The empty type is a right identity for Join.

Join-⊥ʳ : Join A (⊥ {ℓ = ℓ}) ≃ A
Join-⊥ʳ = Eq.↔→≃
  (rec id ⊥-elim (λ { (_ , ()) }))
  inl
  refl
  (PO.elim _ (λ _ → refl _) (λ ()) (λ { (_ , ()) }))

-- The empty type is a left identity for Join.

Join-⊥ˡ : Join (⊥ {ℓ = ℓ}) A ≃ A
Join-⊥ˡ {A = A} =
  Join ⊥ A  ↝⟨ Join-symmetric ⟩
  Join A ⊥  ↝⟨ Join-⊥ʳ ⟩□
  A         □

-- The unit type is a left zero for Join.
--
-- I based this lemma on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters (see Example 1.8), but I suspect that
-- the result is well-known.

Join-⊤ˡ : Join ⊤ A ≃ ⊤
Join-⊤ˡ = Eq.↔→≃
  _
  inl
  refl
  (PO.elim _
     (λ _ → refl _)
     (λ x → glue (tt , x))
     (λ (_ , x) →
        subst (inl tt ≡_) (glue (tt , x)) (refl (inl tt))  ≡⟨ sym trans-subst ⟩
        trans (refl (inl tt)) (glue (tt , x))              ≡⟨ trans-reflˡ _ ⟩∎
        glue (tt , x)                                      ∎))

-- The unit type is a right zero for Join.

Join-⊤ʳ : Join A ⊤ ≃ ⊤
Join-⊤ʳ {A = A} =
  Join A ⊤  ↝⟨ Join-symmetric ⟩
  Join ⊤ A  ↝⟨ Join-⊤ˡ ⟩□
  ⊤         □

-- Join A (¬ A) is equivalent to Dec A.
--
-- This lemma is used in (at least my variant of) Christian Sattler's
-- proof of Very-modal-Closed≃Dec (see below).

Join-¬≃Dec : Join A (¬ A) ≃ Dec A
Join-¬≃Dec = Eq.↔→≃
  (rec inj₁ inj₂ lemma)
  [ inl , inr ]
  [ (λ _ → refl _) , (λ _ → refl _) ]
  (PO.elim _ (λ _ → refl _) (λ _ → refl _) lemma)
  where
  lemma : (p : A × ¬ A) → P p
  lemma (inh , not-inh) = ⊥-elim (not-inh inh)

------------------------------------------------------------------------
-- Preservation lemmas

-- A map function.

Join-map : (A → C) → (B → D) → Join A B → Join C D
Join-map f g = PO.rec (inl ∘ f) (inr ∘ g) (λ _ → glue _)

-- Join preserves logical equivalences.

Join-cong-⇔ : A ⇔ C → B ⇔ D → Join A B ⇔ Join C D
Join-cong-⇔ A⇔C B⇔D = record
  { to   = Join-map (_⇔_.to   A⇔C) (_⇔_.to   B⇔D)
  ; from = Join-map (_⇔_.from A⇔C) (_⇔_.from B⇔D)
  }

-- Join preserves split surjections.

Join-cong-↠ : A ↠ C → B ↠ D → Join A B ↠ Join C D
Join-cong-↠ A↠C B↠D = record
  { logical-equivalence = equiv
  ; right-inverse-of    =
      PO.elim _
        (λ x →
           inl (_↠_.to A↠C (_↠_.from A↠C x))  ≡⟨ cong inl $ _↠_.right-inverse-of A↠C _ ⟩∎
           inl x                              ∎)
        (λ x →
           inr (_↠_.to B↠D (_↠_.from B↠D x))  ≡⟨ cong inr $ _↠_.right-inverse-of B↠D _ ⟩∎
           inr x                              ∎)
        (λ (x , y) →
           subst (λ z → _⇔_.to equiv (_⇔_.from equiv z) ≡ z)
             (glue (x , y))
             (cong inl (_↠_.right-inverse-of A↠C x))               ≡⟨ subst-in-terms-of-trans-and-cong ⟩

           trans (sym (cong (_⇔_.to equiv ∘ _⇔_.from equiv)
                         (glue (x , y))))
             (trans (cong inl (_↠_.right-inverse-of A↠C x))
                (cong id (glue (x , y))))                          ≡⟨ cong₂ trans
                                                                        (cong sym $ sym $ cong-∘ _ _ _)
                                                                        (cong (trans _) $ sym $ cong-id _) ⟩
           trans (sym (cong (_⇔_.to equiv)
                         (cong (_⇔_.from equiv) (glue (x , y)))))
             (trans (cong inl (_↠_.right-inverse-of A↠C x))
                (glue (x , y)))                                    ≡⟨ cong (flip trans _) $ cong sym $
                                                                      trans (cong (cong _) PO.rec-glue) $
                                                                      PO.rec-glue ⟩
           trans (sym (glue ( _↠_.to A↠C (_↠_.from A↠C x)
                            , _↠_.to B↠D (_↠_.from B↠D y)
                            )))
             (trans (cong inl (_↠_.right-inverse-of A↠C x))
                (glue (x , y)))                                    ≡⟨ elim₁
                                                                        (λ {x′} eq →
                                                                           trans (sym (glue (x′ , _↠_.to B↠D (_↠_.from B↠D y))))
                                                                             (trans (cong inl eq) (glue (x , y))) ≡
                                                                           cong inr (_↠_.right-inverse-of B↠D y))
                                                                        (elim₁
                                                                           (λ {y′} eq →
                                                                              trans (sym (glue (x , y′)))
                                                                                (trans (cong inl (refl _)) (glue (x , y))) ≡
                                                                              cong inr eq)
                                                                           (trans (trans (cong (trans _) $
                                                                                          trans (cong (flip trans _) $
                                                                                                 cong-refl _) $
                                                                                          trans-reflˡ _) $
                                                                                   trans-symˡ _) $
                                                                            sym $ cong-refl _)
                                                                           _)
                                                                        _ ⟩∎
           cong inr (_↠_.right-inverse-of B↠D y)                   ∎)
  }
  where
  equiv =
    Join-cong-⇔
      (_↠_.logical-equivalence A↠C)
      (_↠_.logical-equivalence B↠D)

-- Join preserves bijections.

Join-cong-↔ : A ↔ C → B ↔ D → Join A B ↔ Join C D
Join-cong-↔ A↔C B↔D = record
  { surjection =
      Join-cong-↠
        (_↔_.surjection A↔C)
        (_↔_.surjection B↔D)
  ; left-inverse-of =
      _↠_.right-inverse-of $
        Join-cong-↠
          (_↔_.surjection $ inverse A↔C)
          (_↔_.surjection $ inverse B↔D)
  }

-- Join preserves equivalences.

Join-cong-≃ : A ≃ C → B ≃ D → Join A B ≃ Join C D
Join-cong-≃ A≃C B≃D =
  Eq.↔⇒≃ $ Join-cong-↔ (_≃_.bijection A≃C) (_≃_.bijection B≃D)

-- Join preserves equivalences with erased proofs.

Join-cong-≃ᴱ : A ≃ᴱ C → B ≃ᴱ D → Join A B ≃ᴱ Join C D
Join-cong-≃ᴱ A≃ᴱC B≃ᴱD =
  EEq.[≃]→≃ᴱ (EEq.[proofs] $ Join-cong-≃ (EEq.≃ᴱ→≃ A≃ᴱC) (EEq.≃ᴱ→≃ B≃ᴱD))

------------------------------------------------------------------------
-- Some negative results

-- The constructor inl is not necessarily injective.

¬-Injective-inl :
  ¬ ({A : Type a} {B : Type b} → Injective (inl {S = Join-span A B}))
¬-Injective-inl =
  (∀ {A B} → Injective (inl {S = Join-span A B}))                →⟨ (λ hyp → hyp) ⟩
  Injective (inl {S = Join-span (↑ _ Bool) (↑ _ ⊤)})             →⟨ (λ hyp → hyp) ⟩
  (inl (lift true) ≡ inl (lift false) → lift true ≡ lift false)  →⟨ _$ inl-true≡inl-false ⟩
  lift true ≡ lift false                                         →⟨ Bool.true≢false ∘ cong lower ⟩□
  ⊥                                                              □
  where
  inl-true≡inl-false =
    inl (lift true)   ≡⟨ glue _ ⟩
    inr (lift tt)     ≡⟨ sym $ glue _ ⟩∎
    inl (lift false)  ∎

-- The constructor inl is not necessarily an embedding.

¬-Is-embedding-inl :
  ¬ ({A : Type a} {B : Type b} → Is-embedding (inl {S = Join-span A B}))
¬-Is-embedding-inl =
  (∀ {A B} → Is-embedding (inl {S = Join-span A B}))  →⟨ (λ hyp → Emb.injective hyp) ⟩
  (∀ {A B} → Injective (inl {S = Join-span A B}))     →⟨ ¬-Injective-inl ⟩□
  ⊥                                                   □

-- The constructor inr is not necessarily injective.

¬-Injective-inr :
  ¬ ({A : Type a} {B : Type b} → Injective (inr {S = Join-span A B}))
¬-Injective-inr =
  (∀ {A B} → Injective (inr {S = Join-span A B}))                →⟨ (λ hyp → hyp) ⟩
  Injective (inr {S = Join-span (↑ _ ⊤) (↑ _ Bool)})             →⟨ (λ hyp → hyp) ⟩
  (inr (lift true) ≡ inr (lift false) → lift true ≡ lift false)  →⟨ _$ inr-true≡inr-false ⟩
  lift true ≡ lift false                                         →⟨ Bool.true≢false ∘ cong lower ⟩□
  ⊥                                                              □
  where
  inr-true≡inr-false =
    inr (lift true)   ≡⟨ sym $ glue _ ⟩
    inl (lift tt)     ≡⟨ glue _ ⟩∎
    inr (lift false)  ∎

-- The constructor inr is not necessarily an embedding.

¬-Is-embedding-inr :
  ¬ ({A : Type a} {B : Type b} → Is-embedding (inr {S = Join-span A B}))
¬-Is-embedding-inr =
  (∀ {A B} → Is-embedding (inr {S = Join-span A B}))  →⟨ (λ hyp → Emb.injective hyp) ⟩
  (∀ {A B} → Injective (inr {S = Join-span A B}))     →⟨ ¬-Injective-inr ⟩□
  ⊥                                                   □

-- It is not the case that Join preserves injections.

¬-Join-cong-↣ :
  ¬ (∀ {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
     A ↣ C → B ↣ D → Join A B ↣ Join C D)
¬-Join-cong-↣ =
  (∀ {A B C D} → A ↣ C → B ↣ D → Join A B ↣ Join C D)  →⟨ (λ hyp → hyp) ⟩

  (↑ _ Bool ↣ ↑ _ Bool → ⊥ ↣ ↑ _ ⊤ →
   Join (↑ _ Bool) ⊥ ↣ Join (↑ _ Bool) (↑ _ ⊤))        →⟨ (λ hyp → hyp Bool↣Bool ⊥↣⊤) ⟩

  Join (↑ _ Bool) ⊥ ↣ Join (↑ _ Bool) (↑ _ ⊤)          →⟨ (λ hyp →

    Bool                                                     ↔⟨ inverse B.↑↔ ⟩
    ↑ _ Bool                                                 ↔⟨ inverse Join-⊥ʳ ⟩
    Join (↑ _ Bool) ⊥                                        ↝⟨ hyp ⟩
    Join (↑ _ Bool) (↑ _ ⊤)                                  ↔⟨ Join-cong-↔ F.id B.↑↔ ⟩
    Join (↑ _ Bool) ⊤                                        ↔⟨ Join-⊤ʳ ⟩□
    ⊤                                                        □) ⟩

  Bool ↣ ⊤                                             →⟨ (λ hyp → _↣_.injective hyp (refl _)) ⟩

  true ≡ false                                         →⟨ Bool.true≢false ⟩□

  ⊥                                                    □
  where
  Bool↣Bool =
    ↑ _ Bool  ↔⟨ B.↑↔ ⟩
    Bool      ↔⟨ inverse B.↑↔ ⟩□
    ↑ _ Bool  □

  ⊥↣⊤ = record
    { to        = λ ()
    ; injective = λ {}
    }

-- It is not the case that Join preserves embeddings.

¬-Join-cong-Embedding :
  ¬ (∀ {A : Type a} {B : Type b} {C : Type c} {D : Type d} →
     Embedding A C → Embedding B D → Embedding (Join A B) (Join C D))
¬-Join-cong-Embedding =
  (∀ {A B C D} →
   Embedding A C → Embedding B D → Embedding (Join A B) (Join C D))  →⟨ (λ hyp → hyp) ⟩

  (Embedding (↑ _ Bool) (↑ _ Bool) → Embedding ⊥ (↑ _ ⊤) →
   Embedding (Join (↑ _ Bool) ⊥) (Join (↑ _ Bool) (↑ _ ⊤)))          →⟨ (λ hyp → hyp Bool↣Bool ⊥↣⊤) ⟩

  Embedding (Join (↑ _ Bool) ⊥) (Join (↑ _ Bool) (↑ _ ⊤))            →⟨ (λ hyp →

    Bool                                                                   ↔⟨ inverse B.↑↔ ⟩
    ↑ _ Bool                                                               ↔⟨ inverse Join-⊥ʳ ⟩
    Join (↑ _ Bool) ⊥                                                      ↝⟨ hyp ⟩
    Join (↑ _ Bool) (↑ _ ⊤)                                                ↔⟨ Join-cong-↔ F.id B.↑↔ ⟩
    Join (↑ _ Bool) ⊤                                                      ↔⟨ Join-⊤ʳ ⟩□
    ⊤                                                                      □) ⟩

  Embedding Bool ⊤                                                   →⟨ (λ hyp → Emb.injective (Embedding.is-embedding hyp) (refl _)) ⟩

  true ≡ false                                                       →⟨ Bool.true≢false ⟩□

  ⊥                                                                  □
  where
  Bool↣Bool =
    ↑ _ Bool  ↔⟨ B.↑↔ ⟩
    Bool      ↔⟨ inverse B.↑↔ ⟩□
    ↑ _ Bool  □

  ⊥↣⊤ = record
    { to           = λ ()
    ; is-embedding = λ ()
    }

------------------------------------------------------------------------
-- The closed modality

private

  -- A lemma used below.

  Join≃⊤ : Is-proposition A → A → Join A B ≃ ⊤
  Join≃⊤ {A = A} {B = B} prop x =
    Join A B  ↔⟨ flip Join-cong-↔ F.id $
                 _⇔_.to contractible⇔↔⊤ $
                 propositional⇒inhabited⇒contractible prop x ⟩
    Join ⊤ B  ↝⟨ Join-⊤ˡ ⟩□
    ⊤         □

-- The closed modality related to a proposition.
--
-- This definition is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Closed : (A : Type a) → Is-proposition A → Modality a
Closed A prop = Σ-closed-reflective-subuniverse.modality λ where
  .Σ-closed-reflective-subuniverse.◯ → Join A

  .Σ-closed-reflective-subuniverse.η → inr

  .Σ-closed-reflective-subuniverse.Modal B →
    A → Contractible B

  .Σ-closed-reflective-subuniverse.Modal-propositional ext →
    Π-closure ext 1 λ _ →
    H-level-propositional ext 0

  .Σ-closed-reflective-subuniverse.Modal-◯ {A = B} →
    A                        →⟨ Join≃⊤ prop ⟩
    Join A B ≃ ⊤             ↔⟨ inverse $ contractible↔≃⊤ ext ⟩□
    Contractible (Join A B)  □

  .Σ-closed-reflective-subuniverse.Modal-respects-≃ {A = B} {B = C} B≃C →
    (A → Contractible B)  →⟨ (∀-cong _ λ _ → H-level-cong _ 0 B≃C) ⟩□
    (A → Contractible C)  □

  .Σ-closed-reflective-subuniverse.Σ-closed mB mQ x →
    Σ-closure 0 (mB x) (flip mQ x)

  .Σ-closed-reflective-subuniverse.extendable-along-η {B = C} {A = B} →
    let lemma hyp =
          _≃_.is-equivalence $
            ((Join A B → C)                                               ↔⟨ PO.Pushout→↔Cocone ⟩

             (∃ λ (f : A → C) → ∃ λ (g : B → C) →
                ((x , y) : A × B) → f x ≡ g y)                            ↔⟨ ∃-comm ⟩

             (∃ λ (g : B → C) → ∃ λ (f : A → C) →
                ((x , y) : A × B) → f x ≡ g y)                            ↔⟨ (∃-cong λ _ →
                                                                              drop-⊤-left-Σ
                                                                                (
                (A → C)                                                          ↝⟨ (∀-cong ext λ x →
                                                                                     _⇔_.to contractible⇔↔⊤ $
                                                                                     hyp x) ⟩
                (A → ⊤)                                                          ↝⟨ →-right-zero ⟩□
                ⊤                                                                □)) ⟩

             (∃ λ (g : B → C) → ((x , y) : A × B) → proj₁ (hyp x) ≡ g y)  ↔⟨ (drop-⊤-right λ _ →
                                                                              _⇔_.to contractible⇔↔⊤ $
                                                                              Π-closure ext 0 λ (x , _) →
                                                                              H-level.⇒≡ 0 $ hyp x) ⟩□
             (B → C)                                                      □)
    in
    (A → Contractible C)                                  →⟨ lemma ⟩
    Is-equivalence (λ (f : Join A B → C) → f ∘ inr)       ↔⟨ inverse $ PS.Is-∞-extendable-along≃Is-equivalence ext ⟩□
    Is-∞-extendable-along-[ inr ] (λ (_ : Join A B) → C)  □

-- Closed A prop is topological.
--
-- This definition is based on "Modalities in Homotopy Type Theory" by
-- Rijke, Shulman and Spitters.

Closed-topological :
  {A : Type a}
  (prop : Is-proposition A) →
  Topological (Closed A prop)
Closed-topological {A = A} prop =
    ( A
    , (λ _ → ⊥)
    , (λ B →
         (A → Contractible B)                                             ↔⟨ (∀-cong ext λ _ → contractible↔≃⊤ ext) ⟩
         (A → B ≃ ⊤)                                                      ↔⟨ (∀-cong ext λ _ → Eq.≃-preserves ext F.id (inverse $ Π⊥↔⊤ ext)) ⟩
         (A → B ≃ (⊥ → B))                                                ↝⟨ (∀-cong _ λ _ → record
                                                                                { from = Eq.⟨ _ ,_⟩
                                                                                ; to   = λ eq →
                                                                                    _≃_.is-equivalence $
                                                                                    Eq.with-other-function
                                                                                      eq
                                                                                      const
                                                                                      (λ _ → ⟨ext⟩ λ ())
                                                                                }) ⟩
         (A → Is-equivalence (const ⦂ (B → ⊥ → B)))                       ↔⟨ (∀-cong ext λ _ → inverse $
                                                                              PS.Is-∞-extendable-along≃Is-equivalence-const ext) ⟩□
         (A → Is-∞-extendable-along-[ (λ (_ : ⊥) → lift tt) ] (λ _ → B))  □)
    )
  , (λ _ → ⊥-propositional)

-- Closed A prop is empty-modal exactly when ¬ A holds.
--
-- Something like this was suggested by the audience (Thierry Coquand
-- as well as one or more other persons) when I presented some work to
-- the Proglog group.

Empty-modal-Closed≃¬ :
  (prop : Is-proposition A) →
  Empty-modal (Closed A prop) ≃ (¬ A)
Empty-modal-Closed≃¬ {A = A} prop =
  (A → Contractible ⊥)  ↝⟨ (∀-cong ext λ _ → _⇔_.from (≃⊥≃¬ _) ¬-⊥-contractible) ⟩□
  (A → ⊥)               □

-- The following two lemmas are due to Christian Sattler. (I was not
-- informed of these lemmas directly by Christian, so perhaps his
-- formulation was a bit different.) I think Christian came up with
-- these lemmas after David Wärn told him how one could construct a
-- model that showed that it is not the case that every topological
-- modality is very modal.

-- Closed A prop is very modal exactly when Dec A holds.

Very-modal-Closed≃Dec :
  (prop : Is-proposition A) →
  Very-modal (Closed A prop) ≃ Dec A
Very-modal-Closed≃Dec {A = A} prop =
  Eq.⇔→≃
    (Very-modal-propositional ext (Closed _ prop))
    (Dec-closure-propositional ext prop)
    (Very-modal (Closed A prop)  →⟨ (λ very-modal → very-modal) ⟩
     Join A (Modal ⊥)            →⟨ ◯-map Modal→Stable ⟩
     Join A (Join A ⊥ → ⊥)       ↔⟨ ◯-cong-≃ $ →-cong ext Join-⊥ʳ (from-bijection ⊥↔⊥) ⟩
     Join A (¬ A)                ↔⟨ Join-¬≃Dec ⟩□
     Dec A                       □)
    [ (λ inh → inl inh) , (λ not-inh → inr (⊥-elim ∘ not-inh)) ]
  where
  open Modality (Closed A prop)

-- Closed is very modal for every proposition (in a certain universe)
-- exactly when excluded middle holds (for that universe).

Very-modal-Closed≃Excluded-middle :
  ({A : Type a} (prop : Is-proposition A) →
   Very-modal (Closed A prop)) ≃
  Excluded-middle a
Very-modal-Closed≃Excluded-middle =
  implicit-∀-cong ext $
  ∀-cong ext λ prop →
  Very-modal-Closed≃Dec prop

-- Closed A prop is accessibility-modal for a relation exactly when
-- ¬ A holds.

Accessibility-modal-for-Closed≃¬ :
  {_<_ : B → B → Type a} →
  (prop : Is-proposition A) →
  Modality.Accessibility-modal-for (Closed A prop) _<_ ≃ (¬ A)
Accessibility-modal-for-Closed≃¬ {a = a} {A = A} {_<_ = _<_} prop =
  Eq.⇔→≃
    (Accessibility-modal-for-propositional ext)
    (¬-propositional ext)
    (flip λ x →
       let witness : {B : Type a} → Join A B
           witness = λ {B = B} →
                       $⟨ _ ⟩
             ⊤         ↝⟨ inverse $ Join≃⊤ prop x ⟩□
             Join A B  □
       in
       Accessibility-modal-for _<_         →⟨ Stable-Acc-[]◯ ⟩
       Stable (A.Acc _[ _<_ ]◯_ (inl x))   →⟨ Stable-respects-⇔ record
                                                { to   = λ acc → A.Acc-map (λ _ → witness) acc
                                                ; from = λ acc → A.Acc-map _ acc
                                                } ⟩
       Stable (A.Acc (λ _ _ → ⊤) (inl x))  →⟨ _$ witness ⟩
       A.Acc (λ _ _ → ⊤) (inl x)           →⟨ A.<→¬-Acc _ ⟩□
       ⊥                                   □)
    (¬ A                             →⟨ (λ not-inh →
                                             (λ acc → Modal→Acc→Acc-[]◯-η (⊥-elim ∘ not-inh) (stable not-inh) acc)
                                           , stable not-inh) ⟩□
     Accessibility-modal-for _<_     □)
  where
  open Modality (Closed A prop)

  stable : ¬ A → Join A B → B
  stable {B = B} not-inh =
    Join A B   ↔⟨ Join-cong-≃ (_⇔_.from (≃⊥≃¬ _) not-inh) F.id ⟩
    Join ⊥₀ B  ↔⟨ Join-⊥ˡ ⟩□
    B          □

-- Closed A prop is accessibility-modal exactly when ¬ A holds.

Accessibility-modal-Closed≃¬ :
  (prop : Is-proposition A) →
  Modality.Accessibility-modal (Closed A prop) ≃ (¬ A)
Accessibility-modal-Closed≃¬ {A = A} prop =
  Eq.⇔→≃
    (Accessibility-modal-propositional ext)
    (¬-propositional ext)
    (λ acc →
       _≃_.to (Accessibility-modal-for-Closed≃¬
                 {_<_ = λ (_ _ : ⊥) → ⊥}
                 prop)
         acc)
    (λ not-inh →
       _≃_.from (Accessibility-modal-for-Closed≃¬ prop) not-inh)
  where
  open Modality (Closed A prop)

-- Closed A prop is accessibility-modal exactly when it is
-- empty-modal.

Accessibility-modal-Closed≃Empty-modal-Closed :
  (prop : Is-proposition A) →
  Modality.Accessibility-modal (Closed A prop) ≃
  Empty-modal (Closed A prop)
Accessibility-modal-Closed≃Empty-modal-Closed {A = A} prop =
  Accessibility-modal          ↝⟨ Accessibility-modal-Closed≃¬ prop ⟩
  ¬ A                          ↝⟨ inverse $ Empty-modal-Closed≃¬ prop ⟩□
  Empty-modal (Closed A prop)  □
  where
  open Modality (Closed A prop)

-- Closed A prop is W-modal exactly when it is empty-modal.

W-modal-Closed≃Empty-modal-Closed :
  (prop : Is-proposition A) →
  W-modal (Closed A prop) ≃
  Empty-modal (Closed A prop)
W-modal-Closed≃Empty-modal-Closed {A = A} prop =
  Eq.⇔→≃
    (W-modal-propositional {M = Closed A prop} ext)
    (Empty-modal-propositional {M = Closed A prop} ext)
    W-modal→Empty-modal
    (Empty-modal (Closed A prop)  →⟨ (λ hyp →
                                          _≃_.to (Empty-modal-Closed≃¬ prop) hyp
                                        , _≃_.from (Accessibility-modal-Closed≃Empty-modal-Closed prop) hyp) ⟩
     ¬ A × Accessibility-modal    →⟨ (λ (hyp₁ , hyp₂) →
                                        Very-modal.Modal-W
                                          (Closed A prop)
                                          (_≃_.from (Very-modal-Closed≃Dec prop) (inj₂ hyp₁))
                                          hyp₂ ext) ⟩□
     W-modal (Closed A prop)      □)
  where
  open Modality (Closed A prop)
