------------------------------------------------------------------------
-- Red-black trees with external invariants
------------------------------------------------------------------------

-- The implementation is based on Okasaki's presentation in "Red-black
-- trees in a functional setting" as well as the Wikipeda article on
-- red-black trees. The ordering invariant is handled using more or
-- less the approach described by McBride in "How to Keep Your
-- Neighbours in Order".

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
open import Prelude as P
import Total-order.Erased

module Tree.Red-black.External-invariants
  {e⁺} (eq : ∀ {a p} → Equality-with-J a p e⁺)
  (open Total-order.Erased eq)
  {a o}
  -- The carrier type.
  {A : Type a}
  -- The carrier type is assumed to be totally ordered.
  (O : Total-order A o)
  where

open Derived-definitions-and-properties eq

open import Logical-equivalence using (_⇔_)

import Bag-equivalence eq as L
open import Equality.Decision-procedures eq
open import Equivalence eq as Eq using (_≃_)
open import Erased.Level-1 eq
open import Function-universe eq as F hiding (id; _∘_; if-lemma)
import H-level eq as H-level
open import H-level.Closure eq
open import List eq
open import Maybe eq
import Nat eq as N
import Total-order.Erased eq as TE

private
  open module O  = TE.Total-order O using (_<_; _>_; _≤_)
  open module EO = TE.Total-order (extended O)
    using () renaming (_<_ to _<ᴱ_)

open Sorted-list O

private variable
  @0 b                              : Bool
  @0 m n n′ n₁ n₂                   : ℕ
  @0 xs                             : List _
  @0 x x₁ x₂ x₄ y z                 : A
  @0 b₁ b₂ b₃ lb lb₁ lb₂ ub ub₁ ub₂ : Extended _

------------------------------------------------------------------------
-- A lemma used below

private opaque

  -- A lemma used below.

  @0 if-lemma :
    (b ≡ true → n ≢ 0) →
    let n′ = if b then N.pred n else n in
    n ≡ if b then suc n′ else n′
  if-lemma {b = true} {n = zero}  hyp = ⊥-elim (hyp (refl _) (refl _))
  if-lemma {b = true} {n = suc _} _   = refl _
  if-lemma {b = false}            _   = refl _

------------------------------------------------------------------------
-- Colours

-- Colours.

Colour : Type
Colour = Bool

pattern red   = false
pattern black = true

private variable
  @0 c c₁ c₂ pc : Colour

opaque

  -- Is the colour black?

  is-black : Colour → Bool
  is-black black = true
  is-black red   = false

------------------------------------------------------------------------
-- Trees with colours

-- Trees with colours but no invariants.

data Tree⁻ : Type a where
  leaf : Tree⁻
  node : (c : Colour) (l : Tree⁻) (x : A) (r : Tree⁻) → Tree⁻

pattern nodeᶜ c = node c _ _ _
pattern node⁰   = node _ _ _ _

private variable
  t                              : Tree⁻
  @0 l l₁ l₂ r r₁ r₂ t′ t₁ t₃ t₅ : Tree⁻

------------------------------------------------------------------------
-- Some simple lemmas

opaque

  -- Nodes are not equal to leaves.

  @0 node≢leaf : node c l x r ≢ leaf
  node≢leaf = flip (subst id) _ ∘ cong F
    where
    F : Tree⁻ → Type
    F node⁰ = ⊤
    F leaf  = ⊥

opaque

  -- The node constructor is injective.

  @0 node-injective :
    node c₁ l₁ x₁ r₁ ≡ node c₂ l₂ x₂ r₂ →
    c₁ ≡ c₂ × l₁ ≡ l₂ × x₁ ≡ x₂ × r₁ ≡ r₂
  node-injective {c₁} {l₁} {x₁} {r₁} {c₂} {l₂} {x₂} {r₂} =
    node c₁ l₁ x₁ r₁ ≡ node c₂ l₂ x₂ r₂                  ↔⟨ inverse (Eq.≃-≡ equiv) ⟩
    inj₂ (c₁ , l₁ , x₁ , r₁) ≡ inj₂ (c₂ , l₂ , x₂ , r₂)  ↝⟨ ⊎.cancel-inj₂ ⟩
    (c₁ , l₁ , x₁ , r₁) ≡ (c₂ , l₂ , x₂ , r₂)            ↔⟨ (∃-cong λ _ →
                                                             (∃-cong λ _ → inverse ≡×≡↔≡) F.∘
                                                             inverse ≡×≡↔≡) F.∘
                                                            inverse ≡×≡↔≡ ⟩
    c₁ ≡ c₂ × l₁ ≡ l₂ × x₁ ≡ x₂ × r₁ ≡ r₂                □
    where
    equiv : Tree⁻ ≃ (⊤ ⊎ Colour × Tree⁻ × A × Tree⁻)
    equiv = Eq.↔→≃
      (λ where
         leaf           → inj₁ tt
         (node c l x r) → inj₂ (c , l , x , r))
      P.[ _ , _ ]
      P.[ refl ∘ inj₁ , refl ∘ inj₂ ]
      (λ where
         leaf           → refl _
         (node _ _ _ _) → refl _)

------------------------------------------------------------------------
-- Red-black trees

opaque

  -- The red invariant: red nodes do not have red parents.

  @0 Red-invariant : Colour → Colour → Type
  Red-invariant red red = ⊥
  Red-invariant _   _   = ⊤

opaque

  -- The black invariant implies that the number of black nodes is
  -- equal on every path from the root to a leaf.

  @0 Black-invariant : Colour → ℕ → ℕ → Type
  Black-invariant red   m n = n ≡ m
  Black-invariant black m n = n ≡ suc m

-- Red-black tree invariants.
--
-- The colour parameter is the *parent's* colour (if any). The natural
-- number parameter is the number of black nodes on every path from
-- the root to a leaf. The parameter lb is a lower bound for the nodes
-- in the tree, and ub is an upper bound.

@0 Red-black : Colour → ℕ → (_ _ : Extended A) → Tree⁻ → Type (a ⊔ o)
Red-black _  n lb ub leaf           = lb <ᴱ ub × n ≡ 0
Red-black pc n lb ub (node c l x r) =
  ∃ λ m →
  Red-black c m lb [ x ] l ×
  Red-black c m [ x ] ub r ×
  Red-invariant pc c ×
  Black-invariant c m n

pattern leafʳᵇ lb<ub n≡0     = lb<ub , n≡0
pattern nodeʳᵇ l r rinv binv = _ , l , r , rinv , binv

------------------------------------------------------------------------
-- Some lemmas related to Red-invariant

opaque
  unfolding Red-invariant

  -- Red-invariant is propositional.

  @0 Red-invariant-propositional :
    Is-proposition (Red-invariant pc c)
  Red-invariant-propositional {pc = red}   {c = red} =
    ⊥-propositional
  Red-invariant-propositional {pc = red}   {c = black} =
    H-level.mono₁ 0 ⊤-contractible
  Red-invariant-propositional {pc = black} =
    H-level.mono₁ 0 ⊤-contractible

opaque
  unfolding Red-invariant

  -- The red invariant holds for black children.

  @0 black-child : Red-invariant pc black
  black-child {pc = black} = _
  black-child {pc = red}   = _

opaque
  unfolding Red-invariant

  -- The red invariant holds for black parents.

  @0 black-parent : Red-invariant black c
  black-parent = _

opaque
  unfolding Red-invariant

  -- The red invariant does not hold for two red nodes.

  @0 not-red-red : ¬ Red-invariant red red
  not-red-red ()

opaque
  unfolding Red-invariant

  -- If the red invariant holds for pc and red, then it holds for pc
  -- and c.

  @0 red-child : ∀ {pc} → Red-invariant pc red → Red-invariant pc c
  red-child {pc = red}   inv = ⊥-elim (not-red-red inv)
  red-child {pc = black} _   = _

opaque
  unfolding Red-invariant

  -- If the red invariant holds for red and c, then it holds for pc
  -- and c.

  @0 red-parent : Red-invariant red c → Red-invariant pc c
  red-parent {c = red}   inv = ⊥-elim (not-red-red inv)
  red-parent {c = black} _   = black-child

------------------------------------------------------------------------
-- Some lemmas related to Black-invariant

opaque
  unfolding Black-invariant

  -- Black-invariant is propositional.

  @0 Black-invariant-propositional :
    Is-proposition (Black-invariant c m n)
  Black-invariant-propositional {c = black} = ℕ-set
  Black-invariant-propositional {c = red}   = ℕ-set

opaque
  unfolding Black-invariant

  -- The black invariant is preserved (possibly for a different second
  -- number) if the root is coloured black.

  @0 black-black :
    Black-invariant c m n →
    ∃ (Black-invariant black m)
  black-black {c = red}   eq = _ , cong suc eq
  black-black {c = black} eq = _ , eq

  -- If Black-invariant c m n holds, then n is bounded by suc m.

  @0 Black-invariant→≤ :
    Black-invariant c m n → n N.≤ suc m
  Black-invariant→≤ {c = black}         eq = N.≤-refl′ eq
  Black-invariant→≤ {c = red}   {m} {n} eq =
    n      N.≡⟨ eq ⟩≤
    m      N.≤⟨ N.pred≤ _ ⟩∎
    suc m  ∎≤

  -- If Black-invariant c m n holds and m is non-zero, then n is
  -- non-zero.

  @0 Black-invariant→≢0→≢0 :
    Black-invariant c m n → m ≢ 0 → n ≢ 0
  Black-invariant→≢0→≢0 {c = black} n≡1+m _ n≡0 =
    N.0≢+ (trans (sym n≡0) n≡1+m)
  Black-invariant→≢0→≢0 {c = red} n≡m m≢0 n≡0 =
    m≢0 (trans (sym n≡m) n≡0)

  -- If Black-invariant c (suc m) n holds, then Black-invariant c
  -- holds for m and the predecessor of n.

  @0 Black-invariant-pred :
    Black-invariant c (suc m) n → Black-invariant c m (N.pred n)
  Black-invariant-pred {c = red}   = cong N.pred
  Black-invariant-pred {c = black} = cong N.pred

  -- A lemma with a somewhat convoluted statement.

  @0 Black-invariant-lemma :
    ∀ c (b b′ : Bool) →
    let n″ = if b then N.pred n′ else n′ in
    (b ≡ true → n′ ≢ 0) →
    (b′ ≡ true → b ≡ true) →
    Black-invariant c n′ n →
    Black-invariant c
      (if b′ then n″ else (if b then suc n″ else n″))
      (if b′ then N.pred n else n)
  Black-invariant-lemma c _ false hyp _ =
    subst (flip (Black-invariant c) _) (if-lemma hyp)
  Black-invariant-lemma {n′ = zero} _ true true hyp _ =
    ⊥-elim (hyp (refl _) (refl _))
  Black-invariant-lemma {n′ = suc _} c true true _ _ =
    Black-invariant-pred {c = c}
  Black-invariant-lemma _ false true _ hyp =
    ⊥-elim (Bool.true≢false (sym (hyp (refl _))))

------------------------------------------------------------------------
-- The predicate Red-black is propositional

opaque
  unfolding Black-invariant

  -- The black height is unique.

  @0 black-height-unique :
    Red-black pc n₁ lb ub t →
    Red-black pc n₂ lb ub t →
    n₁ ≡ n₂
  black-height-unique
    {n₁} {t = leaf} {n₂} (leafʳᵇ _ n₁≡0) (leafʳᵇ _ n₂≡0) =
    n₁  ≡⟨ n₁≡0 ⟩
    0   ≡⟨ sym n₂≡0 ⟩∎
    n₂  ∎
  black-height-unique
    {n₁} {t = nodeᶜ black} {n₂}
    (m₁ , l₁ , _ , _ , binv₁) (m₂ , l₂ , _ , _ , binv₂) =
    n₁      ≡⟨ binv₁ ⟩
    suc m₁  ≡⟨ cong suc (black-height-unique l₁ l₂) ⟩
    suc m₂  ≡⟨ sym binv₂ ⟩∎
    n₂      ∎
  black-height-unique
    {n₁} {t = nodeᶜ red} {n₂}
    (m₁ , l₁ , _ , _ , binv₁) (m₂ , l₂ , _ , _ , binv₂) =
    n₁  ≡⟨ binv₁ ⟩
    m₁  ≡⟨ black-height-unique l₁ l₂ ⟩
    m₂  ≡⟨ sym binv₂ ⟩∎
    n₂  ∎

opaque

  -- Red-black is propositional.

  @0 Red-black-propositional :
    Is-proposition (Red-black pc n lb ub t)
  Red-black-propositional {t = leaf} =
    ×-closure 1 EO.<-propositional ℕ-set
  Red-black-propositional {t = node⁰} =
    proj₁-unique→Σ-propositional
      (λ (_ , l₁ , _) (_ , l₂ , _) →
         black-height-unique l₁ l₂)
      (λ _ →
         ×-closure 1 Red-black-propositional $
         ×-closure 1 Red-black-propositional $
         ×-closure 1
           Red-invariant-propositional
           Black-invariant-propositional)

------------------------------------------------------------------------
-- Some lemmas related to the bounds

opaque

  -- The lower bound is strictly below the upper bound.

  @0 lower-bound-<-upper-bound : Red-black pc n lb ub t → lb <ᴱ ub
  lower-bound-<-upper-bound {t = leaf} (leafʳᵇ lb<ub _) =
    lb<ub
  lower-bound-<-upper-bound {t = node⁰} (nodeʳᵇ l r _ _) =
    EO.<-trans (lower-bound-<-upper-bound l)
      (lower-bound-<-upper-bound r)

opaque

  -- The lower bound can be decreased.

  @0 Red-black-<ˡ :
    lb₁ <ᴱ lb₂ → Red-black pc n lb₂ ub t → Red-black pc n lb₁ ub t
  Red-black-<ˡ {t = leaf} lb₁<lb₂ (leafʳᵇ lb₂<ub n≡0) =
    leafʳᵇ (EO.<-trans lb₁<lb₂ lb₂<ub) n≡0
  Red-black-<ˡ {t = node⁰} lb₁<lb₂ (nodeʳᵇ l r rinv binv) =
    nodeʳᵇ (Red-black-<ˡ lb₁<lb₂ l) r rinv binv

opaque

  -- The upper bound can be increased.

  @0 Red-black-<ʳ :
    ub₁ <ᴱ ub₂ → Red-black pc n lb ub₁ t → Red-black pc n lb ub₂ t
  Red-black-<ʳ {t = leaf} ub₁<ub₂ (leafʳᵇ lb<ub₁ n≡0) =
    leafʳᵇ (EO.<-trans lb<ub₁ ub₁<ub₂) n≡0
  Red-black-<ʳ {t = node⁰} ub₁<ub₂ (nodeʳᵇ l r rinv binv) =
    nodeʳᵇ l (Red-black-<ʳ ub₁<ub₂ r) rinv binv

------------------------------------------------------------------------
-- Heights and sizes

-- The height of a tree.

@0 height⁻ : Tree⁻ → ℕ
height⁻ leaf           = 0
height⁻ (node _ l _ r) = suc (N.max (height⁻ l) (height⁻ r))

-- The size of a tree.
--
-- The function is erased because it is (at least) linear in the size
-- of the tree, so it is not recommended to be used at run-time.

@0 size⁻ : Tree⁻ → ℕ
size⁻ leaf           = 0
size⁻ (node _ l _ r) = suc (size⁻ l + size⁻ r)

opaque

  -- A lemma relating the size of a tree to its height.

  @0 size⁻≤2^height⁻∸1 : size⁻ t N.≤ 2 ^ height⁻ t ∸ 1
  size⁻≤2^height⁻∸1 {t} = lemma t N.∸-mono N.≤-refl
    where
    lemma : ∀ t → 1 + size⁻ t N.≤ 2 ^ height⁻ t
    lemma leaf =
      N.≤-refl
    lemma (node _ l _ r) =
      2 + size⁻ l + size⁻ r                  N.≡⟨ N.suc+≡+suc (1 + _) ⟩≤

      (1 + size⁻ l) + (1 + size⁻ r)          N.≤⟨ lemma l N.+-mono lemma r ⟩

      2 ^ height⁻ l + 2 ^ height⁻ r          N.≤⟨ N.≤-refl N.⁺^-mono N.ˡ≤max (height⁻ l) _ N.+-mono
                                                  N.≤-refl N.⁺^-mono N.ʳ≤max (height⁻ l) _ ⟩
      2 ^ N.max (height⁻ l) (height⁻ r) +
      2 ^ N.max (height⁻ l) (height⁻ r)      N.≡⟨ sym (N.2*≡+ (2 ^ N.max (height⁻ l) _)) ⟩≤

      2 * 2 ^ N.max (height⁻ l) (height⁻ r)  N.∎≤

opaque
 unfolding Black-invariant
 mutual

  private

    -- A lemma used below.

    @0 black-case :
      ∀ l r →
      Red-black black m lb [ x ] l →
      Red-black black m [ x ] ub r →
      n ≡ 1 + m →
      1 + N.max (height⁻ l) (height⁻ r) N.≤ 2 * n
    black-case {m} {n} l r l-ok r-ok n≡1+m =
      1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ N.≤-refl N.+-mono
                                              N.max-mono (height⁻≤1+2*black-height l l-ok) (height⁻≤1+2*black-height r r-ok) ⟩
      1 + N.max (1 + 2 * m) (1 + 2 * m)  N.≡⟨ cong suc (N.max-idempotent _) ⟩≤
      2 + 2 * m                          N.≡⟨ sym (N.*-+-distribˡ 2 {n = 1}) ⟩≤
      2 * suc m                          N.≡⟨ cong (2 *_) (sym n≡1+m) ⟩≤
      2 * n                              N.∎≤

  -- For a red-black tree with a red parent colour the height is at
  -- most twice the black height.

  @0 height⁻≤2*black-height :
    ∀ t →
    Red-black red n lb ub t →
    height⁻ t N.≤ 2 * n
  height⁻≤2*black-height {n} leaf _ =
    0      N.≤⟨ N.zero≤ _ ⟩∎
    2 * n  ∎≤
  height⁻≤2*black-height
    {n} (node black l _ r) (nodeʳᵇ l-ok r-ok _ n≡1+m) =
    1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ black-case l r l-ok r-ok n≡1+m ⟩∎
    2 * n                              ∎≤
  height⁻≤2*black-height (nodeᶜ red) (nodeʳᵇ _ _ rinv _) =
    ⊥-elim (not-red-red rinv)

  -- For a red-black tree the height is at most one plus twice the
  -- black height.

  @0 height⁻≤1+2*black-height :
    ∀ t →
    Red-black pc n lb ub t →
    height⁻ t N.≤ 1 + 2 * n
  height⁻≤1+2*black-height {n} leaf _ =
    0          N.≤⟨ N.zero≤ _ ⟩∎
    1 + 2 * n  ∎≤
  height⁻≤1+2*black-height
    {n} (node black l _ r) (nodeʳᵇ l-ok r-ok _ n≡1+m) =
    1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ black-case l r l-ok r-ok n≡1+m ⟩
    2 * n                              N.≤⟨ N.pred≤ _ ⟩∎
    1 + 2 * n                          ∎≤
  height⁻≤1+2*black-height
    {n} (node red l _ r) (m , l-ok , r-ok , _ , n≡m) =
    1 + N.max (height⁻ l) (height⁻ r)  N.≤⟨ N.≤-refl N.+-mono N.max-mono (height⁻≤2*black-height l l-ok) (height⁻≤2*black-height r r-ok) ⟩
    1 + N.max (2 * m) (2 * m)          N.≡⟨ cong (1 +_) (N.max-idempotent _) ⟩≤
    1 + 2 * m                          N.≡⟨ cong ((1 +_) ∘ (2 *_)) (sym n≡m) ⟩≤
    1 + 2 * n                          N.∎≤

------------------------------------------------------------------------
-- Membership

-- Tree membership.

infix 4 _∈⁻_

_∈⁻_ : A → Tree⁻ → Type a
_ ∈⁻ leaf         = ⊥
x ∈⁻ node _ l y r = x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r

opaque

  -- If x is in a red-black tree, then x is strictly between any lower
  -- and upper bounds.

  @0 ∈⁻→<< :
    Red-black pc n lb ub t → x ∈⁻ t → lb <ᴱ [ x ] × [ x ] <ᴱ ub
  ∈⁻→<< {t = node⁰} (nodeʳᵇ l r _ _) (inj₁ x∈l) =
    let <x , x< = ∈⁻→<< l x∈l in
    <x , EO.<-trans x< (lower-bound-<-upper-bound r)
  ∈⁻→<< {t = node⁰} (nodeʳᵇ l r _ _) (inj₂ (inj₁ x≡y)) =
    EO.<-≤-trans (lower-bound-<-upper-bound l)
      (EO.≤-reflexive (cong [_] (sym x≡y))) ,
    EO.≤-<-trans (EO.≤-reflexive (cong [_] x≡y))
      (lower-bound-<-upper-bound r)
  ∈⁻→<< {t = node⁰} (nodeʳᵇ l r _ _) (inj₂ (inj₂ x∈r)) =
    let <x , x< = ∈⁻→<< r x∈r in
    EO.<-trans (lower-bound-<-upper-bound l) <x , x<

opaque

  -- If x is below a lower bound of a red-black tree, then x is not in
  -- the tree.

  @0 <→∉⁻ :
    Red-black pc n lb ub t → [ x ] <ᴱ lb → ¬ x ∈⁻ t
  <→∉⁻ t <lb ∈t =
    let lb< , _ = ∈⁻→<< t ∈t in
    EO.<-asymmetric <lb lb<

opaque

  -- If x is above an upper bound of a red-black tree, then x is not
  -- in the tree.

  @0 >→∉⁻ :
    Red-black pc n lb ub t → ub <ᴱ [ x ] → ¬ x ∈⁻ t
  >→∉⁻ t ub< ∈t =
    let _ , <ub = ∈⁻→<< t ∈t in
    EO.<-asymmetric <ub ub<

opaque

  -- If x < y, then x is in a red-black tree with y in the root if and
  -- only if x is in the left sub-tree.

  @0 <→∈⁻⇔∈⁻ :
    let t = node c l y r in
    Red-black pc n lb ub t →
    x < y →
    x ∈⁻ l ⇔ x ∈⁻ t
  <→∈⁻⇔∈⁻ (nodeʳᵇ _ r _ _) x<y = record
    { to   = inj₁
    ; from =
        P.[ id
          , P.[ (λ eq → ⊥-elim₀ (O.<→≢ x<y eq))
              , (λ ∈r → ⊥-elim₀ (<→∉⁻ r ([]-[] x<y) ∈r))
              ]
          ]
    }

opaque

  -- If x > y, then x is in a red-black tree with y in the root if and
  -- only if x is in the right sub-tree.

  @0 >→∈⁻⇔∈⁻ :
    let t = node c l y r in
    Red-black pc n lb ub t →
    x > y →
    x ∈⁻ r ⇔ x ∈⁻ t
  >→∈⁻⇔∈⁻ (nodeʳᵇ l _ _ _) x>y = record
    { to   = inj₂ ∘ inj₂
    ; from =
        P.[ (λ ∈l → ⊥-elim₀ (>→∉⁻ l ([]-[] x>y) ∈l))
          , P.[ (λ eq → ⊥-elim₀ (O.<→≢ x>y (sym eq)))
              , id
              ]
          ]
    }

opaque

  -- Tree membership is propositional for red-black trees.

  @0 ∈⁻-propositional :
    Red-black pc n lb ub t → Is-proposition (x ∈⁻ t)
  ∈⁻-propositional {t = leaf} _ =
    ⊥-propositional
  ∈⁻-propositional {t = node⁰} (nodeʳᵇ l r _ _) =
    ⊎-closure-propositional
      (λ x∈l →
         let _ , x<y = ∈⁻→<< l x∈l in
         P.[ (λ x≡y → EO.<→≢ x<y (cong [_] x≡y))
           , (λ x∈r → EO.<-asymmetric x<y (∈⁻→<< r x∈r .proj₁))
           ])
      (∈⁻-propositional l)
      (⊎-closure-propositional
         (λ x≡y x∈r → EO.<→≢ (∈⁻→<< r x∈r .proj₁) (cong [_] (sym x≡y)))
         O.is-set (∈⁻-propositional r))

------------------------------------------------------------------------
-- A membership test

opaque

  -- Does the element exist in the red-black tree?

  member?⁻ :
    (x : A) (t : Tree⁻) →
    @0 Red-black pc n lb ub t →
    Dec-Erased (x ∈⁻ t)
  member?⁻ _ leaf _ =
    no [ ⊥-elim ]
  member?⁻ x (node _ l y r) _ with O.compare x y
  … | eqᵀ x≡y = yes [ inj₂ (inj₁ x≡y) ]
  member?⁻ x (node _ l _ _) t@(nodeʳᵇ lʳᵇ _ _ _) | ltᵀ x<y =
    Dec-Erased-map (<→∈⁻⇔∈⁻ t x<y)
      (member?⁻ x l lʳᵇ)
  member?⁻ x (node _ _ _ r) t@(nodeʳᵇ _ rʳᵇ _ _) | gtᵀ x>y =
    Dec-Erased-map (>→∈⁻⇔∈⁻ t x>y)
      (member?⁻ x r rʳᵇ)

------------------------------------------------------------------------
-- An empty tree

opaque

  -- An empty tree.

  empty⁻ : Tree⁻
  empty⁻ = leaf

opaque
  unfolding empty⁻

  -- The empty tree is red-black.

  @0 empty⁻ʳᵇ : Red-black pc 0 min max empty⁻
  empty⁻ʳᵇ = leafʳᵇ min-max (refl _)

opaque
  unfolding empty⁻

  -- The empty tree is empty.

  @0 ∉⁻empty⁻ : ¬ x ∈⁻ empty⁻
  ∉⁻empty⁻ ()

------------------------------------------------------------------------
-- A cast lemma

opaque

  -- A cast lemma.

  @0 cast : m ≡ n → Red-black pc m lb ub t → Red-black pc n lb ub t
  cast = subst (λ n → Red-black _ n _ _ _)

------------------------------------------------------------------------
-- Insertion

opaque

  -- A balancing function.

  balanceˡ : Colour → Tree⁻ → A → Tree⁻ → Tree⁻
  balanceˡ black (node red (node red t₁ x₂ t₃) x₄ t₅) x₆ t₇ =
    node red (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  balanceˡ black (node red t₁ x₂ (node red t₃ x₄ t₅)) x₆ t₇ =
    node red (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  balanceˡ c l x r =
    node c l x r

opaque

  -- A balancing function.

  balanceʳ : Colour → Tree⁻ → A → Tree⁻ → Tree⁻
  balanceʳ black t₁ x₂ (node red (node red t₃ x₄ t₅) x₆ t₇) =
    node red (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  balanceʳ black t₁ x₂ (node red t₃ x₄ (node red t₅ x₆ t₇)) =
    node red (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  balanceʳ c l x r =
    node c l x r

opaque

  -- Inserts an element into the tree.

  insert⁻′ : A → Tree⁻ → Tree⁻
  insert⁻′ x leaf             = node red leaf x leaf
  insert⁻′ x t@(node c l y r) with O.compare x y
  … | eqᵀ _ = t
  … | ltᵀ _ = balanceˡ c (insert⁻′ x l) y r
  … | gtᵀ _ = balanceʳ c l y (insert⁻′ x r)

opaque

  -- If the tree is non-empty, then the root is coloured black.

  colour-root-black : Tree⁻ → Tree⁻
  colour-root-black leaf           = leaf
  colour-root-black (node _ l x r) = node black l x r

opaque

  -- Inserts an element into the tree.

  insert⁻ : A → Tree⁻ → Tree⁻
  insert⁻ x t = colour-root-black (insert⁻′ x t)

------------------------------------------------------------------------
-- Insertion produces red-black trees, given certain assumptions

-- A "fake" parent colour, used in the implementation of
-- Almost-red-black.

@0 fake-parent-colour : Colour → Colour → Colour
fake-parent-colour pc red   = pc
fake-parent-colour pc black = black

-- In an "almost red-black tree" the red invariant might be broken:
--
-- * If the parent colour is black and the tree has a red root, then
--   the root's children are allowed to be red.
--
-- * If the parent colour is red, then the tree is allowed to have a
--   red root.

@0 Almost-red-black :
  Colour → ℕ → (_ _ : Extended A) → Tree⁻ → Type (a ⊔ o)
Almost-red-black _  n lb ub leaf           = lb <ᴱ ub × n ≡ 0
Almost-red-black pc n lb ub (node c l x r) =
  ∃ λ m →
  Red-black (fake-parent-colour pc c) m lb [ x ] l ×
  Red-black (fake-parent-colour pc c) m [ x ] ub r ×
  Black-invariant c m n

pattern leafᵃʳᵇ lb<ub n≡0 = lb<ub , n≡0
pattern nodeᵃʳᵇ l r binv  = _ , l , r , binv

opaque

  -- Well-formed trees are still well-formed if the parent node is
  -- coloured black.

  @0 Red-black→Red-black-black :
    Red-black pc n lb ub t →
    Red-black black n lb ub t
  Red-black→Red-black-black {t = leaf} (leafʳᵇ lb<ub n≡0) =
    leafʳᵇ lb<ub n≡0
  Red-black→Red-black-black {t = node⁰} (nodeʳᵇ l r _ binv) =
    nodeʳᵇ l r black-parent binv

opaque

  -- A tree that is well-formed for a red parent is well-formed with a
  -- parent of any colour.

  @0 Red-black-red→Red-black :
    Red-black red n lb ub t →
    Red-black pc n lb ub t
  Red-black-red→Red-black {t = leaf} (leafʳᵇ lb<ub n≡0) =
    leafʳᵇ lb<ub n≡0
  Red-black-red→Red-black {t = node⁰} (nodeʳᵇ l r rinv binv) =
    nodeʳᵇ l r (red-parent rinv) binv

opaque

  -- Red-black trees are almost red-black.

  @0 Red-black→Almost-red-black :
    ∀ t → Red-black pc n lb ub t → Almost-red-black pc n lb ub t
  Red-black→Almost-red-black leaf (leafʳᵇ lb<ub n≡0) =
    leafᵃʳᵇ lb<ub n≡0
  Red-black→Almost-red-black (nodeᶜ black) (nodeʳᵇ l r _ binv) =
    nodeᵃʳᵇ l r binv
  Red-black→Almost-red-black (nodeᶜ red) (nodeʳᵇ l r _ binv) =
    nodeᵃʳᵇ (Red-black-red→Red-black l) (Red-black-red→Red-black r) binv

opaque

  -- An almost red-black tree with a red parent is a red-black tree
  -- with a black parent.

  @0 Almost-red-black-red→Red-black-black :
    Almost-red-black red n lb ub t → Red-black black n lb ub t
  Almost-red-black-red→Red-black-black {t = leaf} (leafᵃʳᵇ lb<ub n≡0) =
    leafʳᵇ lb<ub n≡0
  Almost-red-black-red→Red-black-black
    {t = nodeᶜ red} (nodeᵃʳᵇ l r binv) =
    nodeʳᵇ l r black-parent binv
  Almost-red-black-red→Red-black-black
    {t = nodeᶜ black} (nodeᵃʳᵇ l r binv) =
    nodeʳᵇ l r black-parent binv

opaque

  -- If the red invariant holds for pc and red, then a tree that is
  -- well-formed with a black parent is well-formed for pc.

  @0 Red-black-black→Red-black :
    Red-invariant pc red →
    Red-black black n lb ub t →
    Red-black pc n lb ub t
  Red-black-black→Red-black {t = leaf} rinv (leafʳᵇ lb<ub n≡0) =
    leafʳᵇ lb<ub n≡0
  Red-black-black→Red-black {t = node⁰} rinv (nodeʳᵇ l r _ binv) =
    nodeʳᵇ l r (red-child rinv) binv

opaque
  unfolding Black-invariant balanceˡ

  -- The function balanceˡ takes an almost red-black tree and a
  -- red-black tree to an almost red-black tree.

  @0 balanceˡʳᵇ :
    Almost-red-black c m lb [ x ] l →
    Red-black c m [ x ] ub r →
    Red-invariant pc c →
    Black-invariant c m n →
    Almost-red-black pc n lb ub (balanceˡ c l x r)
  balanceˡʳᵇ {c = red} l r rinv binv =
    nodeᵃʳᵇ
      (Red-black-black→Red-black rinv
         (Almost-red-black-red→Red-black-black l))
      (Red-black-red→Red-black r) binv
  balanceˡʳᵇ
    {c = black} {l = node red (nodeᶜ red) _ _}
    (nodeᵃʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) t₅ binv₂) t₇ rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁)
         (Red-black→Red-black-black t₃) rinv₃
         (cong suc (trans binv₂ binv₁)))
      (nodeʳᵇ t₅ (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡʳᵇ
    {c = black} {l = node red leaf _ (nodeᶜ red)}
    (nodeᵃʳᵇ t₁ (nodeʳᵇ t₃ t₅ _ binv₁) binv₂) t₇ rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (Red-black→Red-black-black (cast (sym binv₁) t₃)) rinv₃
         (cong suc binv₂))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡʳᵇ
    {c = black} {l = node red (nodeᶜ black) _ (nodeᶜ red)}
    (nodeᵃʳᵇ t₁ (nodeʳᵇ t₃ t₅ _ binv₁) binv₂) t₇ rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (Red-black→Red-black-black (cast (sym binv₁) t₃)) rinv₃
         (cong suc binv₂))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡʳᵇ {c = black} {l = leaf} (leafᵃʳᵇ lb< n≡0) t _ binv =
    nodeᵃʳᵇ (leafʳᵇ lb< n≡0) t binv
  balanceˡʳᵇ
    {c = black} {l = node red leaf _ leaf}
    (nodeᵃʳᵇ (leafʳᵇ lb< n≡0) (leafʳᵇ x₁<x₂ _) binv₁) t₃ _ binv₂ =
    nodeᵃʳᵇ
      (nodeʳᵇ (leafʳᵇ lb< n≡0) (leafʳᵇ x₁<x₂ n≡0) black-parent binv₁) t₃
      binv₂
  balanceˡʳᵇ
    {c = black} {l = node red leaf _ (nodeᶜ black)}
    (nodeᵃʳᵇ (leafʳᵇ lb< n≡0) (nodeʳᵇ t₂ t₄ _ binv₁) binv₂) t₆ _ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (leafʳᵇ lb< n≡0) (nodeʳᵇ t₂ t₄ black-child binv₁)
         black-parent binv₂)
      t₆ binv₃
  balanceˡʳᵇ
    {c = black} {l = node red (nodeᶜ black) _ leaf}
    (nodeᵃʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) (leafʳᵇ x₄<x₅ n≡0) binv₂) t₆ _
    binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (nodeʳᵇ t₁ t₃ black-child binv₁) (leafʳᵇ x₄<x₅ n≡0)
         black-parent binv₂)
      t₆ binv₃
  balanceˡʳᵇ
    {c = black} {l = node red (nodeᶜ black) _ (nodeᶜ black)}
    (nodeᵃʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) (nodeʳᵇ t₅ t₇ _ binv₂) binv₃) t₉ _
    binv₄ =
    nodeᵃʳᵇ
      (nodeʳᵇ (nodeʳᵇ t₁ t₃ black-child binv₁)
         (nodeʳᵇ t₅ t₇ black-child binv₂) black-parent binv₃)
      t₉ binv₄
  balanceˡʳᵇ
    {c = black} {l = nodeᶜ black} (nodeᵃʳᵇ t₁ t₃ binv₁) t₅ _ binv₂ =
    nodeᵃʳᵇ (nodeʳᵇ t₁ t₃ black-parent binv₁) t₅ binv₂

opaque
  unfolding Black-invariant balanceʳ

  -- The function balanceˡ takes a red-black tree and an almost
  -- red-black tree to an almost red-black tree.

  @0 balanceʳʳᵇ :
    Red-black c m lb [ x ] l →
    Almost-red-black c m [ x ] ub r →
    Red-invariant pc c →
    Black-invariant c m n →
    Almost-red-black pc n lb ub (balanceʳ c l x r)
  balanceʳʳᵇ {c = red} l r rinv binv =
    nodeᵃʳᵇ (Red-black-red→Red-black l)
      (Red-black-black→Red-black rinv
         (Almost-red-black-red→Red-black-black r))
      binv
  balanceʳʳᵇ
    {c = black} {r = node red (nodeᶜ red) _ _}
    t₁ (nodeᵃʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) t₇ binv₂) rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁)
         (Red-black→Red-black-black (cast (sym (trans binv₂ binv₁)) t₃))
         rinv₃ (refl _))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅)) t₇ rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red leaf _ (nodeᶜ red)}
    t₁ (nodeᵃʳᵇ t₃ (nodeʳᵇ t₅ t₇ _ binv₁) binv₂) rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (cast {pc = black} {t = leaf} (sym binv₂) t₃) rinv₃
         (refl _))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (Red-black→Red-black-black (cast (sym binv₁) t₇)) rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red (nodeᶜ black) _ (nodeᶜ red)}
    t₁ (nodeᵃʳᵇ t₃ (nodeʳᵇ t₅ t₇ _ binv₁) binv₂) rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (cast {t = node⁰} (sym binv₂) t₃) rinv₃ (refl _))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (Red-black→Red-black-black (cast (sym binv₁) t₇)) rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳʳᵇ {c = black} {r = leaf} t (leafʳᵇ lb< n≡0) _ binv =
    nodeᵃʳᵇ t (leafʳᵇ lb< n≡0) binv
  balanceʳʳᵇ
    {c = black} {r = node red leaf _ leaf}
    t₁ (nodeᵃʳᵇ (leafʳᵇ x₂<x₃ n≡0) (leafʳᵇ <ub _) binv₁) _ binv₂ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (leafʳᵇ x₂<x₃ n≡0) (leafʳᵇ <ub n≡0) black-parent binv₁)
      binv₂
  balanceʳʳᵇ
    {c = black} {r = node red leaf _ (nodeᶜ black)}
    t₁ (nodeᵃʳᵇ (leafʳᵇ x₂<x₃ n≡0) (nodeʳᵇ t₄ t₆ _ binv₁) binv₂) _
    binv₃ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (leafʳᵇ x₂<x₃ n≡0) (nodeʳᵇ t₄ t₆ black-child binv₁)
         black-parent binv₂)
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red (nodeᶜ black) _ leaf}
    t₁ (nodeᵃʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) (leafʳᵇ <ub n≡0) binv₂) _ binv₃ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (nodeʳᵇ t₃ t₅ black-child binv₁) (leafʳᵇ <ub n≡0)
         black-parent binv₂)
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red (nodeᶜ black) _ (nodeᶜ black)}
    t₁ (nodeᵃʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) (nodeʳᵇ t₇ t₉ _ binv₂) binv₃) _
    binv₄ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (nodeʳᵇ t₃ t₅ black-child binv₁)
         (nodeʳᵇ t₇ t₉ black-child binv₂) black-parent binv₃)
      binv₄
  balanceʳʳᵇ
    {c = black} {r = nodeᶜ black} t₁ (nodeᵃʳᵇ t₃ t₅ binv₁) _ binv₂ =
    nodeᵃʳᵇ t₁ (nodeʳᵇ t₃ t₅ black-parent binv₁) binv₂

opaque
  unfolding Black-invariant insert⁻′

  -- The function insert⁻′ takes red-black trees to almost red-black
  -- trees, given certain assumptions.

  @0 insert⁻′ʳᵇ :
    Red-black pc n lb ub t →
    lb <ᴱ [ x ] → [ x ] <ᴱ ub →
    Almost-red-black pc n lb ub (insert⁻′ x t)
  insert⁻′ʳᵇ {t = leaf} (leafʳᵇ _ n≡0) lb< <ub =
    nodeᵃʳᵇ (leafʳᵇ lb< (refl _)) (leafʳᵇ <ub (refl _)) n≡0
  insert⁻′ʳᵇ
    {t = t@(node _ _ y _)} {x} tʳᵇ@(nodeʳᵇ l r rinv binv) lb< <ub
    with O.compare x y
  … | eqᵀ _   = Red-black→Almost-red-black t tʳᵇ
  … | ltᵀ x<y = balanceˡʳᵇ (insert⁻′ʳᵇ l lb< ([]-[] x<y)) r rinv binv
  … | gtᵀ x>y = balanceʳʳᵇ l (insert⁻′ʳᵇ r ([]-[] x>y) <ub) rinv binv

opaque
  unfolding colour-root-black

  -- The function colour-root-black takes almost red-black trees to
  -- red-black trees.

  @0 colour-root-blackʳᵇ :
    Almost-red-black pc n lb ub t →
    ∃ λ n → Red-black pc n lb ub (colour-root-black t)
  colour-root-blackʳᵇ {t = leaf} (leafᵃʳᵇ lb<ub n≡0) =
    _ , leafʳᵇ lb<ub n≡0
  colour-root-blackʳᵇ {t = node _ _ _ _} (nodeᵃʳᵇ lʳᵇ rʳᵇ binv) =
    _ ,
    nodeʳᵇ (Red-black→Red-black-black lʳᵇ)
      (Red-black→Red-black-black rʳᵇ) black-child
      (black-black binv .proj₂)

opaque
  unfolding insert⁻

  -- The function insert⁻ takes red-black trees to red-black trees,
  -- given certain assumptions.

  @0 insert⁻ʳᵇ :
    Red-black pc n lb ub t →
    lb <ᴱ [ x ] → [ x ] <ᴱ ub →
    ∃ λ (n : ℕ) → Red-black pc n lb ub (insert⁻ x t)
  insert⁻ʳᵇ t lb< <ub =
    colour-root-blackʳᵇ (insert⁻′ʳᵇ t lb< <ub)

------------------------------------------------------------------------
-- Membership lemmas for insertion

opaque
  unfolding balanceˡ

  -- A membership lemma for balanceˡ.

  @0 ∈⁻-balanceˡ :
    x ∈⁻ balanceˡ c l y r ⇔
    x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r
  ∈⁻-balanceˡ {c = red} =
    F.id
  ∈⁻-balanceˡ
    {x} {c = black}
    {l = node red (node red t₁ x₂ t₃) x₄ t₅} {y = x₆} {r = t₇} =
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇    ↝⟨ record
                                                                               { to   = P.[ inj₁ ∘ inj₁
                                                                                          , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                              , P.[ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ]
                                                                                              ]
                                                                                          ]
                                                                               ; from = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ] ]
                                                                                          , inj₂ ∘ inj₂ ∘ inj₂
                                                                                          ]
                                                                               } ⟩□
    ((x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  □
  ∈⁻-balanceˡ
    {x} {c = black}
    {l = node red t₁@(nodeᶜ black) x₂ (node red t₃ x₄ t₅)} {y = x₆}
    {r = t₇} =
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  ↝⟨ record
                                                                             { to   = P.[ P.[ inj₁ ∘ inj₁
                                                                                            , P.[ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                            ]
                                                                                        , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
                                                                                            , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ , inj₂ ]
                                                                                            ]
                                                                                        ]
                                                                             ; from = P.[ P.[ inj₁ ∘ inj₁
                                                                                            , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                                , P.[ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                    , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                                    ]
                                                                                                ]
                                                                                            ]
                                                                                        , inj₂ ∘ inj₂ ∘ inj₂
                                                                                        ]
                                                                             } ⟩□
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  □
  ∈⁻-balanceˡ
    {x} {c = black}
    {l = node red t₁@leaf x₂ (node red t₃ x₄ t₅)} {y = x₆} {r = t₇} =
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  ↝⟨ record
                                                                             { to   = P.[ P.[ inj₁ ∘ inj₁
                                                                                            , P.[ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                            ]
                                                                                        , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
                                                                                            , P.[ inj₁ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ , inj₂ ]
                                                                                            ]
                                                                                        ]
                                                                             ; from = P.[ P.[ inj₁ ∘ inj₁
                                                                                            , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                                , P.[ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                    , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                                    ]
                                                                                                ]
                                                                                            ]
                                                                                        , inj₂ ∘ inj₂ ∘ inj₂
                                                                                        ]
                                                                             } ⟩□
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  □
  ∈⁻-balanceˡ {c = black} {l = leaf} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red leaf _ leaf} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red leaf _ (nodeᶜ black)} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red (nodeᶜ black) _ leaf} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red (nodeᶜ black) _ (nodeᶜ black)} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = nodeᶜ black} =
    F.id

opaque
  unfolding balanceʳ

  -- A membership lemma for balanceʳ.

  @0 ∈⁻-balanceʳ :
    x ∈⁻ balanceʳ c l y r ⇔
    x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r
  ∈⁻-balanceʳ {c = red} =
    F.id
  ∈⁻-balanceʳ
    {x} {c = black} {l = t₁} {y = x₂}
    {r = node red (node red t₃ x₄ t₅) x₆ t₇} =
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  ↝⟨ record
                                                                             { to   = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ∘ inj₁ ] ]
                                                                                        , P.[ inj₂ ∘ inj₂ ∘ inj₁ ∘ inj₂ ∘ inj₁
                                                                                            , P.[ inj₂ ∘ inj₂ ∘ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                , inj₂ ∘ inj₂ ∘ inj₂
                                                                                                ]
                                                                                            ]
                                                                                        ]
                                                                             ; from = P.[ inj₁ ∘ inj₁
                                                                                        , P.[ inj₁ ∘ inj₂ ∘ inj₁
                                                                                            , P.[ P.[ inj₁ ∘ inj₂ ∘ inj₂
                                                                                                    , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ]
                                                                                                    ]
                                                                                                , inj₂ ∘ inj₂ ∘ inj₂
                                                                                                ]
                                                                                            ]
                                                                                        ]
                                                                             } ⟩□
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ (x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  □
  ∈⁻-balanceʳ
    {x} {c = black} {l = t₁} {y = x₂}
    {r = node red t₃@(nodeᶜ black) x₄ (node red t₅ x₆ t₇)} =
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  ↝⟨ record
                                                                             { to   = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ] ]
                                                                                        , inj₂ ∘ inj₂ ∘ inj₂
                                                                                        ]
                                                                             ; from = P.[ inj₁ ∘ inj₁
                                                                                        , P.[ inj₁ ∘ inj₂ ∘ inj₁ , P.[ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ] ]
                                                                                        ]
                                                                             } ⟩□
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇    □
  ∈⁻-balanceʳ
    {x} {c = black} {l = t₁} {y = x₂}
    {r = node red t₃@leaf x₄ (node red t₅ x₆ t₇)} =
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  ↝⟨ record
                                                                             { to   = P.[ P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₁ ] ]
                                                                                        , inj₂ ∘ inj₂ ∘ inj₂
                                                                                        ]
                                                                             ; from = P.[ inj₁ ∘ inj₁
                                                                                        , P.[ inj₁ ∘ inj₂ ∘ inj₁ , P.[ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ] ]
                                                                                        ]
                                                                             } ⟩□
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇    □
  ∈⁻-balanceʳ {c = black} {r = leaf} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red leaf _ leaf} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red leaf _ (nodeᶜ black)} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red (nodeᶜ black) _ leaf} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red (nodeᶜ black) _ (nodeᶜ black)} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = nodeᶜ black} =
    F.id

opaque
  unfolding insert⁻′

  -- The value y is in insert⁻′ x t if and only if y is x or y is in t.

  @0 ∈⁻-insert⁻′ :
    y ∈⁻ insert⁻′ x t ⇔ y ≡ x ⊎ y ∈⁻ t
  ∈⁻-insert⁻′ {y} {x} {t = leaf} =
    ⊥ ⊎ y ≡ x ⊎ ⊥  ↔⟨ ⊎-left-identity ⟩□
    y ≡ x ⊎ ⊥      □
  ∈⁻-insert⁻′ {y} {x} {t = node c l z r}
    with O.compare x z
  … | eqᵀ x≡z =
    y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r          ↝⟨ record
                                          { to   = inj₂
                                          ; from = P.[ inj₂ ∘ inj₁ ∘ flip trans x≡z , id ]
                                          } ⟩□
    y ≡ x ⊎ y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r  □
  … | ltᵀ _ =
    y ∈⁻ balanceˡ c (insert⁻′ x l) z r  ↝⟨ ∈⁻-balanceˡ ⟩
    y ∈⁻ insert⁻′ x l ⊎ y ≡ z ⊎ y ∈⁻ r  ↝⟨ ∈⁻-insert⁻′ ⊎-cong F.id ⟩
    (y ≡ x ⊎ y ∈⁻ l) ⊎ y ≡ z ⊎ y ∈⁻ r   ↔⟨ inverse ⊎-assoc ⟩□
    y ≡ x ⊎ y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r     □
  … | gtᵀ _ =
    y ∈⁻ balanceʳ c l z (insert⁻′ x r)  ↝⟨ ∈⁻-balanceʳ ⟩
    y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ insert⁻′ x r  ↝⟨ F.id ⊎-cong F.id ⊎-cong ∈⁻-insert⁻′ ⟩
    y ∈⁻ l ⊎ y ≡ z ⊎ y ≡ x ⊎ y ∈⁻ r     ↝⟨ record
                                             { to   = P.[ inj₂ ∘ inj₁ , P.[ inj₂ ∘ inj₂ ∘ inj₁ , P.[ inj₁ , inj₂ ∘ inj₂ ∘ inj₂ ] ] ]
                                             ; from = P.[ inj₂ ∘ inj₂ ∘ inj₁ , P.[ inj₁ , P.[ inj₂ ∘ inj₁ , inj₂ ∘ inj₂ ∘ inj₂ ] ] ]
                                             } ⟩□
    y ≡ x ⊎ y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r     □

opaque
  unfolding colour-root-black

  -- A membership lemma for colour-root-black.

  @0 ∈⁻-colour-root-black :
    x ∈⁻ colour-root-black t ⇔ x ∈⁻ t
  ∈⁻-colour-root-black {t = leaf}  = F.id
  ∈⁻-colour-root-black {t = node⁰} = F.id

opaque
  unfolding insert⁻

  -- The value y is in insert⁻ x t if and only if y is x or y is in t.

  @0 ∈⁻-insert⁻ :
    y ∈⁻ insert⁻ x t ⇔ y ≡ x ⊎ y ∈⁻ t
  ∈⁻-insert⁻ {y} {x} {t} =
    y ∈⁻ colour-root-black (insert⁻′ x t)  ↝⟨ ∈⁻-colour-root-black ⟩
    y ∈⁻ insert⁻′ x t                      ↝⟨ ∈⁻-insert⁻′ ⟩□
    y ≡ x ⊎ y ∈⁻ t                         □

------------------------------------------------------------------------
-- Finding the minimum element

opaque

  -- Finds the minimum element. The tree must be non-empty.

  find-min⁻ : (t : Tree⁻) → @0 t ≢ leaf → A
  find-min⁻ (node _ l@node⁰ y _) _   = find-min⁻ l node≢leaf
  find-min⁻ (node _ leaf y _)    _   = y
  find-min⁻ leaf                 hyp = ⊥-elim₀ (hyp (refl _))

opaque
  unfolding find-min⁻

  -- A membership lemma for find-min⁻.

  @0 find-min⁻-∈⁻ :
    {t≢leaf : t ≢ leaf} →
    find-min⁻ t t≢leaf ∈⁻ t
  find-min⁻-∈⁻ {t = leaf} {t≢leaf} =
    ⊥-elim (t≢leaf (refl _))
  find-min⁻-∈⁻ {t = node _ leaf _ _} =
    inj₂ (inj₁ (refl _))
  find-min⁻-∈⁻ {t = node _ node⁰ _ _} =
    inj₁ find-min⁻-∈⁻

opaque
  unfolding find-min⁻

  -- An ordering lemma for find-min⁻.

  @0 find-min⁻-≤ :
    (t≢leaf : t ≢ leaf) →
    Red-black pc n lb ub t →
    x ∈⁻ t → find-min⁻ t t≢leaf ≤ x
  find-min⁻-≤ {t = leaf} t≢leaf =
    ⊥-elim (t≢leaf (refl _))
  find-min⁻-≤ {t = node _ leaf _ _} _ _ (inj₂ (inj₁ x≡)) =
    O.≤-reflexive (sym x≡)
  find-min⁻-≤
    {t = node _ leaf _ _} _ (nodeʳᵇ _ r _ _) (inj₂ (inj₂ x∈r))
    with ∈⁻→<< r x∈r
  … | []-[] <x , _ =
    O.<→≤ <x
  find-min⁻-≤ {t = node _ node⁰ _ _} _ (nodeʳᵇ l _ _ _) (inj₁ x∈l) =
    find-min⁻-≤ node≢leaf l x∈l
  find-min⁻-≤ {t = node _ l@node⁰ _ _} _ (nodeʳᵇ lʳᵇ r _ _) (inj₂ x∈)
    with
      EO.<-≤-trans (∈⁻→<< lʳᵇ (find-min⁻-∈⁻ {t = l}) .proj₂)
        (case x∈ of λ where
           (inj₁ x≡)  → EO.≤-reflexive (cong [_] (sym x≡))
           (inj₂ x∈r) → EO.<→≤ (∈⁻→<< r x∈r .proj₁))
  … | []-[] <x = O.<→≤ <x

------------------------------------------------------------------------
-- Balancing functions used by deletion

opaque

  -- A balancing function.
  --
  -- The cases marked with X were, as far as I could tell, missing
  -- from Wikpedia's list of "delete cases". Perhaps I misunderstood
  -- something.

  del-balanceˡ′ : Colour → Tree⁻ → A → Tree⁻ → A → Tree⁻ → Bool × Tree⁻
  del-balanceˡ′ c t₁ x₂ t₃ x₄ (node red t₅ x₆ t₇) =
    false , node c (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  del-balanceˡ′ c t₁ x₂ (node red t₃ x₄ t₅) x₆ t₇@(nodeᶜ black) =
    false , node c (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  del-balanceˡ′ c t₁ x₂ t₃@(nodeᶜ black) x₄ t₅@(nodeᶜ black) =
    is-black c , node black t₁ x₂ (node red t₃ x₄ t₅)
  del-balanceˡ′ c t₁ x₂ (node _ t₃ x₄ t₅) x₆ leaf = -- X.
    false , node black (node c t₁ x₂ t₃) x₄ (node c t₅ x₆ leaf)
  del-balanceˡ′ c t₁ x₂ leaf x₃ leaf = -- X.
    is-black c , node black t₁ x₂ (node red leaf x₃ leaf)
  del-balanceˡ′ c t₁ x₂ t₃@leaf x₄ t₅@(nodeᶜ black) =
    false , node c t₁ x₂ (node black t₃ x₄ t₅)

opaque

  -- A balancing function.

  del-balanceʳ′ : Colour → Tree⁻ → A → Tree⁻ → A → Tree⁻ → Bool × Tree⁻
  del-balanceʳ′ c (node red t₁ x₂ t₃) x₄ t₅ x₆ t₇ =
    false , node c (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  del-balanceʳ′ c t₁@(nodeᶜ black) x₂ (node red t₃ x₄ t₅) x₆ t₇ =
    false , node c (node black t₁ x₂ t₃) x₄ (node black t₅ x₆ t₇)
  del-balanceʳ′ c t₁@(nodeᶜ black) x₂ t₃@(nodeᶜ black) x₄ t₅ =
    is-black c , node black (node red t₁ x₂ t₃) x₄ t₅
  del-balanceʳ′ c leaf x₁ (node _ t₂ x₃ t₄) x₅ t₆ =
    false , node black (node c leaf x₁ t₂) x₃ (node c t₄ x₅ t₆)
  del-balanceʳ′ c leaf x₁ leaf x₂ t₃ =
    is-black c , node black (node red leaf x₁ leaf) x₂ t₃
  del-balanceʳ′ c t₁@(nodeᶜ black) x₂ t₃@leaf x₄ t₅ =
    false , node c (node black t₁ x₂ t₃) x₄ t₅

opaque

  -- A balancing function.

  del-balanceˡ : Colour → Bool × Tree⁻ → A → Tree⁻ → Bool × Tree⁻
  del-balanceˡ c (false , t₁) x₂ t₃ =
    false , node c t₁ x₂ t₃
  del-balanceˡ c (true , t₁) x₂ (node black t₃ x₄ t₅) =
    del-balanceˡ′ c t₁ x₂ t₃ x₄ t₅
  del-balanceˡ c (true , t₁) x₂ (node red (node black t₃ x₄ t₅) x₆ t₇) =
    false , node c (del-balanceˡ′ red t₁ x₂ t₃ x₄ t₅ .proj₂) x₆ t₇
  del-balanceˡ c (_ , t₁) x₂ t₃ =
    false , node c t₁ x₂ t₃

opaque

  -- A balancing function.

  del-balanceʳ : Colour → Tree⁻ → A → Bool × Tree⁻ → Bool × Tree⁻
  del-balanceʳ c t₁ x₂ (false , t₃) =
    false , node c t₁ x₂ t₃
  del-balanceʳ c (node black t₁ x₂ t₃) x₄ (true , t₅) =
    del-balanceʳ′ c t₁ x₂ t₃ x₄ t₅
  del-balanceʳ c (node red t₁ x₂ (node black t₃ x₄ t₅)) x₆ (true , t₇) =
    false , node c t₁ x₂ (del-balanceʳ′ red t₃ x₄ t₅ x₆ t₇ .proj₂)
  del-balanceʳ c t₁ x₂ (_ , t₃) =
    false , node c t₁ x₂ t₃

------------------------------------------------------------------------
-- The balancing functions used by deletion produce red-black trees,
-- given certain assumptions

opaque
  unfolding del-balanceˡ′ is-black

  -- The function del-balanceˡ′ red returns false.

  @0 del-balanceˡ′-red≡false :
    ∀ t₃ t₅ →
    del-balanceˡ′ red t₁ x₂ t₃ x₄ t₅ .proj₁ ≡ false
  del-balanceˡ′-red≡false _             (nodeᶜ red)   = refl _
  del-balanceˡ′-red≡false (nodeᶜ red)   (nodeᶜ black) = refl _
  del-balanceˡ′-red≡false node⁰         leaf          = refl _
  del-balanceˡ′-red≡false (nodeᶜ black) (nodeᶜ black) = refl _
  del-balanceˡ′-red≡false leaf          leaf          = refl _
  del-balanceˡ′-red≡false leaf          (nodeᶜ black) = refl _

opaque
  unfolding del-balanceʳ′ is-black

  -- The function del-balanceʳ′ red returns false.

  @0 del-balanceʳ′-red≡false :
    ∀ t₁ t₃ →
    del-balanceʳ′ red t₁ x₂ t₃ x₄ t₅ .proj₁ ≡ false
  del-balanceʳ′-red≡false (nodeᶜ red)   _             = refl _
  del-balanceʳ′-red≡false (nodeᶜ black) (nodeᶜ red)   = refl _
  del-balanceʳ′-red≡false leaf          node⁰         = refl _
  del-balanceʳ′-red≡false (nodeᶜ black) (nodeᶜ black) = refl _
  del-balanceʳ′-red≡false leaf          leaf          = refl _
  del-balanceʳ′-red≡false (nodeᶜ black) leaf          = refl _

opaque
  unfolding del-balanceˡ

  -- If del-balanceˡ returns true, then the input boolean was true.

  @0 del-balanceˡ≡true→ :
    ∀ b → del-balanceˡ c (b , t₁) x₂ t₃ .proj₁ ≡ true → b ≡ true
  del-balanceˡ≡true→ true  _   = refl _
  del-balanceˡ≡true→ false hyp = ⊥-elim (Bool.true≢false (sym hyp))

opaque
  unfolding del-balanceʳ

  -- If del-balanceʳ returns true, then the input boolean was true.

  @0 del-balanceʳ≡true→ :
    ∀ b → del-balanceʳ c t₁ x₂ (b , t₃) .proj₁ ≡ true → b ≡ true
  del-balanceʳ≡true→ true  _   = refl _
  del-balanceʳ≡true→ false hyp = ⊥-elim (Bool.true≢false (sym hyp))

opaque
  unfolding Black-invariant del-balanceˡ′ is-black

  -- The function del-balanceˡ′ produces red-black trees, given
  -- certain assumptions.

  @0 del-balanceˡ′ʳᵇ :
    ∀ c t₃ t₅ →
    let b , t = del-balanceˡ′ c t₁ x₂ t₃ x₄ t₅ in
    Red-black red n lb [ x₂ ] t₁ →
    Red-black c (suc n) [ x₂ ] ub (node black t₃ x₄ t₅) →
    Red-invariant pc c →
    Black-invariant c (if b then n else suc n) m →
    Red-black (if b then red else pc) m lb ub t
  del-balanceˡ′ʳᵇ
    _ _ (nodeᶜ red) t₁ (nodeʳᵇ t₃ (nodeʳᵇ t₅ t₇ _ binv₁) _ binv₂) rinv
    binv =
    nodeʳᵇ
      (nodeʳᵇ (cast (N.cancel-suc binv₂) (Red-black→Red-black-black t₁))
         t₃ black-child binv₂)
      (nodeʳᵇ (Red-black→Red-black-black t₅)
         (Red-black→Red-black-black t₇) black-child
         (trans binv₂ (cong suc binv₁)))
      rinv binv
  del-balanceˡ′ʳᵇ
    _ (nodeᶜ red) (nodeᶜ black) t₁
    (nodeʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) t₇ _ binv₂) rinv binv =
    nodeʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁)
         (cast (sym (trans (N.cancel-suc binv₂) binv₁))
            (Red-black→Red-black-black t₃))
         black-child (refl _))
      (nodeʳᵇ (cast (sym binv₁) (Red-black→Red-black-black t₅)) t₇
         black-child binv₂)
      rinv binv
  del-balanceˡ′ʳᵇ
    red (nodeᶜ black) (nodeᶜ black) t₁
    (nodeʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) (nodeʳᵇ t₇ t₉ _ binv₂) _ binv₃) _
    binv =
    nodeʳᵇ (Red-black→Red-black-black t₁)
      (nodeʳᵇ (nodeʳᵇ t₃ t₅ black-child binv₁)
         (nodeʳᵇ t₇ t₉ black-child binv₂) black-parent
         (N.cancel-suc binv₃))
      black-child binv
  del-balanceˡ′ʳᵇ
    black (nodeᶜ black) (nodeᶜ black) t₁
    (nodeʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) (nodeʳᵇ t₇ t₉ _ binv₂) _ binv₃) _
    binv =
    nodeʳᵇ (Red-black→Red-black-black t₁)
      (nodeʳᵇ (nodeʳᵇ t₃ t₅ black-child binv₁)
         (nodeʳᵇ t₇ t₉ black-child binv₂) black-parent
         (N.cancel-suc binv₃))
      black-child binv
  del-balanceˡ′ʳᵇ
    red (node _ leaf _ leaf) leaf t₁
    (nodeʳᵇ (nodeʳᵇ (x₂<x₄ , _) (x₄<x₆ , _) _ _) t₇ _ binv₂) _ binv =
    let ≡0 = trans (N.cancel-suc binv₂) (t₇ .proj₂) in
    nodeʳᵇ (nodeʳᵇ t₁ (x₂<x₄ , ≡0) black-parent (refl _))
      (nodeʳᵇ (x₄<x₆ , t₇ .proj₂) t₇ black-parent (N.cancel-suc binv₂))
      black-child binv
  del-balanceˡ′ʳᵇ
    black (node _ leaf _ leaf) leaf t₁
    (nodeʳᵇ (nodeʳᵇ (x₂<x₄ , _) (x₄<x₆ , _) _ _) t₇ _ binv₂) _ binv =
    let ≡0 = trans (N.cancel-suc binv₂) (t₇ .proj₂) in
    nodeʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁) (x₂<x₄ , ≡0) black-parent
         (refl _))
      (nodeʳᵇ (x₄<x₆ , t₇ .proj₂) t₇ black-parent binv₂)
      black-child binv
  del-balanceˡ′ʳᵇ red leaf leaf t₁ (nodeʳᵇ t₃ t₅ _ binv₁) _ binv =
    nodeʳᵇ (Red-black→Red-black-black t₁)
      (nodeʳᵇ t₃ t₅ black-parent (N.cancel-suc binv₁)) black-child binv
  del-balanceˡ′ʳᵇ black leaf leaf t₁ (nodeʳᵇ t₃ t₅ _ binv₁) _ binv =
    nodeʳᵇ (Red-black→Red-black-black t₁)
      (nodeʳᵇ t₃ t₅ black-parent (N.cancel-suc binv₁)) black-child binv
  del-balanceˡ′ʳᵇ
    _ leaf (nodeᶜ black) _ (nodeʳᵇ (_ , ≡0) (nodeʳᵇ _ _ _ ≡+) _ _) _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  del-balanceˡ′ʳᵇ
    _ (nodeᶜ black) leaf _ (nodeʳᵇ (nodeʳᵇ _ _ _ ≡+) (_ , ≡0) _ _) _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  del-balanceˡ′ʳᵇ
    _ (node red (nodeᶜ red) _ _) leaf _
    (nodeʳᵇ (nodeʳᵇ (nodeʳᵇ _ _ rinv _) _ _ _) _ _ _) _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceˡ′ʳᵇ
    _ (node red (nodeᶜ black) _ _) leaf _
    (nodeʳᵇ (nodeʳᵇ (nodeʳᵇ _ _ _ ≡+) _ _ binv) (_ , ≡0) _ _) _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) (trans binv ≡+)))
  del-balanceˡ′ʳᵇ
    _ (node red _ _ (nodeᶜ red)) leaf _
    (nodeʳᵇ (nodeʳᵇ _ (nodeʳᵇ _ _ rinv _) _ _) _ _ _) _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceˡ′ʳᵇ
    _ (node red _ _ (nodeᶜ black)) leaf _
    (nodeʳᵇ (nodeʳᵇ _ (nodeʳᵇ _ _ _ ≡+) _ binv) (_ , ≡0) _ _) _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) (trans binv ≡+)))

opaque
  unfolding Black-invariant del-balanceʳ′ is-black

  -- The function del-balanceʳ′ produces red-black trees, given
  -- certain assumptions.

  @0 del-balanceʳ′ʳᵇ :
    ∀ c t₁ t₃ →
    let b , t = del-balanceʳ′ c t₁ x₂ t₃ x₄ t₅ in
    Red-black c (suc n) lb [ x₄ ] (node black t₁ x₂ t₃) →
    Red-black red n [ x₄ ] ub t₅ →
    Red-invariant pc c →
    Black-invariant c (if b then n else suc n) m →
    Red-black (if b then red else pc) m lb ub t
  del-balanceʳ′ʳᵇ
    _ (nodeᶜ red) _ (nodeʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) t₅ _ binv₂) t₇ rinv
    binv =
    nodeʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁)
         (Red-black→Red-black-black t₃) black-child
         (trans binv₂ (cong suc binv₁)))
      (nodeʳᵇ t₅
         (cast (N.cancel-suc binv₂) (Red-black→Red-black-black t₇))
         black-child binv₂)
      rinv binv
  del-balanceʳ′ʳᵇ
    _ (nodeᶜ black) (nodeᶜ red)
    (nodeʳᵇ t₁ (nodeʳᵇ t₃ t₅ _ binv₁) _ binv₂) t₇ rinv binv =
    nodeʳᵇ
      (nodeʳᵇ t₁ (cast (sym binv₁) (Red-black→Red-black-black t₃))
         black-child binv₂)
      (nodeʳᵇ
         (cast (sym (trans (N.cancel-suc binv₂) binv₁))
            (Red-black→Red-black-black t₅))
         (Red-black→Red-black-black t₇)
         black-child (refl _))
      rinv binv
  del-balanceʳ′ʳᵇ
    red (nodeᶜ black) (nodeᶜ black)
    (nodeʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) (nodeʳᵇ t₅ t₇ _ binv₂) _ binv₃) t₉ _
    binv =
    nodeʳᵇ
      (nodeʳᵇ (nodeʳᵇ t₁ t₃ black-child binv₁)
         (nodeʳᵇ t₅ t₇ black-child binv₂) black-parent
         (N.cancel-suc binv₃))
      (Red-black→Red-black-black t₉) black-child binv
  del-balanceʳ′ʳᵇ
    black (nodeᶜ black) (nodeᶜ black)
    (nodeʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) (nodeʳᵇ t₅ t₇ _ binv₂) _ binv₃) t₉ _
    binv =
    nodeʳᵇ
      (nodeʳᵇ (nodeʳᵇ t₁ t₃ black-child binv₁)
         (nodeʳᵇ t₅ t₇ black-child binv₂) black-parent
         (N.cancel-suc binv₃))
      (Red-black→Red-black-black t₉) black-child binv
  del-balanceʳ′ʳᵇ
    red leaf (node _ leaf _ leaf)
    (nodeʳᵇ t₁ (nodeʳᵇ (x₂<x₄ , _) (x₄<x₆ , _) _ _) _ binv₂) t₇ _ binv =
    let ≡0 = trans (N.cancel-suc binv₂) (t₁ .proj₂) in
    nodeʳᵇ
      (nodeʳᵇ t₁ (x₂<x₄ , t₁ .proj₂) black-parent (N.cancel-suc binv₂))
      (nodeʳᵇ (x₄<x₆ , ≡0) t₇ black-parent (refl _)) black-child binv
  del-balanceʳ′ʳᵇ
    black leaf (node _ leaf _ leaf)
    (nodeʳᵇ t₁ (nodeʳᵇ (x₂<x₄ , _) (x₄<x₆ , _) _ _) _ binv₂) t₇ _ binv =
    let ≡0 = trans (N.cancel-suc binv₂) (t₁ .proj₂) in
    nodeʳᵇ (nodeʳᵇ t₁ (x₂<x₄ , t₁ .proj₂) black-parent binv₂)
      (nodeʳᵇ (x₄<x₆ , ≡0) (Red-black→Red-black-black t₇) black-parent
         (refl _))
      black-child binv
  del-balanceʳ′ʳᵇ red leaf leaf (nodeʳᵇ t₁ t₃ _ binv₁) t₅ _ binv =
    nodeʳᵇ (nodeʳᵇ t₁ t₃ black-parent (N.cancel-suc binv₁))
       (Red-black→Red-black-black t₅) black-child binv
  del-balanceʳ′ʳᵇ black leaf leaf (nodeʳᵇ t₁ t₃ _ binv₁) t₅ _ binv =
    nodeʳᵇ (nodeʳᵇ t₁ t₃ black-parent (N.cancel-suc binv₁))
      (Red-black→Red-black-black t₅) black-child binv
  del-balanceʳ′ʳᵇ
    _ (nodeᶜ black) leaf (nodeʳᵇ (nodeʳᵇ _ _ _ ≡+) (_ , ≡0) _ _) _ _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  del-balanceʳ′ʳᵇ
    _ leaf (nodeᶜ black) (nodeʳᵇ (_ , ≡0) (nodeʳᵇ _ _ _ ≡+) _ _) _ _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  del-balanceʳ′ʳᵇ
    _ leaf (node red (nodeᶜ red) _ _)
    (nodeʳᵇ _ (nodeʳᵇ (nodeʳᵇ _ _ rinv _) _ _ _) _ _) _ _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceʳ′ʳᵇ
    _ leaf (node red (nodeᶜ black) _ _)
    (nodeʳᵇ (_ , ≡0) (nodeʳᵇ (nodeʳᵇ _ _ _ ≡+) _ _ binv) _ _) _ _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) (trans binv ≡+)))
  del-balanceʳ′ʳᵇ
    _ leaf (node red _ _ (nodeᶜ red))
    (nodeʳᵇ _ (nodeʳᵇ _ (nodeʳᵇ _ _ rinv _) _ _) _ _) _ _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceʳ′ʳᵇ
    _ leaf (node red _ _ (nodeᶜ black))
    (nodeʳᵇ (_ , ≡0) (nodeʳᵇ _ (nodeʳᵇ _ _ _ ≡+) _ binv) _ _) _ _ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) (trans binv ≡+)))

opaque
  unfolding Black-invariant del-balanceˡ

  -- The function del-balanceˡ produces red-black trees, given certain
  -- assumptions.

  @0 del-balanceˡʳᵇ :
    ∀ c b₁ t₃ →
    let b , t = del-balanceˡ c (b₁ , t₁) x₂ t₃
        n′    = if b₁ then suc n else n
    in
    Red-black (if b₁ then red else c) n lb [ x₂ ] t₁ →
    Red-black c n′ [ x₂ ] ub t₃ →
    Red-invariant pc c →
    Black-invariant c (if b then n else n′) m →
    Red-black (if b then red else pc) m lb ub t
  del-balanceˡʳᵇ _ false _ t₁ t₃ rinv binv =
    nodeʳᵇ t₁ t₃ rinv binv
  del-balanceˡʳᵇ _ true (nodeᶜ black) t₁ t₃ rinv binv =
    del-balanceˡ′ʳᵇ _ _ _ t₁ t₃ rinv binv
  del-balanceˡʳᵇ
    {n} black true (node red (nodeᶜ black) _ (nodeᶜ black)) t₁
    (nodeʳᵇ (nodeʳᵇ t₃ t₅ rinv₁ binv₁) (nodeʳᵇ t₇ t₉ _ binv₂) rinv₃
       binv₃)
    rinv binv =
    nodeʳᵇ
      (Red-black→Red-black-black
         (del-balanceˡ′ʳᵇ _ _ _ t₁
            (nodeʳᵇ t₃ t₅ rinv₁ (trans binv₃ binv₁)) rinv₃
            (cong (if_then n else suc n)
               (sym (del-balanceˡ′-red≡false _ _)))))
      (nodeʳᵇ t₇ t₉ black-parent (trans binv₃ binv₂)) rinv binv
  del-balanceˡʳᵇ
    black true (node red (nodeᶜ red) _ _) _
    (nodeʳᵇ (nodeʳᵇ _ _ rinv _) _ _ _) _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceˡʳᵇ
    black true (node red _ _ (nodeᶜ red)) _
    (nodeʳᵇ _ (nodeʳᵇ _ _ rinv _) _ _) _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceˡʳᵇ
    black true (node red leaf _ _) _ (nodeʳᵇ (_ , ≡0) _ _ binv) _ _ =
    ⊥-elim (N.0≢+ (sym (trans binv ≡0)))
  del-balanceˡʳᵇ
    black true (node red _ _ leaf) _ (nodeʳᵇ _ (_ , ≡0) _ binv) _ _ =
    ⊥-elim (N.0≢+ (sym (trans binv ≡0)))
  del-balanceˡʳᵇ _ true leaf _ (_ , +≡0) _ _ =
    ⊥-elim (N.0≢+ (sym +≡0))
  del-balanceˡʳᵇ red true (nodeᶜ red) _ (nodeʳᵇ _ _ rinv _) _ _ =
    ⊥-elim (not-red-red rinv)

opaque
  unfolding Black-invariant del-balanceʳ

  -- The function del-balanceʳ produces red-black trees, given certain
  -- assumptions.

  @0 del-balanceʳʳᵇ :
    ∀ c t₁ b₁ →
    let b , t = del-balanceʳ c t₁ x₂ (b₁ , t₃)
        n′    = if b₁ then suc n else n
    in
    Red-black c n′ lb [ x₂ ] t₁ →
    Red-black (if b₁ then red else c) n [ x₂ ] ub t₃ →
    Red-invariant pc c →
    Black-invariant c (if b then n else n′) m →
    Red-black (if b then red else pc) m lb ub t
  del-balanceʳʳᵇ _ _ false t₁ t₃ rinv binv =
    nodeʳᵇ t₁ t₃ rinv binv
  del-balanceʳʳᵇ _ (nodeᶜ black) true t₁ t₃ rinv binv =
    del-balanceʳ′ʳᵇ _ _ _ t₁ t₃ rinv binv
  del-balanceʳʳᵇ
    {n} black (node red (nodeᶜ black) _ (nodeᶜ black)) true
    (nodeʳᵇ (nodeʳᵇ t₁ t₃ rinv₁ binv₁) (nodeʳᵇ t₅ t₇ _ binv₂) rinv₃
       binv₃)
    t₉ rinv binv =
    nodeʳᵇ (nodeʳᵇ t₁ t₃ black-parent (trans binv₃ binv₁))
      (Red-black→Red-black-black
         (del-balanceʳ′ʳᵇ _ _ _ (nodeʳᵇ t₅ t₇ rinv₁ (trans binv₃ binv₂))
            t₉ rinv₃
            (cong (if_then n else suc n)
               (sym (del-balanceʳ′-red≡false _ _)))))
       rinv binv
  del-balanceʳʳᵇ
    black (node red (nodeᶜ red) _ _) true
    (nodeʳᵇ (nodeʳᵇ _ _ rinv _) _ _ _) _ _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceʳʳᵇ
    black (node red _ _ (nodeᶜ red)) true
    (nodeʳᵇ _ (nodeʳᵇ _ _ rinv _) _ _) _ _ _ =
    ⊥-elim (not-red-red rinv)
  del-balanceʳʳᵇ
    black (node red leaf _ _) true (nodeʳᵇ (_ , ≡0) _ _ binv) _ _ _ =
    ⊥-elim (N.0≢+ (sym (trans binv ≡0)))
  del-balanceʳʳᵇ
    black (node red _ _ leaf) true (nodeʳᵇ _ (_ , ≡0) _ binv) _ _ _ =
    ⊥-elim (N.0≢+ (sym (trans binv ≡0)))
  del-balanceʳʳᵇ _ leaf true (_ , +≡0) _ _ _ =
    ⊥-elim (N.0≢+ (sym +≡0))
  del-balanceʳʳᵇ red (nodeᶜ red) true (nodeʳᵇ _ _ rinv _) _ _ _ =
    ⊥-elim (not-red-red rinv)

------------------------------------------------------------------------
-- Membership lemmas for the balancing functions used by deletion

opaque
  unfolding del-balanceˡ′

  -- A membership lemma for del-balanceˡ′.

  @0 ∈⁻-del-balanceˡ′ :
    x ∈⁻ del-balanceˡ′ c t₁ x₂ t₃ x₄ t₅ .proj₂ ⇔
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ (x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅)
  ∈⁻-del-balanceˡ′ {t₅ = nodeᶜ red} = record
    { to = λ where
        (inj₁ (inj₁ p))        → inj₁ p
        (inj₁ (inj₂ (inj₁ p))) → inj₂ (inj₁ p)
        (inj₁ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₁ p))
        (inj₂ p)               → inj₂ (inj₂ (inj₂ p))
    ; from = λ where
        (inj₁ p)               → inj₁ (inj₁ p)
        (inj₂ (inj₁ p))        → inj₁ (inj₂ (inj₁ p))
        (inj₂ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₂ p))
        (inj₂ (inj₂ (inj₂ p))) → inj₂ p
    }
  ∈⁻-del-balanceˡ′ {t₃ = nodeᶜ red} {t₅ = nodeᶜ black} = record
    { to = λ where
        (inj₁ (inj₁ p))        → inj₁ p
        (inj₁ (inj₂ (inj₁ p))) → inj₂ (inj₁ p)
        (inj₁ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₁ (inj₁ p)))
        (inj₂ (inj₁ p))        → inj₂ (inj₂ (inj₁ (inj₂ (inj₁ p))))
        (inj₂ (inj₂ (inj₁ p))) → inj₂ (inj₂ (inj₁ (inj₂ (inj₂ p))))
        (inj₂ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₂ p))
    ; from = λ where
        (inj₁ p)                             → inj₁ (inj₁ p)
        (inj₂ (inj₁ p))                      → inj₁ (inj₂ (inj₁ p))
        (inj₂ (inj₂ (inj₁ (inj₁ p))))        → inj₁ (inj₂ (inj₂ p))
        (inj₂ (inj₂ (inj₁ (inj₂ (inj₁ p))))) → inj₂ (inj₁ p)
        (inj₂ (inj₂ (inj₁ (inj₂ (inj₂ p))))) → inj₂ (inj₂ (inj₁ p))
        (inj₂ (inj₂ (inj₂ p)))               → inj₂ (inj₂ (inj₂ p))
    }
  ∈⁻-del-balanceˡ′ {t₃ = nodeᶜ black} {t₅ = nodeᶜ black} =
    F.id
  ∈⁻-del-balanceˡ′ {t₃ = node⁰} {t₅ = leaf} = record
    { to = λ where
        (inj₁ (inj₁ p))        → inj₁ p
        (inj₁ (inj₂ (inj₁ p))) → inj₂ (inj₁ p)
        (inj₁ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₁ (inj₁ p)))
        (inj₂ (inj₁ p))        → inj₂ (inj₂ (inj₁ (inj₂ (inj₁ p))))
        (inj₂ (inj₂ (inj₁ p))) → inj₂ (inj₂ (inj₁ (inj₂ (inj₂ p))))
        (inj₂ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₂ p))
    ; from = λ where
        (inj₁ p)                             → inj₁ (inj₁ p)
        (inj₂ (inj₁ p))                      → inj₁ (inj₂ (inj₁ p))
        (inj₂ (inj₂ (inj₁ (inj₁ p))))        → inj₁ (inj₂ (inj₂ p))
        (inj₂ (inj₂ (inj₁ (inj₂ (inj₁ p))))) → inj₂ (inj₁ p)
        (inj₂ (inj₂ (inj₁ (inj₂ (inj₂ p))))) → inj₂ (inj₂ (inj₁ p))
        (inj₂ (inj₂ (inj₂ p)))               → inj₂ (inj₂ (inj₂ p))
    }
  ∈⁻-del-balanceˡ′ {t₃ = leaf} {t₅ = leaf} =
    F.id
  ∈⁻-del-balanceˡ′ {t₃ = leaf} {t₅ = nodeᶜ black} =
    F.id

opaque
  unfolding del-balanceʳ′

  -- A membership lemma for del-balanceʳ′.

  @0 ∈⁻-del-balanceʳ′ :
    x ∈⁻ del-balanceʳ′ c t₁ x₂ t₃ x₄ t₅ .proj₂ ⇔
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃) ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅
  ∈⁻-del-balanceʳ′ {t₁ = nodeᶜ red} = record
    { to = λ where
        (inj₁ p)               → inj₁ (inj₁ p)
        (inj₂ (inj₁ p))        → inj₁ (inj₂ (inj₁ p))
        (inj₂ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₂ p))
        (inj₂ (inj₂ (inj₂ p))) → inj₂ p
    ; from = λ where
        (inj₁ (inj₁ p))        → inj₁ p
        (inj₁ (inj₂ (inj₁ p))) → inj₂ (inj₁ p)
        (inj₁ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₁ p))
        (inj₂ p)               → inj₂ (inj₂ (inj₂ p))
    }
  ∈⁻-del-balanceʳ′ {t₁ = nodeᶜ black} {t₃ = nodeᶜ red} = record
    { to = λ where
        (inj₁ (inj₁ p))        → inj₁ (inj₁ p)
        (inj₁ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₁ p))
        (inj₁ (inj₂ (inj₂ p))) → inj₁ (inj₂ (inj₂ (inj₁ p)))
        (inj₂ (inj₁ p))        → inj₁ (inj₂ (inj₂ (inj₂ (inj₁ p))))
        (inj₂ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₂ (inj₂ (inj₂ p))))
        (inj₂ (inj₂ (inj₂ p))) → inj₂ p
    ; from = λ where
        (inj₁ (inj₁ p))                      → inj₁ (inj₁ p)
        (inj₁ (inj₂ (inj₁ p)))               → inj₁ (inj₂ (inj₁ p))
        (inj₁ (inj₂ (inj₂ (inj₁ p))))        → inj₁ (inj₂ (inj₂ p))
        (inj₁ (inj₂ (inj₂ (inj₂ (inj₁ p))))) → inj₂ (inj₁ p)
        (inj₁ (inj₂ (inj₂ (inj₂ (inj₂ p))))) → inj₂ (inj₂ (inj₁ p))
        (inj₂ p)                             → inj₂ (inj₂ (inj₂ p))
    }
  ∈⁻-del-balanceʳ′ {t₁ = nodeᶜ black} {t₃ = nodeᶜ black} =
    F.id
  ∈⁻-del-balanceʳ′ {t₁ = leaf} {t₃ = node⁰} = record
    { to = λ where
        (inj₁ (inj₁ p))        → inj₁ (inj₁ p)
        (inj₁ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₁ p))
        (inj₁ (inj₂ (inj₂ p))) → inj₁ (inj₂ (inj₂ (inj₁ p)))
        (inj₂ (inj₁ p))        → inj₁ (inj₂ (inj₂ (inj₂ (inj₁ p))))
        (inj₂ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₂ (inj₂ (inj₂ p))))
        (inj₂ (inj₂ (inj₂ p))) → inj₂ p
    ; from = λ where
        (inj₁ (inj₁ p))                       → inj₁ (inj₁ p)
        (inj₁ (inj₂ (inj₁ p)))                → inj₁ (inj₂ (inj₁ p))
        (inj₁ (inj₂ (inj₂ (inj₁ p))))         → inj₁ (inj₂ (inj₂ p))
        (inj₁ (inj₂ (inj₂ (inj₂ (inj₁ p)))))  → inj₂ (inj₁ p)
        (inj₁ (inj₂ (inj₂ (inj₂ (inj₂ p)))))  → inj₂ (inj₂ (inj₁ p))
        (inj₂ p)                              → inj₂ (inj₂ (inj₂ p))
    }
  ∈⁻-del-balanceʳ′ {t₁ = leaf} {t₃ = leaf} =
    F.id
  ∈⁻-del-balanceʳ′ {t₁ = nodeᶜ black} {t₃ = leaf} =
    F.id

opaque
  unfolding del-balanceˡ

  -- A membership lemma for del-balanceˡ.

  @0 ∈⁻-del-balanceˡ :
    x ∈⁻ del-balanceˡ c (b , t₁) x₂ t₃ .proj₂ ⇔
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃
  ∈⁻-del-balanceˡ {b = false} =
    F.id
  ∈⁻-del-balanceˡ {b = true} {t₃ = nodeᶜ black} =
    ∈⁻-del-balanceˡ′
  ∈⁻-del-balanceˡ
    {x} {b = true} {t₁} {x₂}
    {t₃ = node red (node black t₃ x₄ t₅) x₆ t₇} =
    x ∈⁻ del-balanceˡ′ red t₁ x₂ t₃ x₄ t₅ .proj₂ ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇       ↝⟨ ∈⁻-del-balanceˡ′ ⊎-cong F.id ⟩
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ (x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅)) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇  ↝⟨ record
                                                                               { to = λ where
                                                                                   (inj₁ (inj₁ p))        → inj₁ p
                                                                                   (inj₁ (inj₂ (inj₁ p))) → inj₂ (inj₁ p)
                                                                                   (inj₁ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₁ p))
                                                                                   (inj₂ p)               → inj₂ (inj₂ (inj₂ p))
                                                                               ; from = λ where
                                                                                   (inj₁ p)               → inj₁ (inj₁ p)
                                                                                   (inj₂ (inj₁ p))        → inj₁ (inj₂ (inj₁ p))
                                                                                   (inj₂ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₂ p))
                                                                                   (inj₂ (inj₂ (inj₂ p))) → inj₂ p
                                                                               } ⟩□
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ (x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇    □
  ∈⁻-del-balanceˡ {b = true} {t₃ = node red (nodeᶜ red) _ _} =
    F.id
  ∈⁻-del-balanceˡ {b = true} {t₃ = node red leaf _ _} =
    F.id
  ∈⁻-del-balanceˡ {b = true} {t₃ = leaf} =
    F.id

opaque
  unfolding del-balanceʳ

  -- A membership lemma for del-balanceʳ.

  @0 ∈⁻-del-balanceʳ :
    x ∈⁻ del-balanceʳ c t₁ x₂ (b , t₃) .proj₂ ⇔
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃
  ∈⁻-del-balanceʳ {b = false} =
    F.id
  ∈⁻-del-balanceʳ {t₁ = nodeᶜ black} {b = true} =
    ∈⁻-del-balanceʳ′
  ∈⁻-del-balanceʳ
    {x} {t₁ = node red t₁ x₂ (node black t₃ x₄ t₅)} {x₂ = x₆} {b = true}
    {t₃ = t₇} =
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ del-balanceʳ′ red t₃ x₄ t₅ x₆ t₇ .proj₂       ↝⟨ F.id ⊎-cong F.id ⊎-cong ∈⁻-del-balanceʳ′ ⟩
    x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ ((x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇)  ↝⟨ record
                                                                               { to = λ where
                                                                                   (inj₁ p)               → inj₁ (inj₁ p)
                                                                                   (inj₂ (inj₁ p))        → inj₁ (inj₂ (inj₁ p))
                                                                                   (inj₂ (inj₂ (inj₁ p))) → inj₁ (inj₂ (inj₂ p))
                                                                                   (inj₂ (inj₂ (inj₂ p))) → inj₂ p
                                                                               ; from = λ where
                                                                                   (inj₁ (inj₁ p))        → inj₁ p
                                                                                   (inj₁ (inj₂ (inj₁ p))) → inj₂ (inj₁ p)
                                                                                   (inj₁ (inj₂ (inj₂ p))) → inj₂ (inj₂ (inj₁ p))
                                                                                   (inj₂ p)               → inj₂ (inj₂ (inj₂ p))
                                                                               } ⟩□
    (x ∈⁻ t₁ ⊎ x ≡ x₂ ⊎ x ∈⁻ t₃ ⊎ x ≡ x₄ ⊎ x ∈⁻ t₅) ⊎ x ≡ x₆ ⊎ x ∈⁻ t₇    □
  ∈⁻-del-balanceʳ {t₁ = node red _ _ (nodeᶜ red)} {b = true} =
    F.id
  ∈⁻-del-balanceʳ {t₁ = node red _ _ leaf} {b = true} =
    F.id
  ∈⁻-del-balanceʳ {t₁ = leaf} {b = true} =
    F.id

------------------------------------------------------------------------
-- Deleting the minimum element

opaque

  -- Returns and deletes the minimum element. The tree must be
  -- non-empty. If the returned boolean is true, then
  --
  -- * the returned tree's black height is the predecessor of the
  --   input tree's black height (assuming that the input tree is
  --   well-formed), and
  --
  -- * the returned tree's root, if any, is black.

  delete-min⁻ : (t : Tree⁻) → @0 t ≢ leaf → A × Bool × Tree⁻
  delete-min⁻ leaf hyp =
    ⊥-elim₀ (hyp (refl _))
  delete-min⁻ (node c l@node⁰ y r) _ =
    case delete-min⁻ l node≢leaf of λ
      (x , l) →
    x , del-balanceˡ c l y r
  delete-min⁻ (node red leaf y r) _ =
    y , false , r
  delete-min⁻ (node black leaf y leaf) _ =
    y , true , leaf
  delete-min⁻ (node black leaf y r@node⁰) _ =
    y , false , colour-root-black r

opaque

  -- Returns and deletes the minimum element, if any. If the tree is
  -- empty, then nothing is returned.

  delete-min⁻₀ : Tree⁻ → Maybe (A × Tree⁻)
  delete-min⁻₀ leaf    = nothing
  delete-min⁻₀ t@node⁰ =
    just (Σ-map id proj₂ (delete-min⁻ t node≢leaf))

------------------------------------------------------------------------
-- Deletion of the minimum element produces red-black trees, given
-- certain assumptions

opaque
  unfolding Black-invariant colour-root-black delete-min⁻

  -- The function delete-min⁻ produces red-black trees, given certain
  -- assumptions.

  @0 delete-min⁻ʳᵇ :
    (t : Tree⁻)
    (t≢leaf : t ≢ leaf) →
    let x , b , t′ = delete-min⁻ t t≢leaf in
    Red-black pc n lb ub t →
    (b ≡ true → n ≢ 0) ×
    Red-black (if b then red else pc) (if b then N.pred n else n) [ x ]
      ub t′
  delete-min⁻ʳᵇ leaf hyp _ =
    ⊥-elim₀ (hyp (refl _))
  delete-min⁻ʳᵇ (node red leaf _ _) _ (nodeʳᵇ _ r _ binv) =
    ⊥-elim ∘ Bool.true≢false ∘ sym ,
    cast (sym binv) (Red-black-red→Red-black r)
  delete-min⁻ʳᵇ (node black leaf _ leaf) _ (nodeʳᵇ _ r _ binv) =
    (λ _ → N.0≢+ ∘ flip trans binv ∘ sym) ,
    r .proj₁ , trans (cong N.pred binv) (r .proj₂)
  delete-min⁻ʳᵇ
    (node black leaf _ (nodeᶜ red)) _
    (nodeʳᵇ _ (nodeʳᵇ l r _ binv₁) _ binv) =
    ⊥-elim ∘ Bool.true≢false ∘ sym ,
    nodeʳᵇ (Red-black→Red-black-black l) (Red-black→Red-black-black r)
      black-child (trans binv (cong suc binv₁))
  delete-min⁻ʳᵇ
    (node black leaf _ (nodeᶜ black)) _
    (nodeʳᵇ (_ , ≡0) (nodeʳᵇ _ _ _ ≡+) _ _) =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  delete-min⁻ʳᵇ
    {n} {ub} (node c l@node⁰ x r) _
    (n′ , lʳᵇ@(nodeʳᵇ llʳᵇ lrʳᵇ rinv₁ binv₁) , rʳᵇ , rinv , binv) =
    let _ , b , l′ = delete-min⁻ l node≢leaf
        b′ , _     = del-balanceˡ c (b , l′) x r
        ≢0 , l′ʳᵇ  = delete-min⁻ʳᵇ _ node≢leaf lʳᵇ

        ≢0′ : b′ ≡ true → n ≢ 0
        ≢0′ b′≡true =
          Black-invariant→≢0→≢0 {c = c} binv
            (≢0 (del-balanceˡ≡true→ _ b′≡true))

        n″ = if b then N.pred n′ else n′

        rʳᵇ′ : Red-black c (if b then suc n″ else n″) [ x ] ub r
        rʳᵇ′ = cast (if-lemma ≢0) rʳᵇ

        binv′ :
          Black-invariant c
            (if b′ then n″ else (if b then suc n″ else n″))
            (if b′ then N.pred n else n)
        binv′ =
          Black-invariant-lemma c b b′ ≢0 (del-balanceˡ≡true→ _) binv
    in
    ≢0′ , del-balanceˡʳᵇ _ _ _ l′ʳᵇ rʳᵇ′ rinv binv′

opaque
  unfolding delete-min⁻₀

  -- The function delete-min⁻₀ produces red-black trees, given certain
  -- assumptions.

  @0 delete-min⁻₀ʳᵇ :
    (t : Tree⁻) →
    delete-min⁻₀ t ≡ just (x , t′) →
    Red-black pc n lb ub t →
    ∃ λ n → Red-black pc n [ x ] ub t′
  delete-min⁻₀ʳᵇ leaf hyp _ =
    ⊥-elim (⊎.inj₁≢inj₂ hyp)
  delete-min⁻₀ʳᵇ t@node⁰ hyp tʳᵇ
    with delete-min⁻ t node≢leaf
       | delete-min⁻ʳᵇ _ node≢leaf tʳᵇ
  … | _ , false , _ | _ , t′ =
    _ ,
    subst (λ (lb , t) → Red-black _ _ [ lb ] _ t) (⊎.cancel-inj₂ hyp) t′
  … | _ , true , _ | _ , t′ =
    _ ,
    subst (λ (lb , t) → Red-black _ _ [ lb ] _ t) (⊎.cancel-inj₂ hyp)
      (Red-black-red→Red-black t′)

------------------------------------------------------------------------
-- Membership lemmas for deletion of the minimum element

opaque
  unfolding colour-root-black delete-min⁻

  -- A membership lemma for delete-min⁻.

  @0 ∈⁻-delete-min⁻ :
    (t≢leaf : t ≢ leaf) →
    let x , _ , t′ = delete-min⁻ t t≢leaf in
    y ∈⁻ t ⇔ y ≡ x ⊎ y ∈⁻ t′
  ∈⁻-delete-min⁻ {t = leaf} hyp =
    ⊥-elim₀ (hyp (refl _))
  ∈⁻-delete-min⁻ {t = node red leaf _ _} _ =
    from-bijection ⊎-left-identity
  ∈⁻-delete-min⁻ {t = node black leaf _ leaf} _ =
    from-bijection ⊎-left-identity
  ∈⁻-delete-min⁻ {t = node black leaf _ node⁰} _ =
    from-bijection ⊎-left-identity
  ∈⁻-delete-min⁻ {t = node c t₁@node⁰ x₂ t₃} {y} _ =
    let x , b , t₁′ = delete-min⁻ t₁ _ in
    y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃                          ↝⟨ ∈⁻-delete-min⁻ _ ⊎-cong F.id ⟩
    (y ≡ x ⊎ y ∈⁻ t₁′) ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃               ↔⟨ inverse ⊎-assoc ⟩
    y ≡ x ⊎ (y ∈⁻ t₁′ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃)               ↝⟨ F.id ⊎-cong inverse ∈⁻-del-balanceˡ ⟩□
    y ≡ x ⊎ y ∈⁻ del-balanceˡ c (b , t₁′) x₂ t₃ .proj₂  □

opaque
  unfolding delete-min⁻₀

  -- A membership lemma for delete-min⁻₀.

  @0 ∈⁻-delete-min⁻₀ :
    delete-min⁻₀ t ≡ just (x , t′) →
    y ∈⁻ t ⇔ y ≡ x ⊎ y ∈⁻ t′
  ∈⁻-delete-min⁻₀ {t = leaf} hyp =
    ⊥-elim (⊎.inj₁≢inj₂ hyp)
  ∈⁻-delete-min⁻₀ {t = t@node⁰} {x} {t′} {y} hyp =
    let x′ , _ , t″ = delete-min⁻ t node≢leaf in
    y ∈⁻ t            ↝⟨ ∈⁻-delete-min⁻ _ ⟩
    y ≡ x′ ⊎ y ∈⁻ t″  ↝⟨ ≡⇒↝ _ (cong (λ (x , t′) → y ≡ x ⊎ y ∈⁻ t′) (⊎.cancel-inj₂ hyp)) ⟩□
    y ≡ x  ⊎ y ∈⁻ t′  □

------------------------------------------------------------------------
-- Other lemmas related to deletion of the minimum element

opaque

  -- An ordering lemma for delete-min⁻.

  @0 <-delete-min⁻ :
    (t≢leaf : t ≢ leaf) →
    let x , _ , t′ = delete-min⁻ t t≢leaf in
    Red-black pc n lb ub t →
    y ∈⁻ t′ → x < y
  <-delete-min⁻ t≢leaf t y∈
    with ∈⁻→<< (delete-min⁻ʳᵇ _ t≢leaf t .proj₂) y∈
  … | []-[] x<y , _ = x<y

opaque

  -- An ordering lemma for delete-min⁻₀.

  @0 <-delete-min⁻₀ :
    delete-min⁻₀ t ≡ just (x , t′) →
    Red-black pc n lb ub t →
    y ∈⁻ t′ → x < y
  <-delete-min⁻₀ eq t y∈
    with ∈⁻→<< (delete-min⁻₀ʳᵇ _ eq t .proj₂) y∈
  … | []-[] x<y , _ = x<y

opaque
  unfolding delete-min⁻₀

  -- The function delete-min⁻₀ returns nothing if and only if the tree
  -- is empty.

  @0 Is-nothing-delete-min⁻₀ :
    Is-nothing (delete-min⁻₀ t) ⇔ (∀ {x} → ¬ x ∈⁻ t)
  Is-nothing-delete-min⁻₀ {t = leaf} =
    record { to = λ _ () }
  Is-nothing-delete-min⁻₀ {t = node⁰} =
    record { to = ⊥-elim; from = _$ (inj₂ (inj₁ (refl _))) }

opaque
  unfolding delete-min⁻₀

  -- The value of delete-min⁻₀ t is just something if and only if t is
  -- non-empty.

  @0 Is-just-delete-min⁻₀ :
    Is-just (delete-min⁻₀ t) ⇔ (∃ λ x → x ∈⁻ t)
  Is-just-delete-min⁻₀ {t = leaf} =
    from-bijection (inverse ×-right-zero)
  Is-just-delete-min⁻₀ {t = node _ _ x _} =
    record { to = λ _ → x , inj₂ (inj₁ (refl _)) }

opaque

  -- If the non-empty tree t is red-black, every element in t is
  -- either equal to x or in t′, x is strictly smaller than all
  -- elements in t′, and delete-min⁻ t is x′ , b , t″, then x is equal
  -- to x′ and t′ contains the same elements as t″.

  @0 delete-min⁻-unique :
    (t≢leaf : t ≢ leaf) →
    Red-black pc n lb ub t →
    (∀ {y} → y ∈⁻ t′ → x < y) →
    (∀ {y} → y ∈⁻ t ⇔ y ≡ x ⊎ y ∈⁻ t′) →
    let x′ , _ , t″ = delete-min⁻ t t≢leaf in
    x ≡ x′ × (∀ {y} → y ∈⁻ t′ ⇔ y ∈⁻ t″)
  delete-min⁻-unique {t} {t′} {x} t≢leaf tʳᵇ ∈→< ∈⇔ =
    let x′ , _ , t″ = delete-min⁻ t t≢leaf

        x≤x′ =
          P.[ O.≤-reflexive ∘ sym , O.<→≤ ∘ ∈→< ]
             (_⇔_.to (∈⇔ {y = x′})
                (_⇔_.from (∈⁻-delete-min⁻ t≢leaf) (inj₁ (refl _))))

        x′≤x =
          P.[ O.≤-reflexive ∘ sym , O.<→≤ ∘ <-delete-min⁻ t≢leaf tʳᵇ ]
            (_⇔_.to (∈⁻-delete-min⁻ t≢leaf)
               (_⇔_.from ∈⇔ (inj₁ (refl _))))

        x≡x′ = O.≤-antisym x≤x′ x′≤x
    in
    x≡x′ ,
    (λ {y} →
       y ∈⁻ t′          ↝⟨ inverse (⇔⊎→×¬⇔ ∈⇔ (flip (lemma ∘ ∈→<))) ⟩
       y ∈⁻ t × y ≢ x   ↝⟨ F.id ×-cong ¬-cong _ (≡⇒↝ _ (cong (_ ≡_) x≡x′)) ⟩
       y ∈⁻ t × y ≢ x′  ↝⟨ ⇔⊎→×¬⇔ (∈⁻-delete-min⁻ t≢leaf) (flip (lemma ∘ <-delete-min⁻ t≢leaf tʳᵇ)) ⟩□
       y ∈⁻ t″          □)
    where
    lemma : z < y → y ≡ z → ⊥₀
    lemma = (_∘ sym) ∘ O.<→≢

opaque
  unfolding delete-min⁻₀

  -- If t is red-black, every element in t is either equal to x or in
  -- t′, and x is strictly smaller than all elements in t′, then
  -- delete-min⁻₀ t is just (x , t″) for some t″ that contains the
  -- same elements as t′.

  @0 delete-min⁻₀-just :
    Red-black pc n lb ub t →
    (∀ {y} → y ∈⁻ t′ → x < y) →
    (∀ {y} → y ∈⁻ t ⇔ y ≡ x ⊎ y ∈⁻ t′) →
    ∃ λ t″ →
        delete-min⁻₀ t ≡ just (x , t″) × (∀ {y} → y ∈⁻ t′ ⇔ y ∈⁻ t″)
  delete-min⁻₀-just {t = leaf} tʳᵇ _ hyp =
    ⊥-elim (_⇔_.from hyp (inj₁ (refl _)))
  delete-min⁻₀-just {t = node⁰} tʳᵇ hyp₁ hyp₂ =
    let x≡x′ , t′≈t″ = delete-min⁻-unique node≢leaf tʳᵇ hyp₁ hyp₂ in
    _ , cong just (cong (_, _) (sym x≡x′)) , t′≈t″

opaque

  -- If t is red-black, then the value of delete-min⁻₀ t is
  -- just (x , t″) for some tree t″ that contains the same elements as
  -- t′ if and only if
  --
  -- * x is strictly smaller than all elements in t′ and
  --
  -- * every value is in t if and only it is either equal to x or in
  --   t′.

  @0 delete-min⁻₀-just-⇔ :
    Red-black pc n lb ub t →
    (∃ λ t″ →
       delete-min⁻₀ t ≡ just (x , t″) × (∀ {y} → y ∈⁻ t′ ⇔ y ∈⁻ t″)) ⇔
    (∀ {y} → y ∈⁻ t′ → x < y) × (∀ {y} → y ∈⁻ t ⇔ y ≡ x ⊎ y ∈⁻ t′)
  delete-min⁻₀-just-⇔ t = record
    { to = λ (_ , eq , t′≈t″) →
        <-delete-min⁻₀ eq t ∘ _⇔_.to t′≈t″ ,
        (F.id ⊎-cong inverse t′≈t″) F.∘ ∈⁻-delete-min⁻₀ eq
    ; from = uncurry (delete-min⁻₀-just t)
    }

------------------------------------------------------------------------
-- Deletion

opaque

  -- Deletes the given element. If the boolean is true, then the
  -- returned tree's black height is the predecessor of the input
  -- tree's black height (assuming that the input tree is
  -- well-formed). If the returned tree has a root, then it is black
  -- or has the same colour as the input's root. TODO

  delete⁻′ : A → Tree⁻ → Bool × Tree⁻
  delete⁻′ _ leaf =
    false , leaf
  delete⁻′ x (node c l y r) with O.compare x y
  … | ltᵀ _ = del-balanceˡ c (delete⁻′ x l) y r
  … | gtᵀ _ = del-balanceʳ c l y (delete⁻′ x r)
  delete⁻′ _ (node c leaf _ leaf) | eqᵀ _ =
    is-black c , leaf
  delete⁻′ _ (node _ l@node⁰ _ leaf) | eqᵀ _ =
    false , colour-root-black l
  delete⁻′ _ (node _ leaf _ r@node⁰) | eqᵀ _ =
    false , colour-root-black r
  delete⁻′ _ (node c l@node⁰ _ r@node⁰) | eqᵀ _ =
    case delete-min⁻ r node≢leaf of λ
      (z , r) →
    del-balanceʳ c l z r

opaque

  -- Deletes the given element, if it exists in the tree.

  delete⁻ : A → Tree⁻ → Tree⁻
  delete⁻ x t = delete⁻′ x t .proj₂

------------------------------------------------------------------------
-- Deletion produces red-black trees, given certain assumptions

opaque
  unfolding Black-invariant colour-root-black delete⁻′ is-black

  -- The function delete⁻′ produces red-black trees, given certain
  -- assumptions.

  @0 delete⁻′ʳᵇ :
    (t : Tree⁻) →
    let b , t′ = delete⁻′ x t in
    Red-black pc n lb ub t →
    (b ≡ true → n ≢ 0) ×
    Red-black (if b then red else pc) (if b then N.pred n else n) lb
      ub t′
  delete⁻′ʳᵇ leaf t =
    ⊥-elim ∘ Bool.true≢false ∘ sym , t
  delete⁻′ʳᵇ {x} (node _ _ y _) _ with O.compare x y
  delete⁻′ʳᵇ (node red leaf _ leaf) (nodeʳᵇ (lb< , _) (<ub , ≡0) _ binv)
    | eqᵀ _ =
    ⊥-elim ∘ Bool.true≢false ∘ sym ,
    leafʳᵇ (EO.<-trans lb< <ub) (trans binv ≡0)
  delete⁻′ʳᵇ
    (node black leaf _ leaf) (nodeʳᵇ (lb< , _) (<ub , ≡0) _ binv)
    | eqᵀ _ =
    (λ _ → N.0≢+ ∘ flip trans binv ∘ sym) ,
    leafʳᵇ (EO.<-trans lb< <ub) (trans (cong N.pred binv) ≡0)
  delete⁻′ʳᵇ
    (node black (nodeᶜ red) _ leaf)
    (nodeʳᵇ (nodeʳᵇ l r _ binv₁) (<ub , _) _ binv)
    | eqᵀ _ =
    ⊥-elim ∘ Bool.true≢false ∘ sym ,
    nodeʳᵇ (Red-black→Red-black-black l)
      (Red-black-<ʳ <ub (Red-black→Red-black-black r))
      black-child (trans binv (cong suc binv₁))
  delete⁻′ʳᵇ
    (node red (nodeᶜ red) _ leaf) (nodeʳᵇ (nodeʳᵇ _ _ rinv _) _ _ _)
    | eqᵀ _ =
    ⊥-elim (not-red-red rinv)
  delete⁻′ʳᵇ
    (node _ (nodeᶜ black) _ leaf)
    (nodeʳᵇ (nodeʳᵇ _ _ _ ≡+) (_ , ≡0) _ _)
    | eqᵀ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  delete⁻′ʳᵇ
    (node black leaf _ (nodeᶜ red))
    (nodeʳᵇ (lb< , _) (nodeʳᵇ l r _ binv₁) _ binv)
    | eqᵀ _ =
    ⊥-elim ∘ Bool.true≢false ∘ sym ,
    nodeʳᵇ (Red-black-<ˡ lb< (Red-black→Red-black-black l))
      (Red-black→Red-black-black r) black-child
      (trans binv (cong suc binv₁))
  delete⁻′ʳᵇ
    (node red leaf _ (nodeᶜ red))
    (nodeʳᵇ _ (nodeʳᵇ _ _ rinv _) _ _)
    | eqᵀ _ =
    ⊥-elim (not-red-red rinv)
  delete⁻′ʳᵇ
    (node _ leaf _ (nodeᶜ black))
    (nodeʳᵇ (_ , ≡0) (nodeʳᵇ _ _ _ ≡+) _ _)
    | eqᵀ _ =
    ⊥-elim (N.0≢+ (trans (sym ≡0) ≡+))
  delete⁻′ʳᵇ {n} {lb}
    (node c l@node⁰ y r@node⁰) (n′ , lʳᵇ , rʳᵇ , rinv , binv)
    | eqᵀ _ =
    let z , b , r′ = delete-min⁻ r node≢leaf
        ≢0 , r′ʳᵇ  = delete-min⁻ʳᵇ r node≢leaf rʳᵇ
        b′ , t     = del-balanceʳ c l z (b , r′)

        ≢0′ : b′ ≡ true → n ≢ 0
        ≢0′ b′≡true =
          Black-invariant→≢0→≢0 {c = c} binv
            (≢0 (del-balanceʳ≡true→ _ b′≡true))

        z∈r : z ∈⁻ r
        z∈r = _⇔_.from (∈⁻-delete-min⁻ node≢leaf) (inj₁ (refl _))

        [y]<[z] : [ y ] <ᴱ [ z ]
        [y]<[z] = ∈⁻→<< rʳᵇ z∈r .proj₁

        n″ = if b then N.pred n′ else n′
        n‴ = if b then suc n″ else n″

        n′≡n‴ : n′ ≡ n‴
        n′≡n‴ = if-lemma ≢0

        lʳᵇ′ : Red-black c n‴ lb [ z ] l
        lʳᵇ′ = cast {t = l} n′≡n‴ (Red-black-<ʳ {t = l} [y]<[z] lʳᵇ)

        binv′ :
          Black-invariant c (if b′ then n″ else n‴)
            (if b′ then N.pred n else n)
        binv′ =
          Black-invariant-lemma c b b′ ≢0 (del-balanceʳ≡true→ _) binv
    in
    ≢0′ , del-balanceʳʳᵇ _ _ _ lʳᵇ′ r′ʳᵇ rinv binv′
  delete⁻′ʳᵇ {x} {n} {ub} (node c l y r) (n′ , lʳᵇ , rʳᵇ , rinv , binv)
    | ltᵀ _ =
    let b , l′    = delete⁻′ x l
        ≢0 , l′ʳᵇ = delete⁻′ʳᵇ l lʳᵇ
        b′ , t    = del-balanceˡ c (b , l′) y r

        ≢0′ : b′ ≡ true → n ≢ 0
        ≢0′ b′≡true =
          Black-invariant→≢0→≢0 {c = c} binv
            (≢0 (del-balanceˡ≡true→ _ b′≡true))

        n″ = if b then N.pred n′ else n′
        n‴ = if b then suc n″ else n″

        n′≡n‴ : n′ ≡ n‴
        n′≡n‴ = if-lemma ≢0

        rʳᵇ′ : Red-black c n‴ [ y ] ub r
        rʳᵇ′ = cast n′≡n‴ rʳᵇ

        binv′ :
          Black-invariant c (if b′ then n″ else n‴)
            (if b′ then N.pred n else n)
        binv′ =
          Black-invariant-lemma c b b′ ≢0 (del-balanceˡ≡true→ _) binv
    in
    ≢0′ , del-balanceˡʳᵇ _ _ _ l′ʳᵇ rʳᵇ′ rinv binv′
  delete⁻′ʳᵇ {x} {n} {lb} (node c l y r) (n′ , lʳᵇ , rʳᵇ , rinv , binv)
    | gtᵀ _ =
    let b , r′    = delete⁻′ x r
        ≢0 , r′ʳᵇ = delete⁻′ʳᵇ r rʳᵇ
        b′ , t    = del-balanceʳ c l y (b , r′)

        ≢0′ : b′ ≡ true → n ≢ 0
        ≢0′ b′≡true =
          Black-invariant→≢0→≢0 {c = c} binv
            (≢0 (del-balanceʳ≡true→ _ b′≡true))

        n″ = if b then N.pred n′ else n′
        n‴ = if b then suc n″ else n″

        n′≡n‴ : n′ ≡ n‴
        n′≡n‴ = if-lemma ≢0

        lʳᵇ′ : Red-black c n‴ lb [ y ] l
        lʳᵇ′ = cast n′≡n‴ lʳᵇ

        binv′ :
          Black-invariant c (if b′ then n″ else n‴)
            (if b′ then N.pred n else n)
        binv′ =
          Black-invariant-lemma c b b′ ≢0 (del-balanceʳ≡true→ _) binv
    in
    ≢0′ , del-balanceʳʳᵇ _ _ _ lʳᵇ′ r′ʳᵇ rinv binv′

opaque
  unfolding delete⁻

  -- The function delete⁻ produces red-black trees, given certain
  -- assumptions.

  @0 delete⁻ʳᵇ :
    Red-black pc n lb ub t →
    ∃ λ n → Red-black pc n lb ub (delete⁻ x t)
  delete⁻ʳᵇ {t} {x} tʳᵇ with delete⁻′ x t | delete⁻′ʳᵇ {x = x} t tʳᵇ
  … | false , _ | _ , t′ʳᵇ = _ , t′ʳᵇ
  … | true  , _ | _ , t′ʳᵇ = _ , Red-black-red→Red-black t′ʳᵇ

------------------------------------------------------------------------
-- Membership lemmas for deletion

opaque
  unfolding colour-root-black delete⁻′

  -- A membership lemma for delete⁻′.

  @0 ∈⁻-delete⁻′ :
    Red-black pc n lb ub t →
    let _ , t′ = delete⁻′ x t in
    y ∈⁻ t′ ⇔ y ≢ x × y ∈⁻ t
  ∈⁻-delete⁻′ {t = leaf} _ =
    from-bijection (inverse ×-right-zero)
  ∈⁻-delete⁻′ {t = node _ _ z _} {x} _ with O.compare x z
  ∈⁻-delete⁻′ {t = node _ leaf _ leaf} _ | eqᵀ x≡z = record
    { to   = ⊥-elim
    ; from = λ where
        (y≢x , inj₂ (inj₁ y≡z)) → ⊥-elim (y≢x (trans y≡z (sym x≡z)))
    }
  ∈⁻-delete⁻′ {t = node _ node⁰ _ leaf} (nodeʳᵇ l _ _ _)
    | eqᵀ x≡z = record
    { to = λ y∈l →
        (λ y≡x → case ∈⁻→<< l y∈l of λ where
           (_ , []-[] y<z) → O.<→≢ y<z (trans y≡x x≡z)) ,
        inj₁ y∈l
    ; from = λ where
        (_ , inj₁ y∈l)          → y∈l
        (y≢x , inj₂ (inj₁ y≡z)) → ⊥-elim (y≢x (trans y≡z (sym x≡z)))
    }
  ∈⁻-delete⁻′ {t = node _ leaf _ node⁰} (nodeʳᵇ _ r _ _)
    | eqᵀ x≡z = record
    { to = λ y∈r →
        (λ y≡x → case ∈⁻→<< r y∈r of λ where
           ([]-[] z<y , _) → O.<→≢ z<y (sym (trans y≡x x≡z))) ,
        inj₂ (inj₂ y∈r)
    ; from = λ where
        (y≢x , inj₂ (inj₁ y≡z)) → ⊥-elim (y≢x (trans y≡z (sym x≡z)))
        (_ , inj₂ (inj₂ y∈r))   → y∈r
    }
  ∈⁻-delete⁻′
    {t = node c t₁@node⁰ x₂ t₃@node⁰} {x} {y} (nodeʳᵇ t₁ʳᵇ t₃ʳᵇ _ _)
    | eqᵀ x≡x₂ =
    let x₃ , b , t₄ = delete-min⁻ t₃ node≢leaf in
    y ∈⁻ del-balanceʳ c t₁ x₃ (b , t₄) .proj₂  ↝⟨ ∈⁻-del-balanceʳ ⟩
    y ∈⁻ t₁ ⊎ y ≡ x₃ ⊎ y ∈⁻ t₄                 ↝⟨ F.id ⊎-cong inverse (∈⁻-delete-min⁻ _) ⟩
    y ∈⁻ t₁ ⊎ y ∈⁻ t₃                          ↝⟨ record
                                                    { to = λ where
                                                        (inj₁ y∈t₁) →
                                                          (λ y≡x →
                                                             case ∈⁻→<< t₁ʳᵇ y∈t₁ of λ where
                                                               (_ , []-[] y<x₂) →
                                                                 O.<→≢ y<x₂ (trans y≡x x≡x₂)) ,
                                                          inj₁ y∈t₁
                                                        (inj₂ y∈t₃) →
                                                          (λ y≡x →
                                                             case ∈⁻→<< t₃ʳᵇ y∈t₃ of λ where
                                                               ([]-[] x₂<y , _) →
                                                                 O.<→≢ x₂<y (sym (trans y≡x x≡x₂))) ,
                                                          inj₂ (inj₂ y∈t₃)
                                                    ; from = λ where
                                                        (_   , inj₁ y∈t₁)        → inj₁ y∈t₁
                                                        (y≢x , inj₂ (inj₁ y≡x₂)) → ⊥-elim (y≢x (trans y≡x₂ (sym x≡x₂)))
                                                        (_   , inj₂ (inj₂ y∈t₃)) → inj₂ y∈t₃

                                                    } ⟩□
    y ≢ x × (y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃)       □
  ∈⁻-delete⁻′ {t = node c t₁ x₂ t₃} {x} {y} (nodeʳᵇ t₁ʳᵇ t₃ʳᵇ _ _)
    | ltᵀ x<x₂ =
    y ∈⁻ del-balanceˡ c (delete⁻′ x t₁) x₂ t₃ .proj₂  ↝⟨ ∈⁻-del-balanceˡ ⟩
    y ∈⁻ delete⁻′ x t₁ .proj₂ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃      ↝⟨ ∈⁻-delete⁻′ t₁ʳᵇ ⊎-cong F.id ⟩
    y ≢ x × y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃                ↝⟨ record
                                                           { to = λ where
                                                               (inj₁ (y≢x , y∈t₁)) → y≢x , inj₁ y∈t₁
                                                               (inj₂ (inj₁ y≡x₂))  →
                                                                 (λ y≡x → O.<→≢ x<x₂ (trans (sym y≡x) y≡x₂)) ,
                                                                 inj₂ (inj₁ y≡x₂)
                                                               (inj₂ (inj₂ y∈t₃)) →
                                                                 (λ y≡x →
                                                                    case ∈⁻→<< t₃ʳᵇ y∈t₃ of λ where
                                                                      ([]-[] x₂<y , _) →
                                                                        O.<→≢ (O.<-trans x<x₂ x₂<y) (sym y≡x)) ,
                                                                 inj₂ (inj₂ y∈t₃)
                                                           ; from = λ where
                                                               (y≢x , inj₁ y∈t₁)        → inj₁ (y≢x , y∈t₁)
                                                               (_   , inj₂ (inj₁ y≡x₂)) → inj₂ (inj₁ y≡x₂)
                                                               (_   , inj₂ (inj₂ y∈t₃)) → inj₂ (inj₂ y∈t₃)
                                                           } ⟩□
    y ≢ x × (y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃)              □
  ∈⁻-delete⁻′ {t = node c t₁ x₂ t₃} {x} {y} (nodeʳᵇ t₁ʳᵇ t₃ʳᵇ _ _)
    | gtᵀ x>x₂ =
    y ∈⁻ del-balanceʳ c t₁ x₂ (delete⁻′ x t₃) .proj₂  ↝⟨ ∈⁻-del-balanceʳ ⟩
    y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ∈⁻ delete⁻′ x t₃ .proj₂      ↝⟨ F.id ⊎-cong F.id ⊎-cong ∈⁻-delete⁻′ t₃ʳᵇ ⟩
    y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ≢ x × y ∈⁻ t₃                ↝⟨ record
                                                           { to = λ where
                                                               (inj₁ y∈t₁) →
                                                                 (λ y≡x →
                                                                    case ∈⁻→<< t₁ʳᵇ y∈t₁ of λ where
                                                                      (_ , []-[] y<x₂) →
                                                                        O.<→≢ (O.<-trans y<x₂ x>x₂) y≡x) ,
                                                                 inj₁ y∈t₁
                                                               (inj₂ (inj₁ y≡x₂)) →
                                                                 (λ y≡x → O.<→≢ x>x₂ (trans (sym y≡x₂) y≡x)) ,
                                                                 inj₂ (inj₁ y≡x₂)
                                                               (inj₂ (inj₂ (y≢x , y∈t₃))) → y≢x , inj₂ (inj₂ y∈t₃)
                                                           ; from = λ where
                                                               (_   , inj₁ y∈t₁)        → inj₁ y∈t₁
                                                               (_   , inj₂ (inj₁ y≡x₂)) → inj₂ (inj₁ y≡x₂)
                                                               (y≢x , inj₂ (inj₂ y∈t₃)) → inj₂ (inj₂ (y≢x , y∈t₃))
                                                           } ⟩□
    y ≢ x × (y ∈⁻ t₁ ⊎ y ≡ x₂ ⊎ y ∈⁻ t₃)              □

opaque
  unfolding delete⁻

  -- A membership lemma for delete⁻.

  @0 ∈⁻-delete⁻ :
    Red-black pc n lb ub t →
    y ∈⁻ delete⁻ x t ⇔ y ≢ x × y ∈⁻ t
  ∈⁻-delete⁻ = ∈⁻-delete⁻′

------------------------------------------------------------------------
-- Conversion to lists

private opaque

  -- A helper function used by to-List⁻.

  to-List⁻′ : Tree⁻ → List A → List A
  to-List⁻′ leaf           xs = xs
  to-List⁻′ (node _ l x r) xs = to-List⁻′ l (x ∷ to-List⁻′ r xs)

private opaque
  unfolding to-List⁻′

  -- A membership lemma for to-List⁻′.

  @0 ∈⁻-to-List⁻′ :
    (x L.∈ to-List⁻′ t xs) ≃ (x ∈⁻ t ⊎ x L.∈ xs)
  ∈⁻-to-List⁻′ {x} {t = leaf} {xs} =
    x L.∈ xs      ↔⟨ inverse ⊎-left-identity ⟩□
    ⊥ ⊎ x L.∈ xs  □
  ∈⁻-to-List⁻′ {x} {t = node _ l y r} {xs} =
    x L.∈ to-List⁻′ l (y ∷ to-List⁻′ r xs)  ↝⟨ ∈⁻-to-List⁻′ ⟩
    x ∈⁻ l ⊎ x ≡ y ⊎ x L.∈ to-List⁻′ r xs   ↝⟨ F.id ⊎-cong F.id ⊎-cong ∈⁻-to-List⁻′ ⟩
    x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r ⊎ x L.∈ xs      ↔⟨ F.⊎-assoc F.∘ (F.id ⊎-cong F.⊎-assoc) ⟩□
    (x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r) ⊎ x L.∈ xs    □

private opaque
  unfolding to-List⁻′

  -- The list returned by to-List⁻′ is sorted, given certain
  -- assumptions.

  @0 Sorted-to-List⁻′ :
    Red-black pc n b₁ b₂ t → Sorted-≤₁ b₂ b₃ xs →
    Sorted b₁ b₃ (to-List⁻′ t xs)
  Sorted-to-List⁻′ {t = leaf} {xs} (leafʳᵇ b₁<b₂ _) s =
    Sorted-≤₁→Sorted xs b₁<b₂ s
  Sorted-to-List⁻′ {t = node⁰} {xs} (nodeʳᵇ l r _ _) s =
    Sorted-to-List⁻′ l (EO.≤-refl , Sorted-to-List⁻′ r s)

opaque

  -- Converts the tree to a list.

  to-List⁻ : Tree⁻ → List A
  to-List⁻ t = to-List⁻′ t []

opaque
  unfolding to-List⁻

  -- A membership lemma for to-List⁻.

  @0 ∈⁻-to-List⁻ :
    (x L.∈ to-List⁻ t) ≃ (x ∈⁻ t)
  ∈⁻-to-List⁻ {x} {t} =
    x L.∈ to-List⁻′ t []  ↝⟨ ∈⁻-to-List⁻′ ⟩
    x ∈⁻ t ⊎ ⊥            ↔⟨ ⊎-right-identity ⟩□
    x ∈⁻ t                □

opaque
  unfolding to-List⁻

  -- The list returned by to-List⁻ is sorted, given a certain
  -- assumption.

  @0 Sorted-to-List⁻ :
    Red-black pc n lb ub t →
    Sorted lb ub (to-List⁻ t)
  Sorted-to-List⁻ t = Sorted-to-List⁻′ t EO.≤-refl

opaque

  -- A possibly slower but perhaps less complicated alternative to
  -- to-List⁻.

  @0 to-List⁻-slow : Tree⁻ → List A
  to-List⁻-slow leaf           = []
  to-List⁻-slow (node _ l x r) = to-List⁻-slow l ++ x ∷ to-List⁻-slow r

opaque
  unfolding to-List⁻ to-List⁻′ to-List⁻-slow

  -- The functions to-List⁻-slow and to-List⁻ return equal results.

  @0 to-List⁻-slow≡to-List⁻ :
    to-List⁻-slow t ≡ to-List⁻ t
  to-List⁻-slow≡to-List⁻ {t} =
    to-List⁻-slow t        ≡⟨ sym (++-right-identity _) ⟩
    to-List⁻-slow t ++ []  ≡⟨ lemma t ⟩∎
    to-List⁻′ t []         ∎
    where
    lemma : ∀ t → to-List⁻-slow t ++ xs ≡ to-List⁻′ t xs
    lemma      leaf           = refl _
    lemma {xs} (node _ l x r) =
      (to-List⁻-slow l ++ x ∷ to-List⁻-slow r) ++ xs  ≡⟨ sym (++-associative (to-List⁻-slow l) _ _) ⟩
      to-List⁻-slow l ++ (x ∷ to-List⁻-slow r ++ xs)  ≡⟨ cong ((to-List⁻-slow l ++_) ∘ (x ∷_)) (lemma r) ⟩
      to-List⁻-slow l ++ x ∷ to-List⁻′ r xs           ≡⟨ lemma l ⟩∎
      to-List⁻′ l (x ∷ to-List⁻′ r xs)                ∎

opaque
  unfolding to-List⁻-slow

  -- The function size⁻ can be expressed using length and to-List⁻-slow.

  @0 size⁻≡length∘to-List⁻-slow : size⁻ t ≡ length (to-List⁻-slow t)
  size⁻≡length∘to-List⁻-slow {t = leaf} =
    refl _
  size⁻≡length∘to-List⁻-slow {t = node _ l x r} =
    1 + size⁻ l + size⁻ r                                      ≡⟨ N.suc+≡+suc _ ⟩
    size⁻ l + (1 + size⁻ r)                                    ≡⟨ cong₂ _+_ size⁻≡length∘to-List⁻-slow (cong suc size⁻≡length∘to-List⁻-slow) ⟩
    length (to-List⁻-slow l) + (1 + length (to-List⁻-slow r))  ≡⟨ sym (length-++ (to-List⁻-slow l)) ⟩∎
    length (to-List⁻-slow l ++ x ∷ to-List⁻-slow r)            ∎

opaque

  -- The function size⁻ can be expressed using length and to-List⁻.

  @0 size⁻≡length∘to-List⁻ : size⁻ t ≡ length (to-List⁻ t)
  size⁻≡length∘to-List⁻ {t} =
    size⁻ t                   ≡⟨ size⁻≡length∘to-List⁻-slow ⟩
    length (to-List⁻-slow t)  ≡⟨ cong length to-List⁻-slow≡to-List⁻ ⟩∎
    length (to-List⁻ t)       ∎

------------------------------------------------------------------------
-- An equality test

opaque

  infix 4 _≟⁻_

  -- An equality test.
  --
  -- The test converts the trees to lists and compares the lists. A
  -- direct implementation could presumably be more efficient.

  _≟⁻_ : (t₁ t₂ : Tree⁻) → Dec-Erased (to-List⁻ t₁ ≡ to-List⁻ t₂)
  t₁ ≟⁻ t₂ =
    Decidable-erased-equality-List O._≟_ (to-List⁻ t₁) (to-List⁻ t₂)
