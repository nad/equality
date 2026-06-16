------------------------------------------------------------------------
-- Red-black trees
------------------------------------------------------------------------

-- The implementation is based on Okasaki's presentation in "Red-black
-- trees in a functional setting". The ordering invariant is handled
-- using more or less the approach described by McBride in "How to
-- Keep Your Neighbours in Order".

{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
open import Prelude as P
import Total-order.Erased

module Tree.Red-black
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

open import Equality.Decision-procedures eq
open import Erased.Level-1 eq
open import Function-universe eq as F hiding (id; _∘_)
open import H-level.Closure eq
import Total-order.Erased eq as TE

private
  open module O  = TE.Total-order O using (_<_; _>_)
  open module EO = TE.Total-order (extended O)
    using () renaming (_<_ to _<ᴱ_)

private variable
  @0 m n   : ℕ
  @0 x y   : A
  @0 lb ub : Extended _
  Tr       : Type _
  t        : Tr

------------------------------------------------------------------------
-- Trees with colours

-- Colours.

Colour : Type
Colour = Bool

pattern red   = false
pattern black = true

private variable
  @0 c pc : Colour

-- Trees with colours but no invariants.

data Tree⁻ : Type a where
  leaf : Tree⁻
  node : (c : Colour) (x : A) (l r : Tree⁻) → Tree⁻

pattern nodeᶜ c = node c _ _ _
pattern node!   = node _ _ _ _

private variable
  l r : Tree⁻

------------------------------------------------------------------------
-- Red-black trees

opaque

  -- The red invariant: red nodes do not have red parents.

  @0 Red-invariant : Colour → Colour → Type
  Red-invariant pc c =
    c ≡ red → pc ≡ red → ⊥

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
Red-black pc n lb ub (node c x l r) =
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

  -- The red invariant holds for black children.

  @0 black-child : Red-invariant pc black
  black-child black≡red _ = Bool.true≢false black≡red

opaque
  unfolding Red-invariant

  -- The red invariant holds for black parents.

  @0 black-parent : Red-invariant black c
  black-parent _ black≡red = Bool.true≢false black≡red

opaque
  unfolding Red-invariant

  -- The red invariant does not hold for two red nodes.

  @0 not-red-red : ¬ Red-invariant red red
  not-red-red inv = inv (refl _) (refl _)

opaque
  unfolding Red-invariant

  -- If the red invariant holds for pc and red, then it holds for pc
  -- and c.

  @0 red-child : ∀ {pc} → Red-invariant pc red → Red-invariant pc c
  red-child {pc = red}   inv = ⊥-elim (not-red-red inv)
  red-child {pc = black} _   = black-parent

opaque
  unfolding Red-invariant

  -- If the red invariant holds for rec and c, then it holds for pc
  -- and c.

  @0 red-parent : Red-invariant red c → Red-invariant pc c
  red-parent {c = red}   inv = ⊥-elim (not-red-red inv)
  red-parent {c = black} _   = black-child

------------------------------------------------------------------------
-- A lemma related to Black-invariant

opaque
  unfolding Black-invariant

  -- The black invariant is preserved (possibly for a different second
  -- number) if the root is coloured black.

  @0 black-black :
    Black-invariant c m n →
    ∃ (Black-invariant black m)
  black-black {c = red}   eq = _ , cong suc eq
  black-black {c = black} eq = _ , eq

------------------------------------------------------------------------
-- A lemma related to the bounds

opaque

  -- The lower bound is strictly below the upper bound.

  @0 lower-bound-<-upper-bound : Red-black pc n lb ub t → lb <ᴱ ub
  lower-bound-<-upper-bound {t = leaf} (leafʳᵇ lb<ub _) =
    lb<ub
  lower-bound-<-upper-bound {t = node! } (nodeʳᵇ l r _ _) =
    EO.<-trans (lower-bound-<-upper-bound l)
      (lower-bound-<-upper-bound r)

------------------------------------------------------------------------
-- Membership

-- Tree membership.

infix 4 _∈⁻_

_∈⁻_ : A → Tree⁻ → Type a
_ ∈⁻ leaf         = ⊥
x ∈⁻ node _ y l r = x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r

opaque

  -- If x is in a red-black tree, then x is strictly between any lower
  -- and upper bounds.

  @0 ∈⁻→<< :
    Red-black pc n lb ub t → x ∈⁻ t → lb <ᴱ [ x ] × [ x ] <ᴱ ub
  ∈⁻→<< {t = node! } (nodeʳᵇ l r _ _) (inj₁ x∈l) =
    let <x , x< = ∈⁻→<< l x∈l in
    <x , EO.<-trans x< (lower-bound-<-upper-bound r)
  ∈⁻→<< {t = node! } (nodeʳᵇ l r _ _) (inj₂ (inj₁ x≡y)) =
    EO.<-≤-trans (lower-bound-<-upper-bound l)
      (EO.≤-reflexive (cong [_] (sym x≡y))) ,
    EO.≤-<-trans (EO.≤-reflexive (cong [_] x≡y))
      (lower-bound-<-upper-bound r)
  ∈⁻→<< {t = node! } (nodeʳᵇ l r _ _) (inj₂ (inj₂ x∈r)) =
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
    let t = node c y l r in
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
    let t = node c y l r in
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
  ∈⁻-propositional {t = node! } (nodeʳᵇ l r _ _) =
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
  member?⁻ x (node _ y l r) _ with O.compare x y
  … | eqᵀ x≡y = yes [ inj₂ (inj₁ x≡y) ]
  member?⁻ x (node _ _ l _) t@(nodeʳᵇ lʳᵇ _ _ _) | ltᵀ x<y =
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

  balanceˡ : Colour → A → Tree⁻ → Tree⁻ → Tree⁻
  balanceˡ red x l r =
    node red x l r
  balanceˡ black x₆ (node red x₄ (node red x₂ t₁ t₃) t₅) t₇ =
    node red x₄ (node black x₂ t₁ t₃) (node black x₆ t₅ t₇)
  balanceˡ black x₆ (node red x₂ t₁ (node red x₄ t₃ t₅)) t₇ =
    node red x₄ (node black x₂ t₁ t₃) (node black x₆ t₅ t₇)
  balanceˡ black x l r =
    node black x l r

opaque

  -- A balancing function.

  balanceʳ : Colour → A → Tree⁻ → Tree⁻ → Tree⁻
  balanceʳ red x l r =
    node red x l r
  balanceʳ black x₂ t₁ (node red x₆ (node red x₄ t₃ t₅) t₇) =
    node red x₄ (node black x₂ t₁ t₃) (node black x₆ t₅ t₇)
  balanceʳ black x₂ t₁ (node red x₄ t₃ (node red x₆ t₅ t₇)) =
    node red x₄ (node black x₂ t₁ t₃) (node black x₆ t₅ t₇)
  balanceʳ black x l r =
    node black x l r

opaque

  -- Inserts an element into the tree.

  insert⁻′ : A → Tree⁻ → Tree⁻
  insert⁻′ x leaf             = node red x leaf leaf
  insert⁻′ x t@(node c y l r) with O.compare x y
  … | eqᵀ _   = t
  … | ltᵀ x<y = balanceˡ c y (insert⁻′ x l) r
  … | gtᵀ x>y = balanceʳ c y l (insert⁻′ x r)

opaque

  -- If the tree is non-empty, then the root is coloured black.

  colour-root-black : Tree⁻ → Tree⁻
  colour-root-black leaf           = leaf
  colour-root-black (node _ x l r) = node black x l r

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

-- In an "almost red-black tree" the red invariant might be broken for
-- the top-most layer.

@0 Almost-red-black :
  Colour → ℕ → (_ _ : Extended A) → Tree⁻ → Type (a ⊔ o)
Almost-red-black _  n lb ub leaf           = lb <ᴱ ub × n ≡ 0
Almost-red-black pc n lb ub (node c x l r) =
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
  Red-black→Red-black-black {t = node! } (nodeʳᵇ l r _ binv) =
    nodeʳᵇ l r black-parent binv

opaque

  -- A tree that is well-formed for a red parent is well-formed with a
  -- parent of any colour.

  @0 Red-black-red→Red-black :
    Red-black red n lb ub t →
    Red-black pc n lb ub t
  Red-black-red→Red-black {t = leaf} (leafʳᵇ lb<ub n≡0) =
    leafʳᵇ lb<ub n≡0
  Red-black-red→Red-black {t = node! } (nodeʳᵇ l r rinv binv) =
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
  Red-black-black→Red-black {t = node! } rinv (nodeʳᵇ l r _ binv) =
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
    Almost-red-black pc n lb ub (balanceˡ c x l r)
  balanceˡʳᵇ {c = red} l r rinv binv =
    nodeᵃʳᵇ
      (Red-black-black→Red-black rinv
         (Almost-red-black-red→Red-black-black l))
      (Red-black-red→Red-black r) binv
  balanceˡʳᵇ
    {c = black} {l = node red _ (nodeᶜ red) _}
    (nodeᵃʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) t₅ binv₂) t₇ rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁)
         (Red-black→Red-black-black t₃) rinv₃
         (cong suc (trans binv₂ binv₁)))
      (nodeʳᵇ t₅ (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡʳᵇ
    {c = black} {l = node red _ leaf (nodeᶜ red)}
    (nodeᵃʳᵇ t₁ (nodeʳᵇ t₃ t₅ _ binv₁) binv₂) t₇ rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (Red-black→Red-black-black (cast (sym binv₁) t₃)) rinv₃
         (cong suc binv₂))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (cast binv₂ t₇) rinv₃ (cong suc binv₂))
      binv₃
  balanceˡʳᵇ
    {c = black} {l = node red _ (nodeᶜ black) (nodeᶜ red)}
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
    {c = black} {l = node red _ leaf leaf}
    (nodeᵃʳᵇ (leafʳᵇ lb< n≡0) (leafʳᵇ x₁<x₂ _) binv₁) t₃ _ binv₂ =
    nodeᵃʳᵇ
      (nodeʳᵇ (leafʳᵇ lb< n≡0) (leafʳᵇ x₁<x₂ n≡0) black-parent binv₁) t₃
      binv₂
  balanceˡʳᵇ
    {c = black} {l = node red _ leaf (nodeᶜ black)}
    (nodeᵃʳᵇ (leafʳᵇ lb< n≡0) (nodeʳᵇ t₂ t₄ _ binv₁) binv₂) t₆ _ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (leafʳᵇ lb< n≡0) (nodeʳᵇ t₂ t₄ black-child binv₁)
         black-parent binv₂)
      t₆ binv₃
  balanceˡʳᵇ
    {c = black} {l = node red _ (nodeᶜ black) leaf}
    (nodeᵃʳᵇ (nodeʳᵇ t₁ t₃ _ binv₁) (leafʳᵇ x₄<x₅ n≡0) binv₂) t₆ _
    binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (nodeʳᵇ t₁ t₃ black-child binv₁) (leafʳᵇ x₄<x₅ n≡0)
         black-parent binv₂)
      t₆ binv₃
  balanceˡʳᵇ
    {c = black} {l = node red _ (nodeᶜ black) (nodeᶜ black)}
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
    Almost-red-black pc n lb ub (balanceʳ c x l r)
  balanceʳʳᵇ {c = red} l r rinv binv =
    nodeᵃʳᵇ (Red-black-red→Red-black l)
      (Red-black-black→Red-black rinv
         (Almost-red-black-red→Red-black-black r))
      binv
  balanceʳʳᵇ
    {c = black} {r = node red _ (nodeᶜ red) _}
    t₁ (nodeᵃʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) t₇ binv₂) rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ (Red-black→Red-black-black t₁)
         (Red-black→Red-black-black (cast (sym (trans binv₂ binv₁)) t₃))
         rinv₃ (refl _))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅)) t₇ rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red _ leaf (nodeᶜ red)}
    t₁ (nodeᵃʳᵇ t₃ (nodeʳᵇ t₅ t₇ _ binv₁) binv₂) rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (cast {pc = black} {t = leaf} (sym binv₂) t₃) rinv₃
         (refl _))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (Red-black→Red-black-black (cast (sym binv₁) t₇)) rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red _ (nodeᶜ black) (nodeᶜ red)}
    t₁ (nodeᵃʳᵇ t₃ (nodeʳᵇ t₅ t₇ _ binv₁) binv₂) rinv₃ binv₃ =
    nodeᵃʳᵇ
      (nodeʳᵇ t₁ (cast {t = node! } (sym binv₂) t₃) rinv₃ (refl _))
      (nodeʳᵇ (Red-black→Red-black-black (cast (sym binv₁) t₅))
         (Red-black→Red-black-black (cast (sym binv₁) t₇)) rinv₃
         (cong suc binv₂))
      binv₃
  balanceʳʳᵇ {c = black} {r = leaf} t (leafʳᵇ lb< n≡0) _ binv =
    nodeᵃʳᵇ t (leafʳᵇ lb< n≡0) binv
  balanceʳʳᵇ
    {c = black} {r = node red _ leaf leaf}
    t₁ (nodeᵃʳᵇ (leafʳᵇ x₂<x₃ n≡0) (leafʳᵇ <ub _) binv₁) _ binv₂ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (leafʳᵇ x₂<x₃ n≡0) (leafʳᵇ <ub n≡0) black-parent binv₁)
      binv₂
  balanceʳʳᵇ
    {c = black} {r = node red _ leaf (nodeᶜ black)}
    t₁ (nodeᵃʳᵇ (leafʳᵇ x₂<x₃ n≡0) (nodeʳᵇ t₄ t₆ _ binv₁) binv₂) _
    binv₃ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (leafʳᵇ x₂<x₃ n≡0) (nodeʳᵇ t₄ t₆ black-child binv₁)
         black-parent binv₂)
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red _ (nodeᶜ black) leaf}
    t₁ (nodeᵃʳᵇ (nodeʳᵇ t₃ t₅ _ binv₁) (leafʳᵇ <ub n≡0) binv₂) _ binv₃ =
    nodeᵃʳᵇ t₁
      (nodeʳᵇ (nodeʳᵇ t₃ t₅ black-child binv₁) (leafʳᵇ <ub n≡0)
         black-parent binv₂)
      binv₃
  balanceʳʳᵇ
    {c = black} {r = node red _ (nodeᶜ black) (nodeᶜ black)}
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

  -- The function insert takes red-black trees to almost red-black
  -- trees, given certain assumptions.

  @0 insert⁻′ʳᵇ :
    Red-black pc n lb ub t →
    lb <ᴱ [ x ] → [ x ] <ᴱ ub →
    Almost-red-black pc n lb ub (insert⁻′ x t)
  insert⁻′ʳᵇ {t = leaf} (leafʳᵇ _ n≡0) lb< <ub =
    nodeᵃʳᵇ (leafʳᵇ lb< (refl _)) (leafʳᵇ <ub (refl _)) n≡0
  insert⁻′ʳᵇ
    {t = t@(node _ y _ _)} {x} tʳᵇ@(nodeʳᵇ l r rinv binv) lb< <ub
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
  colour-root-blackʳᵇ {t = node _ x l r} (nodeᵃʳᵇ lʳᵇ rʳᵇ binv) =
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
    x ∈⁻ balanceˡ c y l r ⇔
    x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r
  ∈⁻-balanceˡ {c = red} =
    F.id
  ∈⁻-balanceˡ
    {x} {c = black} {y = x₆}
    {l = node red x₄ (node red x₂ t₁ t₃) t₅} {r = t₇} =
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
    {x} {c = black} {y = x₆}
    {l = node red x₂ t₁@(nodeᶜ black) (node red x₄ t₃ t₅)} {r = t₇} =
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
    {x} {c = black} {y = x₆}
    {l = node red x₂ t₁@leaf (node red x₄ t₃ t₅)} {r = t₇} =
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
  ∈⁻-balanceˡ {c = black} {l = node red _ leaf leaf} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red _ leaf (nodeᶜ black)} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red _ (nodeᶜ black) leaf} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = node red _ (nodeᶜ black) (nodeᶜ black)} =
    F.id
  ∈⁻-balanceˡ {c = black} {l = nodeᶜ black} =
    F.id

opaque
  unfolding balanceʳ

  -- A membership lemma for balanceʳ.

  @0 ∈⁻-balanceʳ :
    x ∈⁻ balanceʳ c y l r ⇔
    x ∈⁻ l ⊎ x ≡ y ⊎ x ∈⁻ r
  ∈⁻-balanceʳ {c = red} =
    F.id
  ∈⁻-balanceʳ
    {x} {c = black} {y = x₂} {l = t₁}
    {r = node red x₆ (node red x₄ t₃ t₅) t₇} =
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
    {x} {c = black} {y = x₂} {l = t₁}
    {r = node red x₄ t₃@(nodeᶜ black) (node red x₆ t₅ t₇)} =
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
    {x} {c = black} {y = x₂} {l = t₁}
    {r = node red x₄ t₃@leaf (node red x₆ t₅ t₇)} =
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
  ∈⁻-balanceʳ {c = black} {r = node red _ leaf leaf} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red _ leaf (nodeᶜ black)} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red _ (nodeᶜ black) leaf} =
    F.id
  ∈⁻-balanceʳ {c = black} {r = node red _ (nodeᶜ black) (nodeᶜ black)} =
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
  ∈⁻-insert⁻′ {y} {x} {t = node c z l r}
    with O.compare x z
  … | eqᵀ x≡z =
    y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r          ↝⟨ record
                                          { to   = inj₂
                                          ; from = P.[ inj₂ ∘ inj₁ ∘ flip trans x≡z , id ]
                                          } ⟩□
    y ≡ x ⊎ y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r  □
  … | ltᵀ _ =
    y ∈⁻ balanceˡ c z (insert⁻′ x l) r  ↝⟨ ∈⁻-balanceˡ ⟩
    y ∈⁻ insert⁻′ x l ⊎ y ≡ z ⊎ y ∈⁻ r  ↝⟨ ∈⁻-insert⁻′ ⊎-cong F.id ⟩
    (y ≡ x ⊎ y ∈⁻ l) ⊎ y ≡ z ⊎ y ∈⁻ r   ↔⟨ inverse ⊎-assoc ⟩□
    y ≡ x ⊎ y ∈⁻ l ⊎ y ≡ z ⊎ y ∈⁻ r     □
  … | gtᵀ _ =
    y ∈⁻ balanceʳ c z l (insert⁻′ x r)  ↝⟨ ∈⁻-balanceʳ ⟩
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
  ∈⁻-colour-root-black {t = node! } = F.id

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
-- Red-black trees with integrated invariants

-- Red-black trees.

record Tree : Type (a ⊔ o) where
  no-eta-equality
  field
    tree              : Tree⁻
    @0 {black-height} : ℕ
    @0 red-black      : Red-black black black-height min max tree

opaque

  infix 4 _∈_

  -- A membership relation.

  _∈_ : A → Tree → Type a
  x ∈ t = x ∈⁻ Tree.tree t

opaque
  unfolding _∈_

  -- Tree membership is propositional.

  @0 ∈-propositional : Is-proposition (x ∈ t)
  ∈-propositional {t} = ∈⁻-propositional (Tree.red-black t)

opaque
  unfolding _∈_

  -- Does the element exist in the tree?

  member? : (x : A) (t : Tree) → Dec-Erased (x ∈ t)
  member? x t = member?⁻ x (Tree.tree t) (Tree.red-black t)

opaque

  -- An empty tree.

  empty : Tree
  empty = record
    { tree      = empty⁻
    ; red-black = empty⁻ʳᵇ
    }

opaque
  unfolding _∈_ empty

  -- The empty tree is empty.

  @0 ∉empty : ¬ x ∈ empty
  ∉empty = ∉⁻empty⁻

opaque

  -- Inserts an element into the tree.

  insert : A → Tree → Tree
  insert x t = record
    { tree      = insert⁻ x (Tree.tree t)
    ; red-black = insert⁻ʳᵇ (Tree.red-black t) min-[] []-max .proj₂
    }

opaque
  unfolding _∈_ insert

  -- The value y is in insert x t if and only if y is x or y is in t.

  @0 ∈-insert :
    y ∈ insert x t ⇔ y ≡ x ⊎ y ∈ t
  ∈-insert = ∈⁻-insert⁻
