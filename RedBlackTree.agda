{-
  Verified Red-Black Trees
        Toon Nolten

  Based on Chris Okasaki's "Red-Black Trees in a Functional Setting"
  where he uses red-black trees to implement sets.

  Invariants
  ----------

  1. No red node has a red parent
  2. Every Path from the root to an empty node contains the same number of
     black nodes.
    (Empty nodes are considered black)
-}
module RedBlackTree where

open import Data.Bool using (Bool; true; false) renaming (T to So; not to ¬)
_⇒_ : ∀{ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
P ⇒ T = {{p : P}} → T
infixr 3 _⇒_

if_then_else_ : ∀{ℓ}{A : Set ℓ} b → (So b ⇒ A) → (So (¬ b) ⇒ A) → A
if true  then t else f = t
if false then t else f = f

open import Data.Nat hiding (_<_; _≟_; compare) renaming (_≤_ to _≤ℕ_)
open import Level hiding (suc)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Sum using (_⊎_) renaming (inj₁ to h+0; inj₂ to h+1)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)

module RBTree {a ℓ}(order : StrictTotalOrder a ℓ ℓ) where

  open module sto = StrictTotalOrder order
  A = StrictTotalOrder.Carrier order
  
  pattern LT = tri< _ _ _
  pattern EQ = tri≈ _ _ _
  pattern GT = tri> _ _ _
  _≤_ = compare

  
  data Color : Set where
    R B : Color
  
  _=ᶜ_ : Color → Color → Bool
  R =ᶜ R = true
  B =ᶜ B = true
  _ =ᶜ _ = false

  Height = ℕ

  data Tree : Color → Height → Set a where
    E : Tree B 0
    R : ∀{h} → Tree B h → A → Tree B h → Tree R h
    B : ∀{cl cr h} → Tree cl h → A → Tree cr h → Tree B (suc h)

  data IRTree : Height → Set a where
    IRl : ∀{h} → Tree R h → A → Tree B h → IRTree h
    IRr : ∀{h} → Tree B h → A → Tree R h → IRTree h

  data OutOfBalance : Height → Set a where
    _◂_◂_ : ∀{c h} → IRTree h → A → Tree c h → OutOfBalance h
    _▸_▸_ : ∀{c h} → Tree c h → A → IRTree h → OutOfBalance h

  data Treeish : Color → Height → Set a where
    RB : ∀{c h} → Tree c h → Treeish c h
    IR : ∀{h} → IRTree h → Treeish R h

  postulate
    -- Simple Set Operations
    set : Set
    empty : Set
    member : Set

  -- Insertion

  -- If the element fits in the tree the height will not increase after
  -- insertion.
  fit : ∀{c h} → A → Tree c h → Bool
  -- red root will be blackened h->h+1
  fit _ E = false
  fit a (R _ b _) with a ≤ b
  fit a (R _ _ _) | EQ = false -- true
  fit a (R E         _ _) | LT = false
  fit a (R (B l b r) _ _) | LT = false -- fit a (B l b r)
  fit a (R _ _ E        ) | GT = false
  fit a (R _ _ (B l b r)) | GT = false -- fit a (B l b r)
  -- black root may become red after cascading balance
  fit a (B _ b _) with a ≤ b
  fit a (B _ _ _) | EQ = true
  fit a (B (R l b r) _ _) | LT = fit a (R l b r)
  fit a (B _         _ _) | LT = true
  fit a (B _ _ (R l b r)) | GT = fit a (R l b r)
  fit a (B _ _ _        ) | GT = true

  balance : ∀{h} → OutOfBalance h → Tree R (suc h)
  balance (IRl (R a x b) y c ◂ z ◂ d) = R (B a x b) y (B c z d)
  balance (IRr a x (R b y c) ◂ z ◂ d) = R (B a x b) y (B c z d)
  balance (a ▸ x ▸ IRl (R b y c) z d) = R (B a x b) y (B c z d)
  balance (a ▸ x ▸ IRr b y (R c z d)) = R (B a x b) y (B c z d)

  blacken : ∀{h} → (t : Σ[ c ∈ Color ] Treeish c h) → Tree B h ⊎ Tree B (suc h)
  blacken (.B , RB E)         = h+0 E
  blacken (.R , RB (R l b r)) = h+1 (B l b r)
  blacken (.B , RB (B l b r)) = h+0 (B l b r)
  blacken (.R , IR (IRl l b r)) = h+1 (B l b r)
  blacken (.R , IR (IRr l b r)) = h+1 (B l b r)

  ins : ∀{c h} → (a : A) → (t : Tree c h)
        → Σ[ c' ∈ Color ] (if c =ᶜ B then (Tree c' h) else (Treeish c' h))
  ins a E = R , R E a E
  --
  ins a (R _ b _) with a ≤ b
  ins a (R l _ _) | LT with ins a l
  ins _ (R _ b r) | LT | R , t = R , IR (IRl t b r)
  ins _ (R _ b r) | LT | B , t = R , (RB (R t b r))
  ins _ (R l b r) | EQ = R , RB (R l b r)
  ins a (R _ _ r) | GT with ins a r
  ins _ (R l b _) | GT | R , t = R , (IR (IRr l b t))
  ins _ (R l b _) | GT | B , t = R , (RB (R l b t))
  --
  ins a (B _ b _) with a ≤ b
  ins a (B l _ _) | LT with ins a l
  ins _ (B {R} _ b r) | LT | c , RB t = B , B t b r
  ins _ (B {R} _ b r) | LT | .R , IR t = R , balance (t ◂ b ◂ r)
  ins _ (B {B} _ b r) | LT | c , t = B , B t b r
  ins _ (B l b r) | EQ = B , B l b r
  ins a (B _ _ r) | GT with ins a r
  ins _ (B {cr = R} l b _) | GT | c , RB t = B , B l b t
  ins _ (B {cr = R} l b _) | GT | .R , IR t = R , balance (l ▸ b ▸ t)
  ins _ (B {cr = B} l b _) | GT | c , t = B , B l b t

  insert : ∀{c h} → (a : A) → (t : Tree c h)
           → Tree B h ⊎ Tree B (suc h)
  insert {R} a t = blacken (ins a t)
  insert {B} a t with ins a t
  ... | c , t' = blacken (c , RB t')
