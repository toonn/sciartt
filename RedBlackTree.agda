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
_⇒_ : Set → Set → Set
P ⇒ T = {{p : P}} → T
infixr 3 _⇒_

if_then_else_ : ∀{A} b → (So b ⇒ A) → (So (¬ b) ⇒ A) → A
if true  then t else f = t
if false then t else f = f

open import Data.Nat hiding (_≤_; _<_; _≟_; compare)
open import Level hiding (suc)
open import Relation.Binary hiding (_⇒_)

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

  postulate
    -- Simple Set Operations
    set : Set
    empty : Set
    member : Set

  -- Insertion

  -- If the element fits in the tree the height will not increase after
  -- insertion.
  fit : ∀{c h} → A → Tree c h → Bool
  fit _ E = false
  fit a (R _ b _) with a ≤ b
  fit a (R _ _ _) | EQ = true
  fit a (R E         _ _) | LT = false
  fit a (R (B l b r) _ _) | LT = fit a (B l b r)
  fit a (R _ _ E        ) | GT = false
  fit a (R _ _ (B l b r)) | GT = fit a (B l b r)
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

  insert : ∀{c h} → (a : A) → (t : Tree c h)
           → Tree B (if fit a t then h else suc h)
  insert a t = blacken (ins a t)
    where
      blacken : ∀{c h} → Tree c h → Tree B (if B =ᶜ c then h else suc h)
      blacken E         = E
      blacken (R l b r) = B l b r
      blacken (B l b r) = B l b r

      ins : ∀{c h}{c'} → (a : A) → (t : Tree c h)
            → Tree c' (if fit a t then h else suc h)
      ins a E = {!R E a E!}
      --
      ins a (R _ b _) with a ≤ b
      ins a (R l b r) | LT = {!balance R (ins a l) b r!}
      ins _ (R l b r) | EQ = {!R l b r!}
      ins a (R l b r) | GT = {!balance R l b (ins a r)!}
      --
      ins a (B _ b _) with a ≤ b
      ins a (B l b r) | LT = {!balance B (ins a l) b r!}
      ins _ (B l b r) | EQ = {!B l b r!}
      ins a (B l b r) | GT = {!balance B l b (ins a r)!}
