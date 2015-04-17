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

open import Data.Bool hiding (T)

data Order : Set where
  LT EQ GT : Order

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Order

data Color : Set where
  R B : Color

data Tree (A : Set) : Set where
  E : Tree A
  T : Color → Tree A → A → Tree A → Tree A

-- Simple Set Operations
set : Set → Set
set A = Tree A

empty : ∀{A} → set A
empty = E

member : ∀{A}⦃ ord : Ord A ⦄ → A → set A → Bool
member x E = false
member ⦃ ord ⦄ x (T _ a y b) with Ord._<_ ord x y
... | LT = member x a
... | EQ = true
... | GT = member x b

-- Insertion
balance : ∀{A} → Color → set A → A → set A → set A
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance B a x b = T B a x b
balance R a x b = T R a x b

insert : ∀{A}⦃ ord : Ord A ⦄ → A → set A → set A
insert {A} ⦃ ord ⦄ x s = blacken (ins s)
  where
    ins : set A → set A
    ins E = T R E x E
    ins (T color a y b) with Ord._<_ ord x y
    ... | LT = balance color (ins a) y b
    ... | EQ = T color a y b
    ... | GT = balance color a y (ins b)
    
    blacken : set A → set A
    blacken E = E
    blacken (T _ a y b) = T B a y b
