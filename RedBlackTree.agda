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

open import Data.Bool renaming (T to So; not to ¬)
open import Data.Nat hiding (_<_)

data Order : Set where
  LT EQ GT : Order

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Order

data Color : Set where
  R B : Color

tooRed : Color → Color → Bool
tooRed R R = true
tooRed _ _ = false

data Tree (A : Set) : Color → Set where
  E : Tree A B
  T : ∀{cl cr}(c : Color)
      → Tree A cl → {_ : So (¬ (tooRed c cl))}
      → A
      → Tree A cr → {_ : So (¬ (tooRed c cr))}
        → Tree A c

-- Simple Set Operations
set : ∀{c} → Set → Set
set {c} A = Tree A c

empty : ∀{A} → set A
empty = E

member : ∀{A c}⦃ ord : Ord A ⦄ → A → set {c} A → Bool
member x E = false
member ⦃ ord ⦄ x (T _ a y b) with Ord._<_ ord x y
... | LT = member x a
... | EQ = true
... | GT = member x b

-- Insertion
resultColor : ∀{A cl cr} → Color → set {cl} A → set {cr} A → Color
resultColor B (T R (T R _ _ _) _ _) _ = R
resultColor B (T R _ _ (T R _ _ _)) _ = R
resultColor B _ (T R (T R _ _ _) _ _) = R
resultColor B _ (T R _ _ (T R _ _ _)) = R
resultColor B _ _ = B
resultColor R _ _ = R

balance : ∀{A cl cr} → (c : Color) → (tl : set {cl} A) → A → (tr : set {cr} A)
            → set {resultColor c tl tr} A
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R (T B a₁ a₂ a₃) x (T R b y c)) z d = T R (T B (T B a₁ a₂ a₃) x b) y (T B c z d)
balance B (T B a₁ a₂ a₃) x (T R (T R b y c) z d) =
  T R (T B (T B a₁ a₂ a₃) x b) y (T B c z d)
balance B (T R (T B a₁₁ a₁₂ a₁₃) a₂ (T B a₃₁ a₃₂ a₃₃)) x (T R (T R b y c) z d) =
  T R (T B ? x b) y (T B c z d)b
balance B a x (T R b y (T R c z d)) =
  T R (T B a x b) y (T B c z d)
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
