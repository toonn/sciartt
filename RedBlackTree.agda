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

open import Data.Bool hiding (if_then_else_) renaming (T to So; not to ¬)
_⇒_ : Set → Set → Set
P ⇒ T = {{p : P}} → T
infixr 3 _⇒_

if_then_else_ : ∀{A} b → (So b ⇒ A) → (So (¬ b) ⇒ A) → A
if true  then t else f = t
if false then t else f = f

open import Data.Nat hiding (_<_)

data Order : Set where
  LT EQ GT : Order

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Order


data Color : Set where
  R B : Color

Height = ℕ

data Type : Set where
  RB IR : Type

cType : Color → Color → Type
cType B B = RB
cType _ _ = IR

data Tree (A : Set) : Color → Height → Type → Set where
  E : Tree A B 0 RB
  R : ∀{cl cr h} → Tree A cl h RB → A → Tree A cr h RB
        → Tree A R h (cType cl cr)
  B : ∀{cl cr h} → Tree A cl h RB → A → Tree A cr h RB
        → Tree A B (suc h) RB
  
-- Simple Set Operations
set : ∀{c h ty} → Set → Set
set {c}{h}{ty} A = Tree A c h ty

empty : ∀{A} → set A
empty = E

member : ∀{A c h ty}{{ord : Ord A}} → A → set {c}{h}{ty} A → Bool
member x E = false
member {{ord}} x (R a y b) with Ord._<_ ord x y
... | LT = member x a
... | EQ = true
... | GT = member x b
member {{ord}} x (B a y b) with Ord._<_ ord x y
... | LT = member x a
... | EQ = true
... | GT = member x b

-- Insertion
-- balance has lots of problems with dependent pattern matching
-- No separate balance because 'd need infinitely deep pattern for R

insert : ∀{A c h h'}{{ord : Ord A}} → A → set {c}{h}{RB} A → set {B}{h'}{RB} A
insert {A} {{ord}} x s = blacken (ins s)
  where
    ins : ∀{c c' h h' ty'} set {c}{h}{RB} A → set {c'}{h'}{ty'} A
    ins t = {!!}
    --ins (R a y b) with Ord._<_ ord x y
    --... | _ = ?
    --ins (B a y b) with Ord._<_ ord x y
    --... | _ = ?
    
    blacken : ∀{c h ty} set {c}{h}{ty} A → set {B}{h}{RB} A
    blacken t = {!!}
    -- blacken (R a y b) = B a y b
    -- blacken (B a y b) = B a y b
