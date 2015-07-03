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
{-# LANGUAGE GADTs, DataKinds, TypeFamilies #-}
module RedBlackTree where

data Nat = Z | S Nat deriving (Show, Eq, Ord)

type Height = Nat

data Color = R | B deriving (Show, Eq, Ord)

data Tree :: Color -> Nat -> * -> * where
  ET :: Tree B Z a
  RT :: Tree B  h a -> a -> Tree B  h a -> Tree R h a
  BT :: Tree cl h a -> a -> Tree cr h a -> Tree B (S h) a

data IRTree :: Nat -> * -> * where
  IRl :: Tree R h a -> a -> Tree B h a -> IRTree h a
  IRr :: Tree B h a -> a -> Tree R h a -> IRTree h a

data OutOfBalance :: Nat -> * -> * where
  (:<:) :: IRTree h a -> a -> Tree c h a -> OutOfBalance h a
  (:>:) :: Tree c h a -> a -> IRTree h a -> OutOfBalance h a

data Treeish :: Color -> Nat -> * -> * where
  RB :: Tree c h a -> Treeish c h a
  IR :: IRTree h a -> Treeish R h a

--Insertion

-- If the element fits in the tree the height will not increase after
-- insertion.
fit :: Ord a => a -> Tree c h a -> Bool
-- red root will be blackened h->h+1
fit _ ET = False
fit _ (RT {}) = False
-- black root may become red after cascading balance
fit a (BT l b r)
  | a == b = True
  | a < b , RT {} <- l = fit a l
  | a < b = True
  | a > b , RT {} <- r = fit a r
  | a > b = True

balance :: OutOfBalance h a -> Tree R (S h) a
balance ((:<:) (IRl (RT a x b) y c) z d) = RT (BT a x b) y (BT c z d)
balance ((:<:) (IRr a x (RT b y c)) z d) = RT (BT a x b) y (BT c z d)
balance ((:>:) a x (IRl (RT b y c) z d)) = RT (BT a x b) y (BT c z d)
balance ((:>:) a x (IRr b y (RT c z d))) = RT (BT a x b) y (BT c z d)

blacken :: Treeish c h a -> Either (Tree B h a) (Tree B (S h) a)
blacken (RB ET) = Left ET
blacken (RB (RT l b r)) = Right (BT l b r)
blacken (RB (BT l b r)) = Left (BT l b r)
blacken (IR (IRl l b r)) = Right (BT l b r)
blacken (IR (IRr l b r)) = Right (BT l b r)

ins :: Ord a => a -> Tree c h a -> Treeish c' h a
ins a ET = RB (RT ET a ET)
--
ins a (RT l b r)
  | a < b = IR (IRl t b r)
    where RB t = ins a l

