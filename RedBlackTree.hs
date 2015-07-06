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

-- Surprisingly difficult to find the right formulation
-- (ins in a pattern guard)
ins :: Ord a => a -> Tree c h a -> Either (Treeish R h a) (Treeish B h a)
ins a ET = Left $ RB (RT ET a ET)
--
ins a (RT l b r)
  | a < b , Left (RB t) <- ins a l = Left $ IR (IRl t b r)
  | a < b , Right (RB t) <- ins a l = Left $ RB (RT t b r)
  | a == b = Left $ RB (RT l b r)
  | a > b , Left (RB t) <- ins a r = Left $ IR (IRr l b t)
  | a > b , Right (RB t) <- ins a r = Left $ RB (RT l b t)
--
ins a (BT l b r)
  | a < b , Left (RB t) <- ins a l = Right $ RB (BT t b r)
  | a < b , Left (IR t) <- ins a l = Left $ RB (balance ((:<:) t b r))
  | a < b , Right (RB t) <- ins a l = Right $ RB (BT t b r)
  | a == b = Right $ RB (BT l b r)
  | a > b , Left (RB t) <- ins a r = Right $ RB (BT l b t)
  | a > b , Left (IR t) <- ins a r = Left $ RB (balance ((:>:) l b t))
  | a > b , Right (RB t) <- ins a r = Right $ RB (BT l b t)

insert :: Ord a => a -> Tree c h a -> Either (Tree B h a) (Tree B (S h) a)
insert a t
  | Left t' <- ins a t = blacken t'
  | Right t' <- ins a t = blacken t'


-- Simple Set operations
type Set c h a = Tree c h a

empty :: Set B Z a
empty = ET

member :: Ord a => a -> Set c h a -> Bool
member _ ET = False
member a (RT l b r)
  | a < b = member a l
  | a == b = True
  | a > b = member a r
member a (BT l b r)
  | a < b = member a l
  | a == b = True
  | a > b = member a r
