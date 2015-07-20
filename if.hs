{-# LANGUAGE TypeFamilies, DataKinds, GADTs, KindSignatures #-}

data Tree :: Bool -> * -> * where
  E :: Tree False a
  T :: Tree False a -> a -> Tree False a -> Tree True a

type family If (cond :: Bool) thenn elsse :: *

type instance If True a b = a
type instance If False a b = b

type family And (a :: Bool) (b :: Bool) :: Bool
type instance And True True = True
type instance And False b = False
type instance And a False = False

f :: Tree h a -> If (And h h) Bool Integer
f E = 5
f (T _ _ _) = True

main :: IO ()
main = do print $ "f E:"
          print $ f E
          print $ "f (T E 3 E)"
          print $ f (T E 3 E)
