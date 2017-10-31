{-# language DataKinds #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
module Simplicity where

import Prelude (Either(..), fst, snd)

data Ty
  = UnitTy
  | Sum Ty Ty
  | Prod Ty Ty

type family TySem (ty :: Ty)

type instance TySem 'UnitTy = ()
type instance TySem ('Sum a b) = Either (TySem a) (TySem b)
type instance TySem ('Prod a b) = (TySem a, TySem b)

data Term :: Ty -> Ty -> * where
  Iden :: Term a a
  Comp :: Term a b -> Term b c -> Term a c
  Unit :: Term a 'UnitTy
  Injl :: Term a b -> Term a ('Sum b c)
  Injr :: Term a c -> Term a ('Sum b c)
  Case :: Term ('Prod a c) d -> Term ('Prod b c) d -> Term ('Prod ('Sum a b) c) d
  Pair :: Term a b -> Term a c -> Term a ('Prod b c)
  Take :: Term a c -> Term ('Prod a b) c
  Drop :: Term b c -> Term ('Prod a b) c

eval :: Term a b -> TySem a -> TySem b
eval = \case
  Iden     -> \a -> a
  Comp s t -> \a -> eval t (eval s a)
  Unit     -> \_ -> ()
  Injl t   -> \a -> Left (eval t a)
  Injr t   -> \a -> Right (eval t a)
  Case s t -> \p -> let (ab, c) = p in case ab of
    Left a  -> eval s (a, c)
    Right b -> eval t (b, c)
  Pair s t -> \a -> (eval s a, eval t a)
  Take t   -> \ab -> eval t (fst ab)
  Drop t   -> \ab -> eval t (snd ab)

-- examples

twoTy :: Ty
twoTy = Sum UnitTy UnitTy

not :: Term ('Sum 'UnitTy 'UnitTy) ('Sum 'UnitTy 'UnitTy)
not = Comp (Pair Iden Unit) (Case (Injr Unit) (Injl Unit))

halfAdder = Case (Drop (Pair (Injl Unit) Iden))
                 (Drop (Pair Iden not))
