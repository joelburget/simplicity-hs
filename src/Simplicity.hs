{-# language DataKinds #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language StandaloneDeriving #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

module Simplicity where

-- import Prelude (Either(..), Show(..), String, Int, IO, fst, snd, flip, (==), putStrLn, (*))
import Prelude hiding (not)
-- import CCCs hiding (eval, fst, snd, ($))
-- import Control.Category
import ConCat.Category


data Ty
  = UnitTy
  | Sum Ty Ty
  | Prod Ty Ty
  deriving Show

type family TySem (ty :: Ty)

type instance TySem 'UnitTy = ()
type instance TySem ('Sum a b) = Either (TySem a) (TySem b)
type instance TySem ('Prod a b) = (TySem a, TySem b)

data Term :: * -> * -> * where
  Iden ::                                   Term a a
  Comp :: Term a b      -> Term b c      -> Term a c
  Unit ::                                   Term a ()
  Injl ::                  Term a b      -> Term a (Either b c)
  Injr ::                  Term a c      -> Term a (Either b c)
  Case :: Term (a, c) d -> Term (b, c) d -> Term (Either a b, c) d
  Pair :: Term a b      -> Term a c      -> Term a (b, c)
  Take ::                  Term a c      -> Term (a, b) c
  Drop ::                  Term b c      -> Term (a, b) c

deriving instance Show (Term a b)

instance Category Term where
  id  = Iden
  (.) = flip Comp

instance ProductCat Term where
  exl     = Take Iden
  exr     = Drop Iden
  (&&&)   = Pair
  f *** g = Pair (Take f) (Drop g)

instance TerminalCat Term where
  it = Unit

instance CoproductCat Term where
  inl = Injl Iden
  inr = Injr Iden

  -- (|||) :: (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)
  --       :: Term c a -> Term d a -> Term (Either c d) a
  f ||| g = undefined -- this may be trouble

instance DistribCat Term where
  distl = Comp swapP (Case (Injl swapP) (Injr swapP))
  distr = Case (Injl Iden) (Injr Iden)

eval :: Term a b -> a -> b
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

type BitTy = 'Sum 'UnitTy 'UnitTy

not :: Term (TySem BitTy) (TySem BitTy)
not = Comp (Pair Iden Unit) (Case (Injr Unit) (Injl Unit))

false :: TySem BitTy
false = Left ()

true :: TySem BitTy
true = Right ()

-- Though the input and output types look the same, this is better thought of
-- as `Bit x Bit -> Bit^2`. In other words, we take two bits and add them to
-- get a half-nibble.
halfAdder :: Term (TySem ('Prod BitTy BitTy)) (TySem ('Prod BitTy BitTy))
halfAdder = Case (Drop (Pair (Injl Unit) Iden))
                 (Drop (Pair Iden not))

type Adder nbits = Term
  (TySem ('Prod ('Prod nbits nbits) BitTy))
  (TySem ('Prod BitTy nbits))

fullAdder :: Adder BitTy
fullAdder = Comp
  (Pair (Take halfAdder) (Drop Iden))
  (Comp
    (Pair
      (Take (Take Iden))
      (Comp
        (Pair (Take (Drop Iden)) (Drop Iden))
        halfAdder))
    (Pair
      (Case (Injr Unit) (Drop (Take Iden)))
      (Drop (Drop Iden))))

fullAddEx :: TySem ('Prod BitTy BitTy)
fullAddEx = eval fullAdder ((false, false), false)

-- doubleAdder :: forall nbits. Adder nbits -> Adder ('Prod nbits nbits)
doubleAdder nbitadder = Comp
  (Pair
    (Take (Pair (Take (Take Iden))
                      (Drop (Take Iden))))
    (Comp (Pair (Take (Pair (Take (Drop Iden))
                            (Drop (Drop Iden))))
                (Drop Iden))
          nbitadder))
  (Comp (Pair (Drop (Drop Iden))
              (Comp (Pair (Take Iden)
                          (Drop (Take Iden)))
                    nbitadder))
        (Pair (Drop (Take Iden))
              (Pair (Drop (Drop Iden)) (Take Iden))))
