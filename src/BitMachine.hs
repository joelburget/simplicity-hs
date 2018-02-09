{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module BitMachine where

import Prelude hiding (read, seq, succ)
import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Monoid (First)
import Data.Semigroup ((<>))
import Data.Vector (Vector)
import qualified Data.Vector as V
import Simplicity

newtype Bit = Bit Bool
  deriving (Eq, Show)

tt, ff :: Bit
tt = Bit True
ff = Bit False

-- TODO: maybe do this in a parametric / traversable way
data ErasedTerm
  = ErIden
  | ErComp ErasedTerm ErasedTerm
  | ErUnit
  | ErInjl ErasedTerm
  | ErInjr ErasedTerm
  | ErCase ErasedTerm ErasedTerm
  | ErPair ErasedTerm ErasedTerm
  | ErTake ErasedTerm
  | ErDrop ErasedTerm
  deriving Show

erase :: Term a b -> ErasedTerm
erase = \case
  Iden     -> ErIden
  Comp s t -> ErComp (erase s) (erase t)
  Unit     -> ErUnit
  Injl t   -> ErInjl (erase t)
  Injr t   -> ErInjr (erase t)
  Case s t -> ErCase (erase s) (erase t)
  Pair s t -> ErPair (erase s) (erase t)
  Take t   -> ErTake (erase t)
  Drop t   -> ErDrop (erase t)

erase' :: ElabTerm Ty -> ErasedTerm
erase' = \case
  EIden _     -> ErIden
  EComp s t _ -> ErComp (erase' s) (erase' t)
  EUnit _     -> ErUnit
  EInjl t _   -> ErInjl (erase' t)
  EInjr t _   -> ErInjr (erase' t)
  ECase s t _ -> ErCase (erase' s) (erase' t)
  EPair s t _ -> ErPair (erase' s) (erase' t)
  ETake t _   -> ErTake (erase' t)
  EDrop t _   -> ErDrop (erase' t)

data PartialTy
  = UnitP
  | Unknown
  | SumP PartialTy PartialTy
  | ProdP PartialTy PartialTy
  deriving Show

data Seq ty = Seq ty ty
  deriving Show

data ElabTerm ty where
  EIden ::                               Seq ty -> ElabTerm ty
  EComp :: ElabTerm ty -> ElabTerm ty -> Seq ty -> ElabTerm ty
  EUnit ::                               Seq ty -> ElabTerm ty
  EInjl ::                ElabTerm ty -> Seq ty -> ElabTerm ty
  EInjr ::                ElabTerm ty -> Seq ty -> ElabTerm ty
  ECase :: ElabTerm ty -> ElabTerm ty -> Seq ty -> ElabTerm ty
  EPair :: ElabTerm ty -> ElabTerm ty -> Seq ty -> ElabTerm ty
  ETake ::                ElabTerm ty -> Seq ty -> ElabTerm ty
  EDrop ::                ElabTerm ty -> Seq ty -> ElabTerm ty

deriving instance Show ty => Show (ElabTerm ty)

justTy :: ElabTerm ty -> (Seq ty)
justTy = \case
  EIden ty     -> ty
  EComp _ _ ty -> ty
  EUnit ty     -> ty
  EInjl _ ty   -> ty
  EInjr _ ty   -> ty
  ECase _ _ ty -> ty
  EPair _ _ ty -> ty
  ETake _ ty   -> ty
  EDrop _ ty   -> ty

unPartial :: PartialTy -> Maybe Ty
unPartial UnitP = Just UnitTy
-- replace any remaining type variables with the unit type
unPartial Unknown = Just UnitTy
unPartial (SumP a b) = Sum <$> unPartial a <*> unPartial b
unPartial (ProdP a b) = Prod <$> unPartial a <*> unPartial b

unPartialSeq :: Seq PartialTy -> Maybe (Seq Ty)
unPartialSeq (Seq t1 t2) = Seq <$> unPartial t1 <*> unPartial t2

unPartialTm :: ElabTerm PartialTy -> Maybe (ElabTerm Ty)
unPartialTm = \case
  EIden s       -> EIden <$> unPartialSeq s
  EComp t1 t2 s -> EComp <$> unPartialTm t1 <*> unPartialTm t2 <*> unPartialSeq s
  EUnit s       -> EUnit <$> unPartialSeq s
  EInjl t s     -> EInjl <$> unPartialTm t  <*> unPartialSeq s
  EInjr t s     -> EInjr <$> unPartialTm t  <*> unPartialSeq s
  ECase t1 t2 s -> ECase <$> unPartialTm t1 <*> unPartialTm t2 <*> unPartialSeq s
  EPair t1 t2 s -> EPair <$> unPartialTm t1 <*> unPartialTm t2 <*> unPartialSeq s
  ETake t s     -> ETake <$> unPartialTm t  <*> unPartialSeq s
  EDrop t s     -> EDrop <$> unPartialTm t  <*> unPartialSeq s

unify :: PartialTy -> PartialTy -> Maybe PartialTy
unify UnitP UnitP = Just UnitP
unify Unknown a = Just a
unify a Unknown = Just a
unify (SumP l1 r1) (SumP l2 r2) = SumP <$> unify l1 l2 <*> unify r1 r2
unify (ProdP l1 r1) (ProdP l2 r2) = ProdP <$> unify l1 l2 <*> unify r1 r2
unify _ _ = Nothing

unify' :: PartialTy -> Ty -> Maybe ()
unify' UnitP UnitTy = Just ()
unify' (SumP l1 r1) (Sum l2 r2) = unify' l1 l2 >> unify' r1 r2
unify' (ProdP l1 r1) (Prod l2 r2) = unify' l1 l2 >> unify' r1 r2
unify' Unknown _ = Just ()
unify' _ _ = Nothing

-- unifyWhole :: PartialTy -> PartialTy -> Maybe Ty
-- unifyWhole a b = unPartial =<< unify a b

getAnteSucc :: ElabTerm t -> Seq t
getAnte :: ElabTerm t -> t
getSucc :: ElabTerm t -> t
getAnteSucc = \case
  EIden     seq -> seq
  EComp _ _ seq -> seq
  EUnit     seq -> seq
  EInjl _   seq -> seq
  EInjr _   seq -> seq
  ECase _ _ seq -> seq
  EPair _ _ seq -> seq
  ETake _   seq -> seq
  EDrop _   seq -> seq
getAnte t = case getAnteSucc t of Seq ante _ -> ante
getSucc t = case getAnteSucc t of Seq _ succ -> succ

expand :: Term a b -> ElabTerm PartialTy
expand = \case
  Iden     -> EIden su
  Comp s t -> EComp (expand s) (expand t) su
  Unit     -> EUnit su
  Injl   t -> EInjl (expand t) su
  Injr   t -> EInjr (expand t) su
  Case s t -> ECase (expand s) (expand t) su
  Pair s t -> EPair (expand s) (expand t) su
  Take   t -> ETake (expand t) su
  Drop   t -> EDrop (expand t) su
  where su = Seq Unknown Unknown

elaborate :: Term a b -> Maybe (ElabTerm Ty)
elaborate = infer . expand

infer :: ElabTerm PartialTy -> Maybe (ElabTerm Ty)
infer = infer' >=> unPartialTm

infer' :: ElabTerm PartialTy -> Maybe (ElabTerm PartialTy)
infer' = \case
  EIden (Seq a1 a2) -> do
    a <- unify a1 a2
    pure $ EIden (Seq a a)
  EComp s t (Seq a c) -> do
    s'  <- infer' s
    t'  <- infer' t
    let (Seq a' b1) = getAnteSucc s'
    let (Seq b2 c') = getAnteSucc t'
    a'' <- unify a a'
    _   <- unify b1 b2
    c'' <- unify c c'
    pure $ EComp s' t' (Seq a'' c'')
  EUnit (Seq ante succ) -> do
    _ <- unify succ UnitP
    pure $ EUnit $ Seq ante UnitP
  EInjl t (Seq ante succ) -> do
    t'        <- infer' t
    let (Seq a b) = getAnteSucc t'
    a'        <- unify a ante
    SumP b' c <- unify (SumP b Unknown) succ
    pure $ EInjl t' (Seq a' (SumP b' c))
  EInjr t (Seq ante succ) -> do
    t'        <- infer' t
    let (Seq a c) = getAnteSucc t'
    a'        <- unify a ante
    SumP b c' <- unify succ (SumP Unknown c)
    pure $ EInjr t' (Seq a' (SumP b c'))
  ECase s t (Seq ante succ) -> do
    s' <- infer' s
    t' <- infer' t
    let (Seq ac d1) = getAnteSucc s'
    let (Seq bc d2) = getAnteSucc t'
    ProdP a c1 <- unify ac (ProdP Unknown Unknown)
    ProdP b c2 <- unify bc (ProdP Unknown Unknown)
    c          <- unify c1 c2
    d          <- unify d1 d2
    ante'      <- unify ante (ProdP (SumP a b) c)
    succ'      <- unify succ d
    pure $ ECase s' t' (Seq ante' succ')
  EPair s t (Seq ante succ) -> do
    s' <- infer' s
    t' <- infer' t
    let (Seq a1 b) = getAnteSucc s'
    let (Seq a2 c) = getAnteSucc t'
    a     <- unify a1 a2
    ante' <- unify ante a
    succ' <- unify succ (ProdP b c)
    pure $ EPair s' t' (Seq ante' succ')
  ETake t (Seq ante succ) -> do
    t' <- infer' t
    let (Seq a c) = getAnteSucc t'
    ante' <- unify ante (ProdP a Unknown)
    succ' <- unify succ c
    pure $ ETake t' (Seq ante' succ')
  EDrop t (Seq ante succ) -> do
    t' <- infer' t
    let (Seq b c) = getAnteSucc t'
    ante' <- unify ante (ProdP Unknown b)
    succ' <- unify succ c
    pure $ EDrop t' (Seq ante' succ')

data BitMachine = BitMachine
  { _readFrameStack  :: [ (Vector (Maybe Bit), Int) ]
  , _writeFrameStack :: [ (Vector (Maybe Bit), Int) ]
  }

makeLenses ''BitMachine

bitSize :: Ty -> Int
bitSize UnitTy = 0
bitSize (Sum a b) = 1 + max (bitSize a) (bitSize b)
bitSize (Prod a b) = bitSize a + bitSize b

padl :: Ty -> Ty -> Int
padl a b = max (bitSize a) (bitSize b) - bitSize a

padr :: Ty -> Ty -> Int
padr a b = max (bitSize a) (bitSize b) - bitSize b

data Failure
  = BadWriteCursorPosition
  | BadReadCursorPosition
  | WriteExpectsUndefined
  | MustHaveActiveWriteFrame
  | MustHaveActiveReadFrame
  | InvariantViolation
  | NoRead
  deriving Show

type Operational = StateT BitMachine (Either Failure)

failWith :: Failure -> Maybe a -> Operational a
failWith failure = \case
  Nothing -> lift (Left failure)
  Just a  -> pure a

assert :: Failure -> Bool -> Operational ()
assert failure = \case
  False -> lift (Left failure)
  True  -> pure ()

invariantSafe :: Getting (First a) BitMachine a -> Operational a
invariantSafe getter = preuse getter >>= failWith InvariantViolation

nop :: Operational ()
nop = pure ()

write :: Bit -> Operational ()
write b = do
  (frame, pos) <- invariantSafe (writeFrameStack . _head)
  assert BadWriteCursorPosition $ pos < length frame
  assert WriteExpectsUndefined $ frame ^?! ix pos == Nothing
  writeFrameStack . _head . _1 . ix pos ?= b

copy :: Int -> Operational ()
copy n = do
  (readFrame, readPos)   <- invariantSafe (readFrameStack . _head)
  (writeFrame, writePos) <- invariantSafe (writeFrameStack . _head)

  assert BadReadCursorPosition  $ readPos  + n <= length readFrame
  assert BadWriteCursorPosition $ writePos + n <= length writeFrame

  slice <- invariantSafe (readFrameStack . _head . _1 . to (V.slice readPos n))

  let updateVector = V.zip (V.generate n (writePos +)) slice
  writeFrameStack . _head . _1 %= flip V.update updateVector

skip :: Int -> Operational ()
skip n = do
  (frame, pos) <- invariantSafe (writeFrameStack . _head)
  assert BadWriteCursorPosition $ pos + n <= length frame
  writeFrameStack . _head . _2 += n

fwd :: Int -> Operational ()
fwd n = do
  (frame, pos) <- invariantSafe (readFrameStack . _head)
  assert BadReadCursorPosition $ pos + n <= length frame
  readFrameStack . _head . _2 += n

bwd :: Int -> Operational ()
bwd n = do
  (frame, pos) <- invariantSafe (readFrameStack . _head)
  assert BadReadCursorPosition $ pos + n <= length frame
  readFrameStack . _head . _2 -= n

newFrame :: Int -> Operational ()
newFrame n = writeFrameStack %= cons (V.replicate n Nothing, 0)

moveFrame :: Operational ()
moveFrame = do
  stk <- use writeFrameStack
  let Just (frame, stk') = uncons stk
  assert MustHaveActiveWriteFrame $ Prelude.not (null stk')
  writeFrameStack .= stk'
  readFrameStack %= cons (frame & _2 .~ 0)

dropFrame :: Operational ()
dropFrame = do
  stk <- use readFrameStack
  assert MustHaveActiveReadFrame $ Prelude.not (null stk)
  readFrameStack %= tail

read :: Operational Bit
read = do
  stk <- use readFrameStack
  case stk of
    (arr, i):_ -> case arr ^? ix i of
      Just (Just b) -> pure b
      _ -> throwError NoRead
    _ -> throwError NoRead

execI :: Instruction -> Operational Int
execI = \case
  Nop        -> nop        >> next
  Write bit  -> write bit  >> next
  Copy n     -> copy n     >> next
  Skip n     -> skip n     >> next
  Fwd n      -> fwd n      >> next
  Bwd n      -> bwd n      >> next
  NewFrame n -> newFrame n >> next
  MoveFrame  -> moveFrame  >> next
  DropFrame  -> dropFrame  >> next
  ReadJmp n  -> do
    stk <- use readFrameStack
    case stk of
      (arr, i):_ -> case arr ^? ix i of
        Just (Just (Bit b)) -> pure $ if b then n else 1
        _ -> throwError NoRead
      _ -> throwError NoRead
  Jmp n -> pure n
  where next = pure 1

runOperational :: Operational a -> BitMachine -> Either Failure (a, BitMachine)
runOperational = runStateT

-- TODO: rewrite as fold
run
  :: BitMachine
  -> [(Instruction, Path)]
  -> [(Maybe Instruction, Path, Either Failure BitMachine)]
run init insts = go (Nothing, []) init insts where
  go (prevInst, prevPath) machine [] = [(prevInst, prevPath, Right machine)]
  go (prevInst, prevPath) machine ((inst, path):insts) = case runOperational (execI inst) machine of
    Left failure -> [(prevInst, prevPath, Left failure)]
    -- XXX hacky
    Right (jump, machine') -> (prevInst, prevPath, Right machine):go (Just inst, path) machine' (drop (jump - 1) insts)

data Instruction
  = Nop
  | Write Bit
  | Copy Int
  | Skip Int
  | Fwd Int
  | Bwd Int
  | NewFrame Int
  | MoveFrame
  | DropFrame
  | ReadJmp Int
  | Jmp Int
  deriving Show

data Step
  = Child1
  | Child2
  deriving Show

type Path = [Step]

compile :: Path -> ElabTerm Ty -> [(Instruction, Path)]
compile path = \case
  EIden (Seq a _a) -> [(Copy (bitSize a), path)]
  (EComp s t _)
    -> [ (NewFrame (bitSize (getSucc s)), path) ]
    <> compile (Child1:path) s
    <> [ (MoveFrame, path) ]
    <> compile (Child2:path) t
    <> [ (DropFrame, path) ]
  (EUnit _seq) -> [(Nop, path)]
  (EInjl t (Seq _ (Sum b c)))
    -> [ (Write ff, path) ]
    <> [ (Skip (padl b c), path) ]
    <> compile (Child1:path) t
  (EInjr t (Seq _a (Sum b c)))
    -> [ (Write tt, path) ]
    <> [ (Skip (padr b c), path) ]
    <> compile (Child1:path) t
  (ECase s t (Seq (Prod (Sum a b) _) _)) ->
    let branch1 =
             [ (Fwd (1 + padl a b), path) ]
          <> compile (Child1:path) s
          <> [ (Bwd (1 + padl a b), path) ]
          <> [ (Jmp (length branch2 + 1), path) ]
        branch2 =
             [ (Fwd (1 + padr a b), path) ]
          <> compile (Child2:path) t
          <> [ (Bwd (1 + padr a b), path) ]
    in (ReadJmp (length branch1 + 1), path) : branch1 <> branch2
  (EPair s t _) -> compile (Child1:path) s <> compile (Child2:path) t
  (ETake t _) -> compile (Child1:path) t
  (EDrop t (Seq (Prod a _) _))
    -> [ (Fwd (bitSize a), path) ]
    <> compile (Child1:path) t
    <> [ (Bwd (bitSize a), path) ]
  _ -> error "no match"

operational :: ElabTerm Ty -> Operational ()
operational = \case
  (EIden (Seq a _a)) -> copy (bitSize a)
  (EComp s t _) -> do
    newFrame (bitSize (getSucc s))
    operational s
    moveFrame
    operational t
    dropFrame
  (EUnit _seq) -> nop
  (EInjl t (Seq _ (Sum b c))) -> do
    write ff
    skip $ padl b c
    operational t
  (EInjr t (Seq _a (Sum b c))) -> do
    write tt
    skip $ padr b c
    operational t
  (ECase s t (Seq (Prod (Sum a b) _) _)) -> do
    bit <- read
    case bit of
      Bit False -> do
        fwd (1 + padl a b)
        operational s
        bwd (1 + padl a b)
      Bit True -> do
        fwd (1 + padr a b)
        operational t
        bwd (1 + padr a b)
  (EPair s t _) -> do
    operational s
    operational t
  (ETake t _) -> operational t
  (EDrop t (Seq (Prod a _) _)) -> do
    fwd (bitSize a)
    operational t
    bwd (bitSize a)
  _ -> error "no match"

-- Cell usage static analysis
cellBnd :: Term a b -> Ty -> Ty -> Int
cellBnd t a b = bitSize a + bitSize b + extraCellBnd a b t

extraCellBnd :: Ty -> Ty -> Term a b -> Int
extraCellBnd _ _ Iden = 0
extraCellBnd _a _c (Comp _s _t) = error "todo: extraCellBnd Comp"
extraCellBnd _ _ Unit = 1
extraCellBnd a (Sum b _c) (Injl t) = extraCellBnd a b t
extraCellBnd a (Sum _b c) (Injr t) = extraCellBnd a c t
extraCellBnd (Prod (Sum a b) c) d (Case s t)
  = max (extraCellBnd (Prod a c) d s) (extraCellBnd (Prod b c) d t)
extraCellBnd a (Prod b c) (Pair s t)
  = max (extraCellBnd a b s) (extraCellBnd a c t)
extraCellBnd (Prod a _b) c (Take t) = extraCellBnd a c t
extraCellBnd (Prod _a b) c (Drop t) = extraCellBnd b c t
extraCellBnd _ _ _ = error "todo: extraCellBnd fallthrough"
