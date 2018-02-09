{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language TemplateHaskell #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module MachineView where

import Control.Monad (void)

import Brick
  ( App(..), AttrMap, BrickEvent(..), EventM, Next, Widget
  , customMain, neverShowCursor
  , continue, halt
  , hLimit, vLimit, vBox, hBox
  , padRight, padLeft, padTop, padAll, Padding(..)
  , withBorderStyle
  , str, txt
  , attrMap, withAttr, emptyWidget, AttrName, on, fg
  , (<+>), (<=>)
  )
import qualified Brick.Widgets.Border as B
import qualified Brick.Widgets.Border.Style as BS
import qualified Brick.Widgets.Center as C
import qualified Graphics.Vty as V
import Data.Vector (Vector)
import qualified Data.Vector as Vector

import Data.List (intersperse)
import Data.Maybe (fromJust)
import Data.Semigroup ((<>))
import Data.Text (Text)
import qualified Data.Text as Text
import Control.Lens

import BitMachine
import Simplicity

-- Types

type Name = ()

data AppState = AppState
  { _program       :: ElabTerm Ty
  , _erasedProgram :: ErasedTerm
  -- TODO: use a proper zipper
  -- TODO: prior states can't really be failures (are they clowns?)
  , _priorStates   :: [(Maybe Instruction, Path, Either Failure BitMachine)]
  , _currentState  :: (Maybe Instruction, Path, Either Failure BitMachine)
  , _laterStates   :: [(Maybe Instruction, Path, Either Failure BitMachine)]
  }

initState :: ElabTerm Ty -> BitMachine -> AppState
initState program machine =
  let focus:later = run machine (compile [] program)
  in AppState
       { _program       = program
       , _erasedProgram = erase' program
       , _priorStates   = []
       , _currentState  = focus
       , _laterStates   = later
       }

makeLenses ''AppState

-- App definition

app :: App AppState a Name
app = App { appDraw = drawUI
          , appChooseCursor = neverShowCursor
          , appHandleEvent = handleEvent
          , appStartEvent = return
          , appAttrMap = const theMap
          }

machineView :: IO ()
machineView = void $ customMain (V.mkVty V.defaultConfig) Nothing app $
  -- XXX fromJust
  initState (fromJust (elaborate halfAdder)) $ BitMachine
    [(Vector.fromList [Just tt, Just ff], 0)]
    [(Vector.fromList [Nothing, Nothing], 0)]

-- Handling events

next :: AppState -> AppState
next current@(AppState prog eras prior focus later) = case later of
  [] -> current
  newCurrent:later' -> AppState prog eras (focus:prior) newCurrent later'

prev :: AppState -> AppState
prev current@(AppState prog eras prior focus later) = case prior of
  [] -> current
  newCurrent:prior' -> AppState prog eras prior' newCurrent (focus:later)

handleEvent :: AppState -> BrickEvent Name a -> EventM Name (Next AppState)
handleEvent g (VtyEvent (V.EvKey (V.KChar 'q') [])) = halt g
handleEvent g (VtyEvent (V.EvKey V.KEsc []))        = halt g
handleEvent g (VtyEvent (V.EvKey V.KUp []))         = continue $ prev g
handleEvent g (VtyEvent (V.EvKey (V.KChar 'k') [])) = continue $ prev g
handleEvent g (VtyEvent (V.EvKey V.KDown []))       = continue $ next g
handleEvent g (VtyEvent (V.EvKey (V.KChar 'j') [])) = continue $ next g
handleEvent g _                                     = continue g

-- Drawing

drawUI :: AppState -> [Widget Name]
drawUI g = let (inst, path, machine) = g ^. currentState in case machine of
  Left failure  -> [ C.center (str (show failure)) ]
  Right machine ->
    let inst' = str $ case inst of
                 Just i  -> show i
                 Nothing -> ""
        showInstr = \case
          Nothing -> ""
          Just instr -> show instr
        aboveInstrs
          = map (str . showInstr . (^._1))
          $ reverse
          $ take 3
          $ g ^. priorStates
        belowInstrs
          = map (str . showInstr . (^._1))
          $ take 10
          $ g ^. laterStates
    in [ C.vCenter $ (C.hCenter $
    padRight (Pad 2) (drawFrameStack (machine ^. readFrameStack))
    <+> drawFrameStack (machine ^. writeFrameStack))
    <=> (padTop (Pad 5) $ (C.hCenter (drawPath path (g ^. erasedProgram)))
    <+> (C.hCenter $ vBox $ aboveInstrs <> [withAttr "blueAttr" inst'] <> belowInstrs))
    ]

data Expansion = NotExpanded | Expanded

drawPath :: Path -> ErasedTerm -> Widget Name
drawPath = go 0 where
  go :: Int -> Path -> ErasedTerm -> Widget Name
  go _n [] tm = withAttr "blueAttr" (nameOf NotExpanded tm)
  go n (Child2:path') tm = case tm of
    ErComp t s -> vBox
      [ nameOf Expanded tm
      , ind <+> nameOf NotExpanded t
      , ind <+> go (n + 1) path' s
      ]
    ErCase t s -> vBox
      [ nameOf Expanded tm
      , ind <+> nameOf NotExpanded t
      , ind <+> go (n + 1) path' s
      ]
    ErPair t s -> vBox
      [ nameOf Expanded tm
      , ind <+> nameOf NotExpanded t
      , ind <+> go (n + 1) path' s
      ]
  go n (Child1:path') tm = case tm of
    ErComp t s -> vBox
      [ nameOf Expanded tm
      , ind <+> go (n + 1) path' t
      , ind <+> nameOf NotExpanded s
      ]
    ErCase t s -> vBox
      [ nameOf Expanded tm
      , ind <+> go (n + 1) path' t
      , ind <+> nameOf NotExpanded s
      ]
    ErPair t s -> vBox
      [ nameOf Expanded tm
      , ind <+> go (n + 1) path' t
      , ind <+> nameOf NotExpanded s
      ]
    ErInjl t -> vBox [ nameOf Expanded tm , ind <+> go (n + 1) path' t ]
    ErInjr t -> vBox [ nameOf Expanded tm , ind <+> go (n + 1) path' t ]
    ErTake t -> vBox [ nameOf Expanded tm , ind <+> go (n + 1) path' t ]
    ErDrop t -> vBox [ nameOf Expanded tm , ind <+> go (n + 1) path' t ]
    _ -> error $ "unmatched: " ++ show tm

  ind = txt " "

  nameOf :: Expansion -> ErasedTerm -> Widget Name
  nameOf expansion = txt . \case
    ErIden     -> "iden"
    ErComp _ _ -> pre <> "comp"
    ErUnit     -> "unit"
    ErInjl _   -> pre <> "injl"
    ErInjr _   -> pre <> "injr"
    ErCase _ _ -> pre <> "case"
    ErPair _ _ -> pre <> "pair"
    ErTake _   -> pre <> "take"
    ErDrop _   -> pre <> "drop"
    where pre = case expansion of
            NotExpanded -> "+"
            Expanded    -> "-"

followPath :: Path -> ErasedTerm -> ErasedTerm
followPath [] tm = tm
followPath (Child2:path') tm = case tm of
  ErComp _ tm' -> followPath path' tm'
  ErCase _ tm' -> followPath path' tm'
  ErPair _ tm' -> followPath path' tm'
  _ -> error $ "can't follow child 2 in " ++ show tm
followPath (Child1:path') tm = case tm of
  ErComp tm' _ -> followPath path' tm'
  ErInjl tm'   -> followPath path' tm'
  ErInjr tm'   -> followPath path' tm'
  ErCase tm' _ -> followPath path' tm'
  ErPair tm' _ -> followPath path' tm'
  ErTake tm'   -> followPath path' tm'
  ErDrop tm'   -> followPath path' tm'
  _ -> error $ "can't follow child 1 in " ++ show tm ++ " (" ++ show path' ++ " remaining)"

drawSimplicity :: ErasedTerm -> Path -> Widget Name
drawSimplicity path tm =
  let tmDisplay = case followPath tm path of
        ErIden -> "iden"
        ErComp _ _ -> "comp"
        ErUnit -> "unit"
        ErInjl _ -> "injl"
        ErInjr _ -> "injr"
        ErCase _ _ -> "case"
        ErPair _ _ -> "pair"
        ErTake _ -> "take"
        ErDrop _ -> "drop"
  in str tmDisplay

drawFrameStack :: [ (Vector (Maybe Bit), Int) ] -> Widget Name
drawFrameStack rows =
  let drawBit = \case
        Nothing          -> txt "?"
        Just (Bit False) -> txt "0"
        Just (Bit True)  -> txt "1"
      drawBits (bits, cursorPos) =
        let drawnBits = txt "[" : map drawBit (Vector.toList bits) <> [txt "]"]
            (splitBefore, cursorBit:splitAfter) = splitAt (cursorPos + 1) drawnBits
        in hBox $ splitBefore <> [withAttr "cursorAttr" cursorBit] <> splitAfter
  in vBox $ map drawBits rows

theMap :: AttrMap
theMap = attrMap V.defAttr
  [ ("blueAttr", fg V.blue)
  , ("greenAttr", fg V.green)
  , ("gameOver", fg V.red `V.withStyle` V.bold)
  , ("cursorAttr", V.defAttr `V.withStyle` V.underline)
  ]

