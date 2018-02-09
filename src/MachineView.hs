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
import Control.Lens

import BitMachine
import Simplicity

-- Types

type Name = ()

data AppState = AppState
  { _program      :: ElabTerm Ty
  -- TODO: use a proper zipper
  -- TODO: prior states can't really be failures (are they clowns?)
  , _priorStates  :: [(Maybe Instruction, Either Failure BitMachine)]
  , _currentState :: (Maybe Instruction, Either Failure BitMachine)
  , _laterStates  :: [(Maybe Instruction, Either Failure BitMachine)]
  }

initState :: ElabTerm Ty -> BitMachine -> AppState
initState program machine =
  let focus:later = run machine (compile program)
  in AppState
       { _program      = program
       , _priorStates  = []
       , _currentState = focus
       , _laterStates  = later
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
next current@(AppState prog prior focus later) = case later of
  [] -> current
  newCurrent:later' -> AppState prog (focus:prior) newCurrent later'

prev :: AppState -> AppState
prev current@(AppState prog prior focus later) = case prior of
  [] -> current
  newCurrent:prior' -> AppState prog prior' newCurrent (focus:later)

handleEvent :: AppState -> BrickEvent Name a -> EventM Name (Next AppState)
handleEvent g (VtyEvent (V.EvKey (V.KChar 'q') [])) = halt g
handleEvent g (VtyEvent (V.EvKey V.KEsc []))        = halt g
handleEvent g (VtyEvent (V.EvKey V.KLeft []))       = continue $ prev g
handleEvent g (VtyEvent (V.EvKey V.KRight []))      = continue $ next g
handleEvent g _                                     = continue g

-- Drawing

drawUI :: AppState -> [Widget Name]
drawUI g = case g ^. currentState . _2 of
  Left failure  -> [ C.center (str (show failure)) ]
  Right machine ->
    let inst = case g ^. currentState . _1 of
                 Just i  -> show i
                 Nothing -> "[begin]"
        showInstr = \case
          Nothing -> ""
          Just instr -> show instr <> ";"
        leftInstrs
          = str
          $ take 35
          $ padR 35
          $ concat
          $ intersperse " "
          $ map (padInstruction . showInstr . fst)
          $ reverse
          $ take 3
          $ g ^. priorStates
        rightInstrs
          = str
          $ take 35
          $ padL 35
          $ concat
          $ intersperse " "
          $ map (padInstruction . showInstr . fst)
          $ take 3
          $ g ^. laterStates
    in [ C.vCenter $ (C.hCenter $
    padRight (Pad 2) (drawFrameStack (machine ^. readFrameStack))
    <+> drawFrameStack (machine ^. writeFrameStack))
    <=> padTop (Pad 2) (leftInstrs <+> C.hCenter (withAttr "blueAttr" (str inst)) <+> rightInstrs)
    ]

padInstruction :: String -> String
padInstruction inst = padL (eachAdd + lAdd) $ padR eachAdd inst
  where paddedSize = 15
        toAdd = paddedSize - length inst
        (eachAdd, lAdd) = divMod toAdd 2

padL :: Int -> String -> String
padL n s
    | length s < n  = s ++ replicate (n - length s) ' '
    | otherwise     = s

padR :: Int -> String -> String
padR n = reverse . padL n . reverse

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

