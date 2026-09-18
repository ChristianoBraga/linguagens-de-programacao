/-
Entry point for the Portuguese build of the lecture notes.
Run with: lake exe lectures-pt --output _out/pt
-/

import VersoManual
import Lectures.Meta.Build
import Lectures.Meta.Style
import Lectures.Pt

open Verso Doc
open Verso.Genre Manual

open Lectures

-- Computes the path of this very `main`, to ensure that examples get names relative to it
open Lean Elab Term Command in
#eval show CommandElabM Unit from do
  let here := (← liftTermElabM (readThe Lean.Core.Context)).fileName
  elabCommand (← `(private def $(mkIdent `mainFileName) : System.FilePath := $(quote here)))

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraHead := codeHighlightHead
  logo := some "logo.svg"
  logoLink := some "../"
  extraFilesHtml := [("site/logo.svg", "logo.svg")]

def main := manualMain (%doc Lectures.Pt) (extraSteps := [buildExercisesFrom mainFileName]) (config := config)
