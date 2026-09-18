/-
Entry point for the English build of the lecture notes.
Run with: lake exe lectures-en --output _out/en
-/

import VersoManual
import Lectures.Meta.Build
import Lectures.Meta.Style
import Lectures.En

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

def main := manualMain (%doc Lectures.En) (extraSteps := [buildExercisesFrom mainFileName]) (config := config)
