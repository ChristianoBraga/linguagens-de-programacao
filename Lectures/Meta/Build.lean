/-
Shared build step that extracts `savedLean` blocks into files under
`example-code` in the output directory. Parameterized by the path of the
main module so both language builds can reuse it.

Adapted from the Verso textbook template (Lean FRO LLC, Apache 2.0).
-/

import Std.Data.HashMap
import VersoManual
import Lectures.Meta.Lean

open Verso Doc
open Verso.Genre Manual
open Std (HashMap)

namespace Lectures

/--
Extract the marked exercises and example code, resolving saved filenames
relative to the directory of `mainFile`.
-/
partial def buildExercisesFrom (mainFile : System.FilePath) (mode : Mode) (cfg : Config) (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode
    | pure ()
  let code := (← part text |>.run {}).snd
  let dest := cfg.destination / "html-multi" / "example-code"
  let some mainDir := mainFile.parent
    | throw <| IO.userError s!"Can't find directory of `{mainFile}`"

  IO.FS.createDirAll <| dest
  for ⟨fn, f⟩ in code do
    -- Make sure the path is relative to that of the main module
    if let some fn' := fn.dropPrefix? mainDir.toString then
      let fn' := (fn'.dropWhile (· ∈ System.FilePath.pathSeparators)).copy
      let fn := dest / fn'
      if let some parent := fn.parent then IO.FS.createDirAll parent
      if (← fn.pathExists) then IO.FS.removeFile fn
      IO.FS.writeFile fn f
    else
      reportError s!"Couldn't save example code. The path '{fn}' is not underneath '{mainDir}'."

where
  part : Part Manual → StateT (HashMap String String) (BuildLogT IO) Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → StateT (HashMap String String) (BuildLogT IO) Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        let .arr #[.str fn, .str code] := which.data
          | reportError s!"Failed to deserialize saved Lean data {which.data}"
        modify fun saved =>
          saved.alter fn fun prior =>
            let prior := prior.getD ""
            some (prior ++ code ++ "\n")

      if which.name == ``Block.savedImport then
        let .arr #[.str fn, .str code] := which.data
          | reportError s!"Failed to deserialize saved Lean import data {which.data}"
        modify fun saved =>
          saved.alter fn fun prior =>
          let prior := prior.getD ""
          some (code.trimAsciiEnd.copy ++ "\n" ++ prior)

      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()
