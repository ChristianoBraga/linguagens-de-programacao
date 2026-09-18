/-
Custom code blocks for the lecture notes.
`savedLean` blocks are elaborated like `lean` blocks and additionally
extracted to files in the `example-code` output directory, so students
receive a runnable exercise file per lecture.

Adapted from the Verso textbook template (Lean FRO LLC, Apache 2.0).
-/

import VersoManual

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean

namespace Lectures

block_extension Block.savedLean (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ goB _ _ contents =>
    contents.mapM goB

block_extension Block.savedImport (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ _ _ =>
    pure .empty

/--
Lean code that is saved to the examples file.
-/
@[code_block savedLean]
def savedLean : CodeBlockExpanderOf InlineLean.LeanBlockConfig
  | args, code => do
    let underlying ← InlineLean.lean args code
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote (code.getString))) #[$underlying])

/--
An import of some other module, to be located in the saved code. Not rendered.
-/
@[code_block]
def savedImport : CodeBlockExpanderOf Unit
  | (), code => do
    ``(Block.other (Block.savedImport $(quote (← getFileName)) $(quote (code.getString))) #[])

/--
Comments to be added as module docstrings to the examples file.
-/
@[code_block]
def savedComment : CodeBlockExpanderOf Unit
  | (), code => do
    let str := code.getString.trimAsciiEnd.copy
    let comment := s!"/-!\n{str}\n-/"
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote comment)) #[])
