/-
A `hover` role that renders its contents with a plain-text tooltip, shown
by the browser on hover via the `title` attribute. Usage:

  {hover "tooltip text"}[visible text]
-/

import VersoManual

open Lean Elab
open Verso Doc Elab Html
open Verso.Output Html
open Verso.Genre Manual
open Verso.ArgParse

namespace Lectures

def hoverTipCss : String := r#"
.hover-tip {
  text-decoration-line: underline;
  text-decoration-style: dotted;
  text-decoration-thickness: from-font;
  cursor: help;
}
"#

inline_extension hover (tip : String) where
  data := .str tip
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [hoverTipCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data content => do
      match data with
      | .str tip =>
        pure {{<span class="hover-tip" title={{tip}}>{{← content.mapM goI}}</span>}}
      | _ =>
        reportError s!"Failed to deserialize hover tip: {data}"
        return {{""}}

section
variable {m} [Monad m] [MonadError m]

structure HoverConfig where
  tip : String

instance : FromArgs HoverConfig m where
  fromArgs := HoverConfig.mk <$> .positional `tip (ValDesc.string.as "hover text (string literal)")
end

@[role hover]
def hoverExpander : RoleExpanderOf HoverConfig
  | {tip}, content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (hover $(quote tip)) #[$content,*])
