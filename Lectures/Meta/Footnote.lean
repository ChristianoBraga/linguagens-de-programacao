/-
Footnotes. Usage:

  ... [LoVe](url){fnref}[lovelib] ...          -- the marker in the text

  :::footnotes
  {fnAnchor "lovelib"}[] LoVe reúne os arquivos ...
  :::

The marker and the note sit on the same page, so both links are plain
fragments. Numbers come from the footnote counter of `Lectures.Meta.Label`,
which restarts in each lecture.
-/

import VersoManual
import Lectures.Meta.Label

open Lean Elab
open Verso Doc Elab Html
open Verso.Output Html
open Verso.Genre Manual
open Verso.ArgParse

namespace Lectures

def footnoteCss : String := r#"
.footnotes {
  font-size: 0.82em;
  line-height: 1.5;
  margin-top: 2.5rem;
  padding-top: 0.75rem;
  border-top: 1px solid #d8dee6;
}
.footnotes p {
  margin: 0.5rem 0;
}
.fn-ref {
  font-weight: 600;
}
.fn-ref a, .fn-anchor {
  text-decoration: none;
}
.fn-anchor {
  font-weight: 600;
  margin-right: 0.3rem;
}
.fn-ref:target, .fn-anchor:target {
  background-color: var(--verso-selected-color);
}
"#

block_extension Block.footnotes where
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [footnoteCss]
  toHtml := some fun _ goB _ _ contents => do
    pure {{<div class="footnotes">{{← contents.mapM goB}}</div>}}

/-- The notes themselves, rendered in a smaller font at the end of the text. -/
@[directive]
def footnotes : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other Block.footnotes #[$args,*])

inline_extension Inline.fnref (key : String) where
  data := .str key
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [footnoteCss]
  toHtml := some fun goI _ data content => do
    match data with
    | .str key =>
      let st ← Verso.Doc.Html.HtmlT.state
      let some e := findLabel st key
        | reportError s!"fnref: no footnote '{key}'"
          pure <| Html.seq (← content.mapM goI)
      pure {{
        <sup class="fn-ref" id={{"fnref-" ++ key}}>
          <a href={{"#fn-" ++ key}}>{{Html.text true e.num}}</a>
        </sup>
      }}
    | _ =>
      reportError s!"fnref: failed to deserialize key: {data}"
      pure <| Html.seq (← content.mapM goI)

inline_extension Inline.fnAnchor (key : String) where
  data := .str key
  traverse _ data _ := do
    match data with
    | .str key =>
      assignLabel { key, counter := "footnote", word := "", cls := "fn-anchor",
                    resetLevel := 1, prefixLevel := 0 }
      pure none
    | _ =>
      reportError s!"fnAnchor: failed to deserialize key: {data}"
      pure none
  toTeX := none
  extraCss := [footnoteCss]
  toHtml := some fun goI _ data content => do
    match data with
    | .str key =>
      let st ← Verso.Doc.Html.HtmlT.state
      let num := (findLabel st key).map (·.num) |>.getD ""
      pure {{
        <a class="fn-anchor" id={{"fn-" ++ key}} href={{"#fnref-" ++ key}}>
          {{Html.text true s!"{num}."}}
        </a>
        {{← content.mapM goI}}
      }}
    | _ =>
      reportError s!"fnAnchor: failed to deserialize key: {data}"
      pure <| Html.seq (← content.mapM goI)

section
variable {m} [Monad m] [MonadError m]

structure FootnoteConfig where
  key : String

instance : FromArgs FootnoteConfig m where
  fromArgs := FootnoteConfig.mk <$> .positional `key (ValDesc.string.as "footnote key (string literal)")
end

/-- The marker in the running text, whose content is the label of the note. -/
@[role]
def fnref : RoleExpanderOf Unit
  | (), content => do
    let key := (inlineToString (← getEnv) (mkNullNode content)).trimAscii.toString
    ``(Verso.Doc.Inline.other (Inline.fnref $(quote key)) #[])

/-- The number that opens a note, linking back to its marker. -/
@[role]
def fnAnchor : RoleExpanderOf FootnoteConfig
  | {key}, content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.fnAnchor $(quote key)) #[$content,*])
