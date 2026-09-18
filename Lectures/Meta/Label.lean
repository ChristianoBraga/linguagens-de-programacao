/-
Labels and counters, in the style of LaTeX. Every referenceable element carries
a label, never a hand-written number, and its number comes from a counter.

Definition sites take the label as an argument:

  {figcap "fig-lean-components"}[The main components of Lean.]
  {tabcap "tbl-connectives"}[The five connectives.]
  {ex "ex-double-negation"}[]
  {exercise "exr-implication-composes"}[]

Reference sites take the label as their content:

  {numref}[fig-lean-components]     -- renders "Figure 1.1", linked
  {secref}[tactics]               -- renders "Section 1.8", linked

Each counter fixes two levels. `resetLevel` is the depth of the section number
at which the counter restarts, and `prefixLevel` is how much of that number the
label displays. Figures restart per lecture and show it (Figure 1.1), tables
restart per section and show it (Table 1.6.1), and examples restart per section
but show a bare number (Example 3).

Numbers are assigned during the traversal pass. A label is appended to an
ordered registry the first time it is seen, and its number is the position of
its label among those of the same counter and scope, so re-traversal is
idempotent and the numbers converge.
-/

import VersoManual

open Lean Elab
open Verso Doc Elab Html
open Verso.Output Html
open Verso.Genre Manual
open Verso.ArgParse

register_option lectures.language : String := {
  defValue := "en"
  descr := "Language of the notes, which selects the words of generated labels"
}

namespace Lectures

/-- The word that opens a label, per language and counter. -/
def labelWord (lang counter : String) : String :=
  match lang, counter with
  | "pt", "figure" => "Figura"
  | "pt", "table" => "Tabela"
  | "pt", "example" => "Exemplo"
  | "pt", "exercise" => "Exercício"
  | "pt", "section" => "Seção"
  | _, "figure" => "Figure"
  | _, "table" => "Table"
  | _, "example" => "Example"
  | _, "exercise" => "Exercise"
  | _, "section" => "Section"
  | _, _ => ""

def currentLanguage [Monad m] [MonadOptions m] : m String := do
  return lectures.language.get (← getOptions)

/-- What a definition site declares about its label. -/
structure LabelInfo where
  key : String
  counter : String
  word : String
  cls : String
  resetLevel : Nat
  prefixLevel : Nat
deriving ToJson, FromJson, Inhabited, Repr

/-- What the registry records for a label once its number is assigned. -/
structure LabelEntry where
  key : String
  counter : String
  scope : String
  word : String
  num : String
deriving ToJson, FromJson, Inhabited, Repr, BEq

structure LabelRegistry where
  entries : Array LabelEntry := #[]
deriving ToJson, FromJson, Inhabited, Repr

def labelDomain : Name := `Lectures.label
def labelStateKey : Name := `Lectures.labels

def labelRegistry (st : TraverseState) : LabelRegistry :=
  match (st.get? labelStateKey : Option (Except String LabelRegistry)) with
  | some (.ok r) => r
  | _ => {}

def findLabel (st : TraverseState) (key : String) : Option LabelEntry :=
  (labelRegistry st).entries.find? (·.key == key)

/-- The label as it reads in the prose, such as `Table 1.6.1`. -/
def LabelEntry.text (e : LabelEntry) : String :=
  if e.word.isEmpty then e.num else s!"{e.word} {e.num}"

/-- The section number of the traversal position, dropping the unnumbered root. -/
def sectionComponents [Monad m] [MonadReaderOf TraverseContext m] : m (Array Nat) := do
  let hs := (← readThe TraverseContext).headers
  let mut out := #[]
  for h in hs.extract 1 hs.size do
    match h.metadata.bind (·.assignedNumber) with
    | some (.nat n) => out := out.push n
    | _ => break
  return out

def joinNums (ns : List String) : String := String.intercalate "." ns

/--
Records the label and assigns its number. Re-registering a label keeps its
position, so the number is stable across traversal passes.
-/
def assignLabel [Monad m] [MonadState TraverseState m] [MonadReaderOf TraverseContext m]
    (info : LabelInfo) : m Unit := do
  let comps ← sectionComponents
  let scope := joinNums ((comps.extract 0 info.resetLevel).toList.map toString)
  let pre := (comps.extract 0 info.prefixLevel).toList.map toString
  let reg := labelRegistry (← get)
  let idx? := reg.entries.findIdx? (·.key == info.key)
  let i := idx?.getD reg.entries.size
  let entries :=
    if idx?.isSome then reg.entries
    else reg.entries.push { key := info.key, counter := info.counter, scope, word := info.word, num := "" }
  let ord := 1 + ((entries.extract 0 i).filter fun e => e.counter == info.counter && e.scope == scope).size
  let num := joinNums (pre ++ [toString ord])
  let entries := entries.set! i { key := info.key, counter := info.counter, scope, word := info.word, num }
  modify (·.set labelStateKey ({ entries } : LabelRegistry))

def labelCss : String := r#"
.lbl-caption {
  font-weight: 600;
}
.lbl-anchor:target {
  background-color: var(--verso-selected-color);
}
.lbl-ref {
  text-decoration: none;
}
"#

inline_extension Inline.labelAnchor (key counter word cls : String) (resetLevel prefixLevel : Nat) where
  data := ToJson.toJson (LabelInfo.mk key counter word cls resetLevel prefixLevel)
  traverse id data _ := do
    match FromJson.fromJson? data with
    | .error e =>
      reportError s!"labelAnchor: failed to deserialize: {e}"
      pure none
    | .ok (info : LabelInfo) =>
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path s!"--label-{info.key}"
      modify (·.saveDomainObject labelDomain info.key id)
      assignLabel info
      pure none
  toTeX := none
  extraCss := [labelCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI id data content => do
      let inner ← content.mapM goI
      match FromJson.fromJson? data with
      | .error e =>
        reportError s!"labelAnchor: failed to deserialize: {e}"
        pure <| Html.seq inner
      | .ok (info : LabelInfo) =>
        let st ← Verso.Doc.Html.HtmlT.state
        let num :=
          match findLabel st info.key with
          | some e => if e.word.isEmpty then s!"{e.num}." else s!"{e.text}."
          | none => ""
        let lead := if inner.isEmpty then num else num ++ " "
        let some link := st.externalTags[id]?
          | reportError s!"labelAnchor: no external tag for '{info.key}'"
            pure <| Html.seq inner
        pure {{
          <span class={{"lbl-anchor " ++ info.cls}} id={{link.htmlId.toString}}>
            {{Html.text true lead}}{{inner}}
          </span>
        }}

inline_extension Inline.numref (key : String) where
  data := .str key
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [labelCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data content => do
      match data with
      | .str key =>
        let st ← Verso.Doc.Html.HtmlT.state
        let some e := findLabel st key
          | reportError s!"numref: no label '{key}'"
            pure <| Html.seq (← content.mapM goI)
        if let some obj := st.getDomainObject? labelDomain key then
          let ids := obj.ids.toArray
          if h : ids.size = 1 then
            if let some link := st.resolveId ids[0] then
              return {{<a class="lbl-ref" href={{link.relativeLink}}>{{Html.text true e.text}}</a>}}
        reportError s!"numref: unresolved label '{key}'"
        pure <| Html.text true e.text
      | _ =>
        reportError s!"numref: failed to deserialize key: {data}"
        pure <| Html.seq (← content.mapM goI)

/- A reference to a section, whose number Verso assigns. -/
inline_extension Inline.secref (secTag : String) (secWord : String) where
  data := ToJson.toJson (secTag, secWord)
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [labelCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data content => do
      match FromJson.fromJson? data with
      | .error e =>
        reportError s!"secref: failed to deserialize: {e}"
        pure <| Html.seq (← content.mapM goI)
      | .ok ((secTag, secWord) : String × String) =>
        let st ← Verso.Doc.Html.HtmlT.state
        let some obj := st.getDomainObject? sectionDomain secTag
          | reportError s!"secref: no section tagged '{secTag}'"
            pure <| Html.seq (← content.mapM goI)
        let num :=
          match obj.data.getObjVal? "sectionNum" with
          | .ok (.str n) => (n.dropEndWhile (· == '.')).toString
          | _ => ""
        let text := if num.isEmpty then secWord else s!"{secWord} {num}"
        let ids := obj.ids.toArray
        if h : ids.size = 1 then
          if let some link := st.resolveId ids[0] then
            return {{<a class="lbl-ref" href={{link.relativeLink}}>{{Html.text true text}}</a>}}
        reportError s!"secref: unresolved section '{secTag}'"
        pure <| Html.text true text

section
variable {m} [Monad m] [MonadError m]

structure LabelConfig where
  key : String

instance : FromArgs LabelConfig m where
  fromArgs := LabelConfig.mk <$> .positional `key (ValDesc.string.as "label (string literal)")
end

private def anchorTerm (key counter cls : String) (resetLevel prefixLevel : Nat)
    (content : TSyntaxArray `inline) : DocElabM Term := do
  let word := labelWord (← currentLanguage) counter
  let content ← content.mapM elabInline
  ``(Verso.Doc.Inline.other
      (Inline.labelAnchor $(quote key) $(quote counter) $(quote word) $(quote cls)
        $(quote resetLevel) $(quote prefixLevel))
      #[$content,*])

/-- The caption of a figure, numbered per lecture. -/
@[role]
def figcap : RoleExpanderOf LabelConfig
  | {key}, content => anchorTerm key "figure" "lbl-caption" 1 1 content

/-- The caption of a table, numbered per section. -/
@[role]
def tabcap : RoleExpanderOf LabelConfig
  | {key}, content => anchorTerm key "table" "lbl-caption" 2 2 content

/-- The number that opens an example, restarted in each section. -/
@[role]
def ex : RoleExpanderOf LabelConfig
  | {key}, content => anchorTerm key "example" "lbl-example" 2 0 content

/-- The number that opens an exercise, restarted in each lecture. -/
@[role]
def exercise : RoleExpanderOf LabelConfig
  | {key}, content => anchorTerm key "exercise" "lbl-example" 1 0 content

private def contentKey (content : TSyntaxArray `inline) : DocElabM String := do
  return (inlineToString (← getEnv) (mkNullNode content)).trimAscii.toString

/-- A reference to a labeled element, which prints its word and its number. -/
@[role]
def numref : RoleExpanderOf Unit
  | (), content => do
    let key ← contentKey content
    ``(Verso.Doc.Inline.other (Inline.numref $(quote key)) #[])

/-- A reference to a tagged section, which prints its number. -/
@[role]
def secref : RoleExpanderOf Unit
  | (), content => do
    let tag ← contentKey content
    let word := labelWord (← currentLanguage) "section"
    ``(Verso.Doc.Inline.other (Inline.secref $(quote tag) $(quote word)) #[])
