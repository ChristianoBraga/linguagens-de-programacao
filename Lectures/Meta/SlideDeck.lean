/-
Slide-deck emission for the course slides.

A slide deck is an ordinary Verso `#doc (Manual)` document whose
top-level `#` sections become slides. All `lean` code blocks are
elaborated and checked at build time, exactly as in the lecture
notes. `emitSlideDeck` renders the traversed document into a single
self-contained HTML file with the CSS and JS of the hand-written
decks in `site/slides/`, and `slidesMain` is the corresponding
entry point (mirroring `manualMain`, but without the manual site).
-/

import VersoManual

open Verso Doc Elab
open Verso.Genre Manual
open Verso.Multi
open Verso.Output Html
open Verso (BuildLogT runWithLogger)
open Verso.FS (ensureDir)

namespace Lectures

/-! ## Column layout for slides

`::::cols` with `:::col` children renders the flexbox two-column
layout of the hand-written decks (`div.cols > div`).
-/

block_extension Block.slideCols where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ goB _ _ contents => do
    pure {{<div class="cols">{{← contents.mapM goB}}</div>}}

block_extension Block.slideCol where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ goB _ _ contents => do
    pure {{<div>{{← contents.mapM goB}}</div>}}

/-- A row of columns on a slide. -/
@[directive]
def cols : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other Block.slideCols #[$args,*])

/-- One column inside a `cols` row. -/
@[directive]
def col : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other Block.slideCol #[$args,*])

/-! ## Derivation trees

A `tree` code block holds preformatted text that is not Lean, such
as a natural deduction derivation, and renders as `pre.tree`.
-/

block_extension Block.slideTree (text : String) where
  data := .str text
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ data _ => do
    match data with
    | .str txt => pure {{<pre class="tree">{{txt}}</pre>}}
    | _ =>
      reportError s!"Failed to deserialize tree text: {data}"
      pure .empty

/-- A preformatted derivation tree, displayed verbatim. -/
@[code_block]
def tree : CodeBlockExpanderOf Unit
  | (), code => do
    ``(Verso.Doc.Block.other
        (Block.slideTree $(Lean.quote (code.getString))) #[])

/-! ## Labeled spans

The decks use small labeled headings inside slides: `.lbl` for
per-column kickers such as "Derivation" or "Tactic mode", `.exh`
for example headings, and `.cite` for citation lines. Each is a
role whose span carries the class; the deck CSS displays the span
as a block.
-/

inline_extension Inline.slideLabel (cls : String) where
  data := .str cls
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun goI _ data content => do
    match data with
    | .str cls =>
      pure {{<span class={{cls}}>{{← content.mapM goI}}</span>}}
    | _ =>
      reportError s!"Failed to deserialize label class: {data}"
      pure <| Html.seq (← content.mapM goI)

/-- A per-column kicker label, e.g. "Derivation". -/
@[role]
def lbl : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.slideLabel "lbl") #[$content,*])

/-- An example heading inside a slide. -/
@[role]
def exh : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.slideLabel "exh") #[$content,*])

/-- A citation line, e.g. under a quotation. -/
@[role]
def «cite» : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.slideLabel "cite") #[$content,*])

/-! ## Deck configuration -/

structure SlideDeck where
  /-- Output file name, e.g. `"lecture-2.en.html"`. -/
  fileName : String
  /-- Contents of the `<title>` element. -/
  pageTitle : String
  /-- `lang` attribute of the page. -/
  htmlLang : String := "en"
  /-- Small line above the title on the title slide. -/
  kicker : String
  /-- Center label of the footer. -/
  label : String
  /-- Link to the lecture notes, shown in the footer. -/
  notesLink : Option (String × String) := none
  /-- Link to the previous deck, shown in the footer. -/
  prevLink : Option (String × String) := none
  /-- Link to the next deck, shown next to the slide counter. -/
  nextLink : Option (String × String) := none
  /-- Text of the jump-to-start footer link. -/
  startLabel : String := "⇤ Start"
  /-- `aria-label` of the previous-slide button. -/
  prevSlideLabel : String := "Previous slide"
  /-- `aria-label` of the next-slide button. -/
  nextSlideLabel : String := "Next slide"
  /-- CSS classes assigned, in order, to the wrapper of each
      intro block of the document on the title slide. -/
  introClasses : Array String := #["subtitle", "byline", "notelink", "refs"]

/-! ## Deck CSS and JS

Copied from `site/slides/lecture-2.en.html`, with the hand-rolled
Lean highlighter removed (Verso emits highlighted token spans at
build time) and rules added for Verso-rendered code, output blocks,
and tables.
-/

def slideDeckCss : String := r##"
  :root {
    --bg: #f8fafc; --card: #ffffff; --text: #0f172a; --muted: #475569;
    --accent: #1e3a8a; --accent2: #0d9488; --border: #e2e8f0;
    --footer-bg: rgba(248,250,252,0.9); --code-bg: rgba(148,163,184,0.18);
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #0f172a; --card: #1e293b; --text: #f1f5f9; --muted: #94a3b8;
      --accent: #93c5fd; --accent2: #5eead4; --border: #334155;
      --footer-bg: rgba(15,23,42,0.9); --code-bg: rgba(148,163,184,0.22);
    }
  }
  * { box-sizing: border-box; }
  html, body { margin: 0; height: 100%; }
  body {
    background: var(--bg); color: var(--text);
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
    overflow: hidden;
  }
  .progress {
    position: fixed; top: 0; left: 0; height: 4px; width: 0;
    background: linear-gradient(90deg, var(--accent), var(--accent2));
    transition: width 0.25s ease; z-index: 10;
  }
  .deck { position: relative; height: 100vh; width: 100vw; }
  .slide {
    position: absolute; inset: 0; display: none;
    flex-direction: column; justify-content: center; align-items: center;
    padding: clamp(1.5rem, 5vw, 4.5rem) clamp(1.5rem, 6vw, 6rem) clamp(3.5rem, 7vw, 4.5rem);
    opacity: 0; transition: opacity 0.3s ease;
  }
  .slide.active { display: flex; opacity: 1; }
  /* Above the edge navigation zones (z-index 4), so clicks on the
     content column reach interactive code (tactic-state toggles). */
  .inner {
    width: 100%; max-width: 66rem; max-height: 100%; overflow-y: auto;
    position: relative; z-index: 5;
  }
  .kicker {
    text-transform: uppercase; letter-spacing: 0.12em;
    font-size: clamp(0.7rem, 1.6vw, 0.95rem); font-weight: 600;
    color: var(--accent2); margin-bottom: 0.75rem;
  }
  h1 {
    font-size: clamp(2rem, 6vw, 4.2rem); line-height: 1.05; margin: 0 0 1rem;
    background: linear-gradient(135deg, var(--accent), var(--accent2));
    -webkit-background-clip: text; background-clip: text;
    -webkit-text-fill-color: transparent; color: transparent;
  }
  h2 {
    font-size: clamp(1.3rem, 3.6vw, 2.4rem); line-height: 1.15; margin: 0 0 1.1rem;
    padding-bottom: 0.4rem; border-bottom: 3px solid;
    border-image: linear-gradient(90deg, var(--accent), var(--accent2)) 1;
  }
  ul { margin: 0; padding: 0; list-style: none; }
  li {
    position: relative; padding-left: 1.5rem; margin: 0.65rem 0;
    font-size: clamp(0.95rem, 2.2vw, 1.45rem); line-height: 1.4; color: var(--muted);
  }
  li strong { color: var(--text); }
  li::before {
    content: ""; position: absolute; left: 0; top: 0.6em;
    width: 0.55rem; height: 0.55rem; border-radius: 2px;
    background: linear-gradient(135deg, var(--accent), var(--accent2));
  }
  code {
    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    font-size: 0.9em; background: var(--code-bg);
    padding: 0.1em 0.35em; border-radius: 0.3em;
  }
  .cols { display: flex; gap: 1.4rem; flex-wrap: wrap; align-items: flex-start; }
  .cols > div { flex: 1 1 22rem; min-width: min(100%, 22rem); }
  pre.tree, pre.code {
    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    font-size: clamp(0.68rem, 1.55vw, 1rem); line-height: 1.35;
    margin: 0.5rem 0; padding: 0.8rem 1rem; white-space: pre; overflow-x: auto;
    background: var(--code-bg); border-radius: 0.5rem; color: var(--text);
  }
  blockquote {
    margin: 0.5rem 0 1rem; padding: 0.75rem 0 0.75rem 1.5rem;
    border-left: 5px solid; border-image: linear-gradient(180deg, var(--accent), var(--accent2)) 1;
    font-size: clamp(1.3rem, 3.4vw, 2.3rem); font-style: italic; line-height: 1.35; color: var(--text);
  }
  blockquote p { margin: 0; }
  .exh {
    display: block; font-weight: 700; color: var(--text);
    font-size: clamp(1rem, 2.3vw, 1.45rem); margin: 1rem 0 0.3rem;
  }
  .lbl {
    display: block; text-transform: uppercase; letter-spacing: 0.08em;
    font-size: clamp(0.68rem, 1.3vw, 0.85rem); font-weight: 700;
    color: var(--accent2); margin: 0.5rem 0 0.15rem;
  }
  .cols li {
    font-size: clamp(0.85rem, 1.7vw, 1.05rem);
    margin: 0.35rem 0; padding-left: 1.3rem;
  }
  .cols div > p { margin: 0.4rem 0 0.15rem; }
  .cite { display: block; font-size: clamp(0.8rem, 1.8vw, 1.05rem); color: var(--muted); }
  .note a, .inner li a, .inner p:not([class]) a {
    color: var(--accent); font-weight: 600;
    text-decoration: underline; text-decoration-color: var(--accent2);
  }
  .note a:hover, .inner li a:hover, .inner p:not([class]) a:hover {
    color: var(--accent2);
  }
  .subtitle { font-size: clamp(1.1rem, 3vw, 2rem); color: var(--muted); }
  .byline { font-size: clamp(0.9rem, 2vw, 1.2rem); color: var(--muted); }
  .notelink a {
    font-size: clamp(0.95rem, 2vw, 1.15rem); font-weight: 600;
    color: var(--accent); text-decoration: none;
    border: 1px solid var(--border); border-radius: 0.6rem; padding: 0.5rem 1.1rem;
    display: inline-block; background: var(--card);
  }
  .notelink a:hover { border-color: var(--accent2); }
  /* The paragraph inside .notelink carries no class of its own, so the generic
     body-link rule above matches it and underlines the button. Same
     specificity, later in the sheet, so this wins. */
  .inner .notelink p a { text-decoration: none; }
  .refs { font-size: clamp(0.85rem, 1.9vw, 1.1rem); margin: 1rem 0 0; color: var(--muted); }
  .slide--title .inner .refs { color: rgba(255,255,255,0.9); }
  .slide--title .inner .refs a { color: #ffffff; text-decoration: underline; }
  .slide--title { background: linear-gradient(135deg, var(--accent) 0%, var(--accent2) 100%); }
  .slide--title .kicker { color: rgba(255,255,255,0.85); }
  .slide--title h1 { -webkit-text-fill-color: #ffffff; color: #ffffff; background: none; }
  .slide--title .subtitle, .slide--title .byline { color: rgba(255,255,255,0.92); }
  .slide--title .inner .notelink a {
    background: rgba(255,255,255,0.12); color: #ffffff; border-color: rgba(255,255,255,0.5);
  }
  .slide--title .inner p { margin: 0 0 1.2rem; }
  /* In dark mode the accents are pastel, so the title-slide gradient is
     light and white ink on it is unreadable. Flip the ink to slate. */
  @media (prefers-color-scheme: dark) {
    .slide--title .inner .refs { color: rgba(15,23,42,0.9); }
    .slide--title .inner .refs a { color: #0f172a; }
    .slide--title .kicker { color: rgba(15,23,42,0.85); }
    .slide--title h1 { -webkit-text-fill-color: #0f172a; color: #0f172a; }
    .slide--title .subtitle, .slide--title .byline { color: rgba(15,23,42,0.92); }
    .slide--title .inner .notelink a {
      background: rgba(15,23,42,0.12); color: #0f172a; border-color: rgba(15,23,42,0.5);
    }
  }
  footer {
    position: fixed; bottom: 0; left: 0; right: 0;
    display: flex; align-items: center; justify-content: space-between; gap: 1rem;
    padding: 0.5rem clamp(1rem, 4vw, 3rem);
    font-size: 0.85rem; color: var(--muted);
    background: var(--footer-bg); backdrop-filter: blur(6px); z-index: 5;
  }
  footer a { color: var(--muted); text-decoration: none; font-weight: 600; }
  footer a:hover { color: var(--accent2); }
  footer .fl { display: flex; gap: 0.9rem; align-items: center; }
  footer .label { flex: 1; text-align: center; opacity: 0.85; }
  @media (max-width: 680px) { footer .label { display: none; } }
  footer .nav { display: flex; gap: 0.4rem; align-items: center; }
  footer button {
    font: inherit; cursor: pointer; background: var(--card); color: var(--text);
    border: 1px solid var(--border); border-radius: 0.5rem; padding: 0.25rem 0.7rem; line-height: 1;
  }
  footer button:hover { border-color: var(--accent2); }
  .zone { position: fixed; top: 0; bottom: 2.8rem; width: 20%; z-index: 4; cursor: pointer; }
  .zone.prev { left: 0; } .zone.next { right: 0; }
  @media print {
    .slide { display: flex !important; opacity: 1 !important; position: relative; page-break-after: always; height: 100vh; }
    footer, .zone, .progress { display: none; }
  }

  /* --- Verso-rendered content --- */
  :root { --verso-code-font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
  code.hl.lean.block {
    display: block;
    font-size: clamp(0.68rem, 1.55vw, 1rem); line-height: 1.35;
    margin: 0.5rem 0; padding: 0.8rem 1rem; white-space: pre; overflow-x: auto;
    background: var(--code-bg); border-radius: 0.5rem; color: var(--text);
  }
  .hl.lean {
    --verso-code-color: var(--text);
    --verso-code-keyword-color: #a626a4;
    --verso-code-keyword-weight: normal;
    --verso-code-const-color: #4078f2;
    --verso-code-var-color: var(--text);
    --verso-code-var-style: normal;
  }
  .hl.lean .sort.token { color: #c18401; }
  .hl.lean .literal.token, .hl.lean .number.token { color: #986801; }
  .hl.lean .string.token, .hl.lean .char.token { color: #50a14f; }
  .hl.lean .comment { color: #a0a1a7; font-style: italic; }
  @media (prefers-color-scheme: dark) {
    .hl.lean {
      --verso-code-keyword-color: #c678dd;
      --verso-code-const-color: #61afef;
    }
    .hl.lean .sort.token { color: #e5c07b; }
    .hl.lean .literal.token, .hl.lean .number.token { color: #d19a66; }
    .hl.lean .string.token, .hl.lean .char.token { color: #98c379; }
    .hl.lean .comment { color: #7f848e; }
  }
  /* Hover payloads are positioned by tippy, as in the notes. Verso's own
     stylesheet hides them until then, so nothing is suppressed here. */
  .tippy-box { font-size: clamp(0.7rem, 1.5vw, 1rem); }
  .tippy-box .hl.lean { background-color: transparent; }
  /* Proof states (tactic-state boxes) in the deck's design system.
     Verso hardcodes a white box with a gray border and sans-serif
     text; these rules follow it in the stylesheet, so at equal
     specificity they win, and the theme variables keep the box
     legible in both light and dark mode. */
  .hl.lean .tactic-state {
    background-color: var(--card);
    border: 1px solid var(--border);
    border-radius: 0.5rem;
    padding: 0.6rem 0.9rem;
    margin: 0.3rem 0;
    color: var(--text);
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
    font-size: clamp(0.68rem, 1.55vw, 1rem);
    line-height: 1.45;
    max-width: 100%;
    overflow-x: auto;
  }
  .hl.lean .tactic-state .goal-name,
  .hl.lean .hypotheses .name,
  .hl.lean .hypotheses .colon,
  .hl.lean .hypotheses .type,
  .hl.lean .conclusion .prefix,
  .hl.lean .conclusion .type {
    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    color: var(--text);
  }
  .hl.lean .goal-name::before { color: var(--muted); }
  .hl.lean .conclusion .prefix { color: var(--accent2); font-weight: 600; }
  .hl.lean .case-label:has(input[type="checkbox"])::before {
    background-color: var(--accent2);
  }
  /* Interactive highlights: Verso hardcodes light grays that erase
     the light token colors in dark mode. var(--border) is a subtle
     tint in both palettes (#e2e8f0 light, #334155 dark), and every
     token color stays readable against it. */
  @media (hover: hover) {
    .hl.lean .tactic:has(> .tactic-toggle:not(:checked)) > label:hover:not(:has(.tactic > label:hover)) {
      background-color: var(--border);
    }
    .hl.lean .token.binding-hl, .hl.lean .literal:hover, .hl.lean .token.typed:hover {
      background-color: var(--border);
      border-radius: 2px;
    }
    .hl.lean .has-info.error:hover, .hl.lean .has-info.warning:hover {
      background-color: transparent;
    }
  }
  /* The expansion pill after a tactic label. */
  .hl.lean .tactic > label::after { border-color: var(--muted); }
  .hl.lean .tactic > label:has(+ .tactic-toggle:checked)::after {
    border: 1px solid var(--accent2);
    background-color: var(--accent2);
  }
  /* An expanded state inside a column scrolls in its code block
     instead of widening the column. */
  .cols > div > code.hl.lean.block { max-width: 100%; }
  pre.hl.lean.lean-output {
    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    font-size: clamp(0.62rem, 1.4vw, 0.9rem); line-height: 1.35;
    margin: 0.4rem 0 0.8rem; padding: 0.6rem 1rem; overflow-x: auto;
    background: var(--code-bg); border-radius: 0.5rem; color: var(--muted);
  }
  /* Centred, and set off from the paragraph that introduces it. */
  table.tabular {
    border-collapse: collapse; margin: 1.4rem auto 0.8rem;
    font-size: clamp(0.8rem, 1.7vw, 1.1rem);
  }
  table.tabular th, table.tabular td {
    border: 1px solid var(--border); padding: 0.22rem 0.7rem;
    text-align: left; color: var(--text);
  }
  table.tabular th { background: var(--code-bg); }
  .slide .inner > p {
    color: var(--muted); font-size: clamp(0.9rem, 1.9vw, 1.2rem);
    line-height: 1.4; margin: 0.7rem 0 0.3rem;
  }
"##

def slideDeckJs : String := r##"
  const slides = Array.from(document.querySelectorAll('.slide'));
  const progress = document.getElementById('progress');
  const counter = document.getElementById('counter');
  let i = 0;
  function clamp(n) { return Math.max(0, Math.min(slides.length - 1, n)); }
  function render() {
    slides.forEach((s, k) => s.classList.toggle('active', k === i));
    progress.style.width = (i / (slides.length - 1) * 100) + '%';
    counter.textContent = (i + 1) + ' / ' + slides.length;
    if (location.hash !== '#' + (i + 1)) history.replaceState(null, '', '#' + (i + 1));
  }
  function go(n) { i = clamp(n); render(); }
  function next() { go(i + 1); }
  function prev() { go(i - 1); }
  document.addEventListener('keydown', (e) => {
    switch (e.key) {
      case 'ArrowRight': case 'PageDown': case ' ': next(); e.preventDefault(); break;
      case 'ArrowLeft': case 'PageUp': prev(); e.preventDefault(); break;
      case 'Home': go(0); break;
      case 'End': go(slides.length - 1); break;
      case 'f': case 'F':
        if (!document.fullscreenElement) document.documentElement.requestFullscreen();
        else document.exitFullscreen(); break;
    }
  });
  document.getElementById('znext').addEventListener('click', next);
  document.getElementById('zprev').addEventListener('click', prev);
  document.getElementById('bnext').addEventListener('click', next);
  document.getElementById('bprev').addEventListener('click', prev);
  document.getElementById('bstart').addEventListener('click', (e) => { e.preventDefault(); go(0); });

  // Click to advance, except on links, buttons, form controls, and
  // Verso-rendered code (whose tactic-state toggles are clickable).
  document.getElementById('deck').addEventListener('click', (e) => {
    if (e.target.closest('a, button, label, input, code.hl.lean')) return;
    next();
  });

  // Mouse-wheel / trackpad navigation, yielding to in-slide scroll when content overflows.
  let wheelLock = false;
  window.addEventListener('wheel', (e) => {
    const dir = e.deltaY > 0 ? 1 : -1;
    const inner = slides[i].querySelector('.inner');
    if (inner) {
      const canScroll = inner.scrollHeight > inner.clientHeight + 1;
      const atTop = inner.scrollTop <= 0;
      const atBottom = inner.scrollTop + inner.clientHeight >= inner.scrollHeight - 1;
      if (canScroll && ((dir > 0 && !atBottom) || (dir < 0 && !atTop))) return;
    }
    e.preventDefault();
    if (wheelLock || Math.abs(e.deltaY) < 8) return;
    wheelLock = true;
    setTimeout(() => { wheelLock = false; }, 500);
    if (dir > 0) next(); else prev();
  }, { passive: false });

  const start = parseInt((location.hash || '').slice(1), 10);
  if (!isNaN(start)) i = clamp(start - 1);
  render();
"##

/-! ## Emission -/

open Verso.Output.Html in
/--
Renders the traversed document as a single-file slide deck. The
document title and intro blocks become the title slide; each
top-level section becomes one slide.
-/
def emitSlideDeck (config : RenderConfig) (deck : SlideDeck)
    (text : Part Manual) (state : TraverseState) : EmitM Unit := do
  let dir := config.destination
  ensureDir dir
  let remotes ← updateRemotes false config.remoteConfigFile (fun _ => pure ())
  let opts : Verso.Doc.Html.Options := {}
  let ctxt : Manual.TraverseContext := {}
  let definitionIds := state.definitionIds ctxt
  let act : StateT (Verso.Code.Hover.State Html)
      (ReaderT AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))) Html := do
    let render {α} [Verso.Doc.Html.ToHtml Manual
          (ReaderT AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))) α]
        (ctxt : Manual.TraverseContext) (x : α) :=
      Manual.toHtml opts ctxt state definitionIds {} {} x
    let titleHtml ← Html.seq <$> text.title.mapM (render ctxt)
    let introHtml ← text.content.mapM (render ctxt)
    let intro := introHtml.mapIdx fun i h =>
      let cls := deck.introClasses[i]? |>.getD "extra"
      {{<div class={{cls}}>{{h}}</div>}}
    let titleSlide := {{
      <section class="slide slide--title">
        <div class="inner">
          <div class="kicker">{{deck.kicker}}</div>
          <h1>{{titleHtml}}</h1>
          {{intro}}
        </div>
      </section>
    }}
    let mut slides := #[titleSlide]
    for p in text.subParts do
      let ctxt' := ctxt.inPart p
      let hd ← Html.seq <$> p.title.mapM (render ctxt')
      let bd ← Html.seq <$> p.content.mapM (render ctxt')
      slides := slides.push {{
        <section class="slide"><div class="inner"><h2>{{hd}}</h2>{{bd}}</div></section>
      }}
    let counter := s!"1 / {slides.size}"
    let versoCss := String.join (state.extraCss.toArray.map (·.css ++ "\n")).toList
    -- The hover payloads of the code rendered above are in the state
    -- once every slide has been rendered, so the page is assembled here.
    let docJson := toString (← get).dedup.docJson
    -- A literal `</script` inside the JSON would end the script element.
    let docJsonSafe := docJson.replace "</" "<\\/"
    let hoverJs := Verso.Code.highlightingJs
      s!"Promise.resolve({docJsonSafe})"
    let mkLink cls (l : String × String) : Html :=
      {{<a class={{(cls : String)}} href={{l.1}}>{{l.2}}</a>}}
    let notesLink := deck.notesLink.map (mkLink "back") |>.getD .empty
    let prevLink := deck.prevLink.map (mkLink "jump") |>.getD .empty
    let nextLink := deck.nextLink.map (mkLink "jump") |>.getD .empty
    pure {{
      <html lang={{deck.htmlLang}}>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <title>{{deck.pageTitle}}</title>
          <style>{{Html.text false Verso.Output.Html.«verso-vars.css»}}</style>
          <style>{{Html.text false versoCss}}</style>
          <style>{{Html.text false Verso.Code.Highlighted.WebAssets.tippy.border.css}}</style>
          <style>{{Html.text false slideDeckCss}}</style>
        </head>
        <body>
          <div class="progress" id="progress"></div>
          <div class="deck" id="deck">{{slides}}</div>
          <div class="zone prev" id="zprev" "aria-hidden"="true"></div>
          <div class="zone next" id="znext" "aria-hidden"="true"></div>
          <footer>
            <span class="fl">
              {{notesLink}}
              <a class="jump" id="bstart" href="#1">{{deck.startLabel}}</a>
              {{prevLink}}
            </span>
            <span class="label">{{deck.label}}</span>
            <span class="nav">
              {{nextLink}}
              <button id="bprev" "aria-label"={{deck.prevSlideLabel}}>"‹"</button>
              <span id="counter">{{counter}}</span>
              <button id="bnext" "aria-label"={{deck.nextSlideLabel}}>"›"</button>
            </span>
          </footer>
          <script>{{Html.text false slideDeckJs}}</script>
          <script>{{Html.text false Verso.Code.Highlighted.WebAssets.popper}}</script>
          <script>{{Html.text false Verso.Code.Highlighted.WebAssets.tippy}}</script>
          <script>{{Html.text false hoverJs}}</script>
        </body>
      </html>
    }}
  let (html, _) ← act.run .empty |>.run remotes
  IO.FS.writeFile (dir / deck.fileName) (Html.doctype ++ html.asString)

/--
Entry point for slide-deck builds. Accepts `--output DIR`, runs the
Manual-genre traversal without splitting into pages for each deck,
and emits the deck files into `DIR`.
-/
def slidesMain (decks : List (Part Manual × SlideDeck))
    (extensionImpls : ExtensionImpls := by exact extension_impls%)
    (options : List String)
    (config : RenderConfig := {}) : IO UInt32 :=
  go extensionImpls
where
  opts (cfg : RenderConfig) : List String → IO RenderConfig
    | ("--output" :: dir :: more) => opts { cfg with destination := dir } more
    | (other :: _) => throw <| IO.userError s!"Unknown option {other}"
    | [] => pure cfg
  go (extensionImpls : ExtensionImpls) : IO UInt32 := do
    let cfg ← opts config options
    runWithLogger <| flip ReaderT.run extensionImpls do
      for (doc, deck) in decks do
        let (doc', state) ← Manual.traverse doc { cfg.toConfig with htmlDepth := 0 }
        emitSlideDeck cfg deck doc' state
