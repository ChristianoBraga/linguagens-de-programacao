/-
Syntax-highlighting colors for Lean code blocks, injected into every page's
`head` via the `extraHead` field of the render configuration. Verso exposes
CSS custom properties for keyword, constant, and variable tokens; the other
token kinds get direct rules with higher specificity than the defaults.
Palette follows the One Light theme.
-/

import VersoManual

open Verso.Output Html

namespace Lectures

def codeHighlightCss : String := "
.hl.lean {
  --verso-code-keyword-color: #a626a4;
  --verso-code-const-color: #4078f2;
}
.hl.lean .sort.token { color: #c18401; }
.hl.lean .literal.token, .hl.lean .number.token { color: #986801; }
.hl.lean .string.token, .hl.lean .char.token { color: #50a14f; }
.hl.lean .comment { color: #a0a1a7; font-style: italic; }
"

/--
Site theme matching the landing page in `site/index.html`. Palette is
indigo `#1e3a8a` to teal `#0d9488` on slate, with the header carrying the
landing gradient.
-/
def themeCss : String := r#"
:root {
  --verso-text-color: #0f172a;
  --verso-structure-color: #0f172a;
  --verso-code-color: #0f172a;
  --verso-toc-background-color: #f8fafc;
  --verso-burger-toc-hidden-color: #ffffff;
}
header {
  background: linear-gradient(135deg, #1e3a8a 0%, #0d9488 100%);
  box-shadow: 0 1px 6px rgba(15, 23, 42, 0.35);
}
.header-title h1 { color: #ffffff; }
#logo img { padding: 0.4rem 0 0.4rem 0.6rem; box-sizing: border-box; }

body { background: #f8fafc; }

/* Content as a landing-style card */
.content-wrapper {
  background: #ffffff;
  border: 1px solid #e2e8f0;
  border-radius: 1.25rem;
  box-shadow: 0 10px 30px rgba(15, 23, 42, 0.06);
  padding: 2rem 2.5rem;
  margin: 1.5rem;
}
@media screen and (max-width: 700px) {
  .content-wrapper { padding: 1rem; margin: 0.5rem; border-radius: 0.75rem; }
}

/* Typography */
main section p, main section li, main section dd { color: #334155; }
main section strong { color: #0f172a; }
.content-wrapper > section > h1 {
  padding-bottom: 0.4rem;
  border-bottom: 3px solid;
  border-image: linear-gradient(90deg, #1e3a8a, #0d9488) 1;
}

/* Verso bug workaround: main is a query container, and style containment
   (implied by container-type) keeps CSS counters from accumulating across
   sibling subtrees, so every margin note renders as 1. The numbers instead
   come from data-note-num attributes set by the script below. */
.marginalia { counter-increment: none; }
.marginalia .note { counter-increment: none; }
.marginalia::after { content: attr(data-note-num); }
.marginalia .note::before { content: attr(data-note-num) "."; }

/* Margin notes as small cards on the slate background */
.marginalia .note {
  background: #ffffff;
  border: 1px solid #e2e8f0;
  border-radius: 0.75rem;
  box-shadow: 0 4px 12px rgba(15, 23, 42, 0.05);
}
main section a { color: #1e3a8a; }
main section a:hover { color: #0d9488; }

/* Code blocks as slate panels */
code.hl.lean.block {
  background: #f8fafc;
  border: 1px solid #e2e8f0;
  border-radius: 0.75rem;
  padding: 1rem 1.25rem;
  overflow-x: auto;
}

/* Tables */
table.tabular th, table.tabular td {
  border: 1px solid #e2e8f0;
  padding: 0.4rem 0.9rem;
}
table.tabular th { background: #f1f5f9; color: #0f172a; }
table.tabular { border-collapse: collapse; }

/* Table of contents */
#toc { border-right: 1px solid #e2e8f0; }
#toc a { color: #475569; }
#toc a:hover { color: #0d9488; }
#toc tr.current a { color: #1e3a8a; font-weight: 600; }

/* Previous/next navigation */
.prev-next-buttons > * { color: #1e3a8a; }
"#

/--
Numbers the margin notes on each page, replacing Verso's CSS counters,
which do not accumulate inside the `main` query container.
-/
def marginNoteNumberJs : String := "
document.addEventListener('DOMContentLoaded', () => {
  let i = 0;
  for (const m of document.querySelectorAll('main .marginalia')) {
    i++;
    m.dataset.noteNum = String(i);
    const note = m.querySelector('.note');
    if (note) { note.dataset.noteNum = String(i); }
  }
});
"

def codeHighlightHead : Array Verso.Output.Html :=
  #[{{<style>{{Verso.Output.Html.text false codeHighlightCss}}</style>}},
    {{<style>{{Verso.Output.Html.text false themeCss}}</style>}},
    {{<script>{{Verso.Output.Html.text false marginNoteNumberJs}}</script>}}]
