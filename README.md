# Programming Languages — Lecture Notes

Lecture notes for the course *09022, Linguagens de Programação* (IME, Computer
Engineering, 5th year), written in [Verso](https://github.com/leanprover/verso).

**Published site:** <https://christianobraga.github.io/linguagens-de-programacao/>
([English](https://christianobraga.github.io/linguagens-de-programacao/en/) ·
[Português](https://christianobraga.github.io/linguagens-de-programacao/pt/)).
Every push to `main` rebuilds and redeploys the site via GitHub Actions
(`.github/workflows/deploy.yml`); the landing page lives in `site/`.
The notes exist in two languages, with parallel document trees:

- `Lectures/En/` — English lectures, root document `Lectures/En.lean`
- `Lectures/Pt/` — Portuguese lectures, root document `Lectures/Pt.lean`
- `Lectures/SlidesEn/`, `Lectures/SlidesPt/` — one slide deck per lecture

Lean code is identical in both versions; only the prose differs.

The course follows Watt's structure and presents each concept as a construction
of Core C++, a well behaved subset of C++17, with typing and evaluation rules in
natural semantics and their implementation in Lean 4. The Core C++ interpreter,
[github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp),
is a dependency of this project, and every Lean example in the notes runs it at
build time, with the output checked by Verso. `Lectures/Meta/` holds the
machinery shared with the Formal Software Verification course (labels and
counters, footnotes, `savedLean` blocks, theme, slide decks).

## Building

```
lake exe lectures-en --output _out/en
lake exe lectures-pt --output _out/pt
lake exe slides-en --output _out/slides-en
lake exe slides-pt --output _out/slides-pt
```

Verso's HTML must be served, not opened from the filesystem. `./preview.sh`
assembles the site exactly as `deploy.sh` does and serves it at
`http://localhost:8000/`.

## Adding a lecture

1. Create `Lectures/En/LectureNN.lean` and `Lectures/Pt/LectureNN.lean`, and the
   decks `Lectures/SlidesEn/LectureNN.lean` and `Lectures/SlidesPt/LectureNN.lean`,
   starting from lecture 1 as a model.
2. Import and `{include 0 ...}` them in `Lectures/En.lean` and `Lectures/Pt.lean`,
   and register the decks in `SlidesEnMain.lean` and `SlidesPtMain.lean`.
3. Put exercises with Lean code in `savedLean -keep` blocks so they are extracted
   to `html-multi/example-code/`.
