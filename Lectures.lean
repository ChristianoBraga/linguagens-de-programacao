/-
Root module of the `Lectures` library.

This module deliberately imports nothing. The English notes
(`Lectures.En`) and the Portuguese notes (`Lectures.Pt`) share the
same internal declaration names, since their Lean code is identical,
so the two trees cannot be elaborated into one environment. The
project is built as four independent single-language targets:

  lake exe lectures-en   -- English notes    (root LecturesEnMain)
  lake exe lectures-pt   -- Portuguese notes (root LecturesPtMain)
  lake exe slides-en     -- English slides   (root SlidesEnMain)
  lake exe slides-pt     -- Portuguese slides (root SlidesPtMain)

A bare `lake build` builds all four, which together compile every
module in the project.
-/
