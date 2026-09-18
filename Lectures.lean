/-
Root module of the `Lectures` library.

This module deliberately imports nothing. The project is built as
independent single-language targets, each of which loads one document
tree:

  lake exe lectures-pt   -- Portuguese notes  (root LecturesPtMain)
  lake exe slides-pt     -- Portuguese slides (root SlidesPtMain)

A bare `lake build` builds both, which together compile every module in
the project.
-/
