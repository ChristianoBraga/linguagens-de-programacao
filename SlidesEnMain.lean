/-
Entry point for the English slide-deck build.
Run with: lake exe slides-en --output _out/slides-en
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesEn.Lecture01
import Lectures.SlidesEn.Lecture02
import Lectures.SlidesEn.Lecture03
import Lectures.SlidesEn.Lecture04

open Verso Doc
open Verso.Genre Manual

open Lectures

def lecture1Deck : SlideDeck where
  fileName := "lecture-1.en.html"
  pageTitle := "Lecture 1: Languages and Paradigms · Slides"
  htmlLang := "en"
  kicker := "Lecture 1 · Programming Languages"
  label := "Lecture 1 · Languages and Paradigms"
  notesLink := some ("../en/Lecture-1___-Languages-and-Paradigms/", "↩ Notes")
  nextLink := some ("lecture-2.en.html", "Next lecture ›")

def lecture2Deck : SlideDeck where
  fileName := "lecture-2.en.html"
  pageTitle := "Lecture 2: Syntax · Slides"
  htmlLang := "en"
  kicker := "Lecture 2 · Programming Languages"
  label := "Lecture 2 · Syntax"
  notesLink := some ("../en/Lecture-2___-Syntax/", "↩ Notes")
  prevLink := some ("lecture-1.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-3.en.html", "Next lecture ›")

def lecture3Deck : SlideDeck where
  fileName := "lecture-3.en.html"
  pageTitle := "Lecture 3: Semantics · Slides"
  htmlLang := "en"
  kicker := "Lecture 3 · Programming Languages"
  label := "Lecture 3 · Semantics"
  notesLink := some ("../en/Lecture-3___-Semantics/", "↩ Notes")
  prevLink := some ("lecture-2.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-4.en.html", "Next lecture ›")

def lecture4Deck : SlideDeck where
  fileName := "lecture-4.en.html"
  pageTitle := "Lecture 4: Language Processors · Slides"
  htmlLang := "en"
  kicker := "Lecture 4 · Programming Languages"
  label := "Lecture 4 · Language Processors"
  notesLink := some ("../en/Lecture-4___-Language-Processors/", "↩ Notes")
  prevLink := some ("lecture-3.en.html", "‹ Previous lecture")

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesEn.Lecture01), lecture1Deck),
   ((%doc Lectures.SlidesEn.Lecture02), lecture2Deck),
   ((%doc Lectures.SlidesEn.Lecture03), lecture3Deck),
   ((%doc Lectures.SlidesEn.Lecture04), lecture4Deck)])
