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
import Lectures.SlidesEn.Lecture05
import Lectures.SlidesEn.Lecture06
import Lectures.SlidesEn.Lecture07
import Lectures.SlidesEn.Lecture08
import Lectures.SlidesEn.Lecture09
import Lectures.SlidesEn.Lecture10
import Lectures.SlidesEn.Lecture11
import Lectures.SlidesEn.Lecture12
import Lectures.SlidesEn.Lecture13
import Lectures.SlidesEn.Lecture14
import Lectures.SlidesEn.Lecture15
import Lectures.SlidesEn.Lecture16

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
  nextLink := some ("lecture-5.en.html", "Next lecture ›")

def lecture5Deck : SlideDeck where
  fileName := "lecture-5.en.html"
  pageTitle := "Lecture 5: Values and Types · Slides"
  htmlLang := "en"
  kicker := "Lecture 5 · Programming Languages"
  label := "Lecture 5 · Values and Types"
  notesLink := some ("../en/Lecture-5___-Values-and-Types/", "↩ Notes")
  prevLink := some ("lecture-4.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-6.en.html", "Next lecture ›")

def lecture6Deck : SlideDeck where
  fileName := "lecture-6.en.html"
  pageTitle := "Lecture 6: Composite Types · Slides"
  htmlLang := "en"
  kicker := "Lecture 6 · Programming Languages"
  label := "Lecture 6 · Composite Types"
  notesLink := some ("../en/Lecture-6___-Composite-Types/", "↩ Notes")
  prevLink := some ("lecture-5.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-7.en.html", "Next lecture ›")

def lecture7Deck : SlideDeck where
  fileName := "lecture-7.en.html"
  pageTitle := "Lecture 7: Recursive Types and Vectors · Slides"
  htmlLang := "en"
  kicker := "Lecture 7 · Programming Languages"
  label := "Lecture 7 · Recursive Types and Vectors"
  notesLink := some ("../en/Lecture-7___-Recursive-Types-and-Vectors/", "↩ Notes")
  prevLink := some ("lecture-6.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-8.en.html", "Next lecture ›")

def lecture8Deck : SlideDeck where
  fileName := "lecture-8.en.html"
  pageTitle := "Lecture 8: Expressions · Slides"
  htmlLang := "en"
  kicker := "Lecture 8 · Programming Languages"
  label := "Lecture 8 · Expressions"
  notesLink := some ("../en/Lecture-8___-Expressions/", "↩ Notes")
  prevLink := some ("lecture-7.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-9.en.html", "Next lecture ›")

def lecture9Deck : SlideDeck where
  fileName := "lecture-9.en.html"
  pageTitle := "Lecture 9: Variables and Storage · Slides"
  htmlLang := "en"
  kicker := "Lecture 9 · Programming Languages"
  label := "Lecture 9 · Variables and Storage"
  notesLink := some ("../en/Lecture-9___-Variables-and-Storage/", "↩ Notes")
  prevLink := some ("lecture-8.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-10.en.html", "Next lecture ›")

def lecture10Deck : SlideDeck where
  fileName := "lecture-10.en.html"
  pageTitle := "Lecture 10: References and Aliasing · Slides"
  htmlLang := "en"
  kicker := "Lecture 10 · Programming Languages"
  label := "Lecture 10 · References and Aliasing"
  notesLink := some ("../en/Lecture-10___-References-and-Aliasing/", "↩ Notes")
  prevLink := some ("lecture-9.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-11.en.html", "Next lecture ›")

def lecture11Deck : SlideDeck where
  fileName := "lecture-11.en.html"
  pageTitle := "Lecture 11: Commands and Control · Slides"
  htmlLang := "en"
  kicker := "Lecture 11 · Programming Languages"
  label := "Lecture 11 · Commands and Control"
  notesLink := some ("../en/Lecture-11___-Commands-and-Control/", "↩ Notes")
  prevLink := some ("lecture-10.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-12.en.html", "Next lecture ›")

def lecture12Deck : SlideDeck where
  fileName := "lecture-12.en.html"
  pageTitle := "Lecture 12: Expressions with Side Effects · Slides"
  htmlLang := "en"
  kicker := "Lecture 12 · Programming Languages"
  label := "Lecture 12 · Expressions with Side Effects"
  notesLink := some ("../en/Lecture-12___-Expressions-with-Side-Effects/", "↩ Notes")
  prevLink := some ("lecture-11.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-13.en.html", "Next lecture ›")

def lecture13Deck : SlideDeck where
  fileName := "lecture-13.en.html"
  pageTitle := "Lecture 13: Functions and Call by Value · Slides"
  htmlLang := "en"
  kicker := "Lecture 13 · Programming Languages"
  label := "Lecture 13 · Functions and Call by Value"
  notesLink := some ("../en/Lecture-13___-Functions-and-Call-by-Value/", "↩ Notes")
  prevLink := some ("lecture-12.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-14.en.html", "Next lecture ›")

def lecture14Deck : SlideDeck where
  fileName := "lecture-14.en.html"
  pageTitle := "Lecture 14: Call by Reference · Slides"
  htmlLang := "en"
  kicker := "Lecture 14 · Programming Languages"
  label := "Lecture 14 · Call by Reference"
  notesLink := some ("../en/Lecture-14___-Call-by-Reference/", "↩ Notes")
  prevLink := some ("lecture-13.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-15.en.html", "Next lecture ›")

def lecture15Deck : SlideDeck where
  fileName := "lecture-15.en.html"
  pageTitle := "Lecture 15: Lambdas and Closures · Slides"
  htmlLang := "en"
  kicker := "Lecture 15 · Programming Languages"
  label := "Lecture 15 · Lambdas and Closures"
  notesLink := some ("../en/Lecture-15___-Lambdas-and-Closures/", "↩ Notes")
  prevLink := some ("lecture-14.en.html", "‹ Previous lecture")
  nextLink := some ("lecture-16.en.html", "Next lecture ›")

def lecture16Deck : SlideDeck where
  fileName := "lecture-16.en.html"
  pageTitle := "Lecture 16: Parameter Evaluation · Slides"
  htmlLang := "en"
  kicker := "Lecture 16 · Programming Languages"
  label := "Lecture 16 · Parameter Evaluation"
  notesLink := some ("../en/Lecture-16___-Parameter-Evaluation/", "↩ Notes")
  prevLink := some ("lecture-15.en.html", "‹ Previous lecture")

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesEn.Lecture01), lecture1Deck),
   ((%doc Lectures.SlidesEn.Lecture02), lecture2Deck),
   ((%doc Lectures.SlidesEn.Lecture03), lecture3Deck),
   ((%doc Lectures.SlidesEn.Lecture04), lecture4Deck),
   ((%doc Lectures.SlidesEn.Lecture05), lecture5Deck),
   ((%doc Lectures.SlidesEn.Lecture06), lecture6Deck),
   ((%doc Lectures.SlidesEn.Lecture07), lecture7Deck),
   ((%doc Lectures.SlidesEn.Lecture08), lecture8Deck),
   ((%doc Lectures.SlidesEn.Lecture09), lecture9Deck),
   ((%doc Lectures.SlidesEn.Lecture10), lecture10Deck),
   ((%doc Lectures.SlidesEn.Lecture11), lecture11Deck),
   ((%doc Lectures.SlidesEn.Lecture12), lecture12Deck),
   ((%doc Lectures.SlidesEn.Lecture13), lecture13Deck),
   ((%doc Lectures.SlidesEn.Lecture14), lecture14Deck),
   ((%doc Lectures.SlidesEn.Lecture15), lecture15Deck),
   ((%doc Lectures.SlidesEn.Lecture16), lecture16Deck)])
