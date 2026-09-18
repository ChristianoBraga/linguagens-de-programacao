/-
Entry point for the Portuguese slide-deck build.
Run with: lake exe slides-pt --output _out/slides-pt
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Lecture01
import Lectures.SlidesPt.Lecture02
import Lectures.SlidesPt.Lecture03
import Lectures.SlidesPt.Lecture04

open Verso Doc
open Verso.Genre Manual

open Lectures

def aula1Deck : SlideDeck where
  fileName := "lecture-1.pt.html"
  pageTitle := "Aula 1: Linguagens e Paradigmas · Slides"
  htmlLang := "pt"
  kicker := "Aula 1 · Linguagens de Programação"
  label := "Aula 1 · Linguagens e Paradigmas"
  notesLink := some ("../pt/Aula-1___-Linguagens-e-Paradigmas/", "↩ Notas")
  nextLink := some ("lecture-2.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula2Deck : SlideDeck where
  fileName := "lecture-2.pt.html"
  pageTitle := "Aula 2: Sintaxe · Slides"
  htmlLang := "pt"
  kicker := "Aula 2 · Linguagens de Programação"
  label := "Aula 2 · Sintaxe"
  notesLink := some ("../pt/Aula-2___-Sintaxe/", "↩ Notas")
  prevLink := some ("lecture-1.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-3.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula3Deck : SlideDeck where
  fileName := "lecture-3.pt.html"
  pageTitle := "Aula 3: Semântica · Slides"
  htmlLang := "pt"
  kicker := "Aula 3 · Linguagens de Programação"
  label := "Aula 3 · Semântica"
  notesLink := some ("../pt/Aula-3___-Sem___ntica/", "↩ Notas")
  prevLink := some ("lecture-2.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-4.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula4Deck : SlideDeck where
  fileName := "lecture-4.pt.html"
  pageTitle := "Aula 4: Processadores de Linguagens · Slides"
  htmlLang := "pt"
  kicker := "Aula 4 · Linguagens de Programação"
  label := "Aula 4 · Processadores de Linguagens"
  notesLink := some ("../pt/Aula-4___-Processadores-de-Linguagens/", "↩ Notas")
  prevLink := some ("lecture-3.pt.html", "‹ Aula anterior")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesPt.Lecture01), aula1Deck),
   ((%doc Lectures.SlidesPt.Lecture02), aula2Deck),
   ((%doc Lectures.SlidesPt.Lecture03), aula3Deck),
   ((%doc Lectures.SlidesPt.Lecture04), aula4Deck)])
