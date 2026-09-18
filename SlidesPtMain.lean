/-
Entry point for the Portuguese slide-deck build.
Run with: lake exe slides-pt --output _out/slides-pt
-/

import VersoManual
import Lectures.Meta.SlideDeck
import Lectures.SlidesPt.Aula01
import Lectures.SlidesPt.Aula02
import Lectures.SlidesPt.Aula03
import Lectures.SlidesPt.Aula04

open Verso Doc
open Verso.Genre Manual

open Lectures

def aula1Deck : SlideDeck where
  fileName := "aula-1.pt.html"
  pageTitle := "Aula 1: Linguagens e Paradigmas · Slides"
  htmlLang := "pt"
  kicker := "Aula 1 · Linguagens de Programação"
  label := "Aula 1 · Linguagens e Paradigmas"
  notesLink := some ("../pt/Aula-1___-Linguagens-e-Paradigmas/", "↩ Notas")
  nextLink := some ("aula-2.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula2Deck : SlideDeck where
  fileName := "aula-2.pt.html"
  pageTitle := "Aula 2: Sintaxe · Slides"
  htmlLang := "pt"
  kicker := "Aula 2 · Linguagens de Programação"
  label := "Aula 2 · Sintaxe"
  notesLink := some ("../pt/Aula-2___-Sintaxe/", "↩ Notas")
  prevLink := some ("aula-1.pt.html", "‹ Aula anterior")
  nextLink := some ("aula-3.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula3Deck : SlideDeck where
  fileName := "aula-3.pt.html"
  pageTitle := "Aula 3: Semântica · Slides"
  htmlLang := "pt"
  kicker := "Aula 3 · Linguagens de Programação"
  label := "Aula 3 · Semântica"
  notesLink := some ("../pt/Aula-3___-Sem___ntica/", "↩ Notas")
  prevLink := some ("aula-2.pt.html", "‹ Aula anterior")
  nextLink := some ("aula-4.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula4Deck : SlideDeck where
  fileName := "aula-4.pt.html"
  pageTitle := "Aula 4: Processadores de Linguagens · Slides"
  htmlLang := "pt"
  kicker := "Aula 4 · Linguagens de Programação"
  label := "Aula 4 · Processadores de Linguagens"
  notesLink := some ("../pt/Aula-4___-Processadores-de-Linguagens/", "↩ Notas")
  prevLink := some ("aula-3.pt.html", "‹ Aula anterior")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesPt.Aula01), aula1Deck),
   ((%doc Lectures.SlidesPt.Aula02), aula2Deck),
   ((%doc Lectures.SlidesPt.Aula03), aula3Deck),
   ((%doc Lectures.SlidesPt.Aula04), aula4Deck)])
