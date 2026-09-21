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
import Lectures.SlidesPt.Lecture05
import Lectures.SlidesPt.Lecture06
import Lectures.SlidesPt.Lecture07
import Lectures.SlidesPt.Lecture08
import Lectures.SlidesPt.Lecture09
import Lectures.SlidesPt.Lecture10
import Lectures.SlidesPt.Lecture11
import Lectures.SlidesPt.Lecture12
import Lectures.SlidesPt.Lecture13
import Lectures.SlidesPt.Lecture14
import Lectures.SlidesPt.Lecture15
import Lectures.SlidesPt.Lecture16
import Lectures.SlidesPt.Lecture17
import Lectures.SlidesPt.Lecture18
import Lectures.SlidesPt.Lecture19
import Lectures.SlidesPt.Lecture20
import Lectures.SlidesPt.Lecture21
import Lectures.SlidesPt.Lecture22
import Lectures.SlidesPt.Lecture23
import Lectures.SlidesPt.Lecture24
import Lectures.SlidesPt.Lecture25
import Lectures.SlidesPt.Lecture26
import Lectures.SlidesPt.Lecture27
import Lectures.SlidesPt.Lecture28
import Lectures.SlidesPt.Lecture29

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
  nextLink := some ("lecture-5.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula5Deck : SlideDeck where
  fileName := "lecture-5.pt.html"
  pageTitle := "Aula 5: Valores e Tipos · Slides"
  htmlLang := "pt"
  kicker := "Aula 5 · Linguagens de Programação"
  label := "Aula 5 · Valores e Tipos"
  notesLink := some ("../pt/Aula-5___-Valores-e-Tipos/", "↩ Notas")
  prevLink := some ("lecture-4.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-6.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula6Deck : SlideDeck where
  fileName := "lecture-6.pt.html"
  pageTitle := "Aula 6: Tipos Compostos · Slides"
  htmlLang := "pt"
  kicker := "Aula 6 · Linguagens de Programação"
  label := "Aula 6 · Tipos Compostos"
  notesLink := some ("../pt/Aula-6___-Tipos-Compostos/", "↩ Notas")
  prevLink := some ("lecture-5.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-7.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula7Deck : SlideDeck where
  fileName := "lecture-7.pt.html"
  pageTitle := "Aula 7: Tipos Recursivos e Vetores · Slides"
  htmlLang := "pt"
  kicker := "Aula 7 · Linguagens de Programação"
  label := "Aula 7 · Tipos Recursivos e Vetores"
  notesLink := some ("../pt/Aula-7___-Tipos-Recursivos-e-Vetores/", "↩ Notas")
  prevLink := some ("lecture-6.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-8.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula8Deck : SlideDeck where
  fileName := "lecture-8.pt.html"
  pageTitle := "Aula 8: Expressões · Slides"
  htmlLang := "pt"
  kicker := "Aula 8 · Linguagens de Programação"
  label := "Aula 8 · Expressões"
  notesLink := some ("../pt/Aula-8___-Express___es/", "↩ Notas")
  prevLink := some ("lecture-7.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-9.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula9Deck : SlideDeck where
  fileName := "lecture-9.pt.html"
  pageTitle := "Aula 9: Variáveis e Armazenamento · Slides"
  htmlLang := "pt"
  kicker := "Aula 9 · Linguagens de Programação"
  label := "Aula 9 · Variáveis e Armazenamento"
  notesLink := some ("../pt/Aula-9___-Vari___veis-e-Armazenamento/", "↩ Notas")
  prevLink := some ("lecture-8.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-10.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula10Deck : SlideDeck where
  fileName := "lecture-10.pt.html"
  pageTitle := "Aula 10: Referências e Apelidos · Slides"
  htmlLang := "pt"
  kicker := "Aula 10 · Linguagens de Programação"
  label := "Aula 10 · Referências e Apelidos"
  notesLink := some ("../pt/Aula-10___-Refer___ncias-e-Apelidos/", "↩ Notas")
  prevLink := some ("lecture-9.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-11.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula11Deck : SlideDeck where
  fileName := "lecture-11.pt.html"
  pageTitle := "Aula 11: Comandos e Controle · Slides"
  htmlLang := "pt"
  kicker := "Aula 11 · Linguagens de Programação"
  label := "Aula 11 · Comandos e Controle"
  notesLink := some ("../pt/Aula-11___-Comandos-e-Controle/", "↩ Notas")
  prevLink := some ("lecture-10.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-12.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula12Deck : SlideDeck where
  fileName := "lecture-12.pt.html"
  pageTitle := "Aula 12: Expressões com Efeitos Colaterais · Slides"
  htmlLang := "pt"
  kicker := "Aula 12 · Linguagens de Programação"
  label := "Aula 12 · Expressões com Efeitos Colaterais"
  notesLink := some ("../pt/Aula-12___-Express___es-com-Efeitos-Colaterais/", "↩ Notas")
  prevLink := some ("lecture-11.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-13.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula13Deck : SlideDeck where
  fileName := "lecture-13.pt.html"
  pageTitle := "Aula 13: Funções e Passagem por Valor · Slides"
  htmlLang := "pt"
  kicker := "Aula 13 · Linguagens de Programação"
  label := "Aula 13 · Funções e Passagem por Valor"
  notesLink := some ("../pt/Aula-13___-Fun______es-e-Passagem-por-Valor/", "↩ Notas")
  prevLink := some ("lecture-12.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-14.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula14Deck : SlideDeck where
  fileName := "lecture-14.pt.html"
  pageTitle := "Aula 14: Passagem por Referência · Slides"
  htmlLang := "pt"
  kicker := "Aula 14 · Linguagens de Programação"
  label := "Aula 14 · Passagem por Referência"
  notesLink := some ("../pt/Aula-14___-Passagem-por-Refer___ncia/", "↩ Notas")
  prevLink := some ("lecture-13.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-15.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula15Deck : SlideDeck where
  fileName := "lecture-15.pt.html"
  pageTitle := "Aula 15: Lambdas e Closures · Slides"
  htmlLang := "pt"
  kicker := "Aula 15 · Linguagens de Programação"
  label := "Aula 15 · Lambdas e Closures"
  notesLink := some ("../pt/Aula-15___-Lambdas-e-Closures/", "↩ Notas")
  prevLink := some ("lecture-14.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-16.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula16Deck : SlideDeck where
  fileName := "lecture-16.pt.html"
  pageTitle := "Aula 16: Avaliação de Parâmetros · Slides"
  htmlLang := "pt"
  kicker := "Aula 16 · Linguagens de Programação"
  label := "Aula 16 · Avaliação de Parâmetros"
  notesLink := some ("../pt/Aula-16___-Avalia______o-de-Par___metros/", "↩ Notas")
  prevLink := some ("lecture-15.pt.html", "‹ Aula anterior")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"
  nextLink := some ("lecture-17.pt.html", "Próxima aula ›")

def aula17Deck : SlideDeck where
  fileName := "lecture-17.pt.html"
  pageTitle := "Aula 17: Tipos Abstratos de Dados · Slides"
  htmlLang := "pt"
  kicker := "Aula 17 · Linguagens de Programação"
  label := "Aula 17 · Tipos Abstratos de Dados"
  notesLink := some ("../pt/Aula-17___-Tipos-Abstratos-de-Dados/", "↩ Notas")
  prevLink := some ("lecture-16.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-18.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula18Deck : SlideDeck where
  fileName := "lecture-18.pt.html"
  pageTitle := "Aula 18: Objetos e Classes · Slides"
  htmlLang := "pt"
  kicker := "Aula 18 · Linguagens de Programação"
  label := "Aula 18 · Objetos e Classes"
  notesLink := some ("../pt/Aula-18___-Objetos-e-Classes/", "↩ Notas")
  prevLink := some ("lecture-17.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-19.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula19Deck : SlideDeck where
  fileName := "lecture-19.pt.html"
  pageTitle := "Aula 19: Herança e Despacho · Slides"
  htmlLang := "pt"
  kicker := "Aula 19 · Linguagens de Programação"
  label := "Aula 19 · Herança e Despacho"
  notesLink := some ("../pt/Aula-19___-Heran___a-e-Despacho/", "↩ Notas")
  prevLink := some ("lecture-18.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-20.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula20Deck : SlideDeck where
  fileName := "lecture-20.pt.html"
  pageTitle := "Aula 20: Orientação a Objetos · Slides"
  htmlLang := "pt"
  kicker := "Aula 20 · Linguagens de Programação"
  label := "Aula 20 · Orientação a Objetos"
  notesLink := some ("../pt/Aula-20___-Orienta______o-a-Objetos/", "↩ Notas")
  prevLink := some ("lecture-19.pt.html", "‹ Aula anterior")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula21Deck : SlideDeck where
  fileName := "lecture-21.pt.html"
  pageTitle := "Aula 21: Sobrecarga · Slides"
  htmlLang := "pt"
  kicker := "Aula 21 · Linguagens de Programação"
  label := "Aula 21 · Sobrecarga"
  notesLink := some ("../pt/Aula-21___-Sobrecarga/", "↩ Notas")
  prevLink := some ("lecture-20.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-22.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula22Deck : SlideDeck where
  fileName := "lecture-22.pt.html"
  pageTitle := "Aula 22: Polimorfismo Paramétrico · Slides"
  htmlLang := "pt"
  kicker := "Aula 22 · Linguagens de Programação"
  label := "Aula 22 · Polimorfismo Paramétrico"
  notesLink := some ("../pt/Aula-22___-Polimorfismo-Param___trico/", "↩ Notas")
  prevLink := some ("lecture-21.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-23.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula23Deck : SlideDeck where
  fileName := "lecture-23.pt.html"
  pageTitle := "Aula 23: Subtipagem · Slides"
  htmlLang := "pt"
  kicker := "Aula 23 · Linguagens de Programação"
  label := "Aula 23 · Subtipagem"
  notesLink := some ("../pt/Aula-23___-Subtipagem/", "↩ Notas")
  prevLink := some ("lecture-22.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-24.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula24Deck : SlideDeck where
  fileName := "lecture-24.pt.html"
  pageTitle := "Aula 24: Inferência de Tipos · Slides"
  htmlLang := "pt"
  kicker := "Aula 24 · Linguagens de Programação"
  label := "Aula 24 · Inferência de Tipos"
  notesLink := some ("../pt/Aula-24___-Infer___ncia-de-Tipos/", "↩ Notas")
  prevLink := some ("lecture-23.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-25.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula25Deck : SlideDeck where
  fileName := "lecture-25.pt.html"
  pageTitle := "Aula 25: O Paradigma Imperativo · Slides"
  htmlLang := "pt"
  kicker := "Aula 25 · Linguagens de Programação"
  label := "Aula 25 · O Paradigma Imperativo"
  notesLink := some ("../pt/Aula-25___-O-Paradigma-Imperativo/", "↩ Notas")
  prevLink := some ("lecture-24.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-26.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula26Deck : SlideDeck where
  fileName := "lecture-26.pt.html"
  pageTitle := "Aula 26: O Paradigma Orientado a Objetos · Slides"
  htmlLang := "pt"
  kicker := "Aula 26 · Linguagens de Programação"
  label := "Aula 26 · O Paradigma Orientado a Objetos"
  notesLink := some ("../pt/Aula-26___-O-Paradigma-Orientado-a-Objetos/", "↩ Notas")
  prevLink := some ("lecture-25.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-27.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula27Deck : SlideDeck where
  fileName := "lecture-27.pt.html"
  pageTitle := "Aula 27: O Paradigma Funcional · Slides"
  htmlLang := "pt"
  kicker := "Aula 27 · Linguagens de Programação"
  label := "Aula 27 · O Paradigma Funcional"
  notesLink := some ("../pt/Aula-27___-O-Paradigma-Funcional/", "↩ Notas")
  prevLink := some ("lecture-26.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-28.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula28Deck : SlideDeck where
  fileName := "lecture-28.pt.html"
  pageTitle := "Aula 28: O Paradigma Lógico · Slides"
  htmlLang := "pt"
  kicker := "Aula 28 · Linguagens de Programação"
  label := "Aula 28 · O Paradigma Lógico"
  notesLink := some ("../pt/Aula-28___-O-Paradigma-L___gico/", "↩ Notas")
  prevLink := some ("lecture-27.pt.html", "‹ Aula anterior")
  nextLink := some ("lecture-29.pt.html", "Próxima aula ›")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def aula29Deck : SlideDeck where
  fileName := "lecture-29.pt.html"
  pageTitle := "Aula 29: Quatro Paradigmas, Um Problema · Slides"
  htmlLang := "pt"
  kicker := "Aula 29 · Linguagens de Programação"
  label := "Aula 29 · Quatro Paradigmas, Um Problema"
  notesLink := some ("../pt/Aula-29___-Quatro-Paradigmas___-Um-Problema/", "↩ Notas")
  prevLink := some ("lecture-28.pt.html", "‹ Aula anterior")
  startLabel := "⇤ Início"
  prevSlideLabel := "Slide anterior"
  nextSlideLabel := "Próximo slide"

def main := slidesMain (decks :=
  [((%doc Lectures.SlidesPt.Lecture01), aula1Deck),
   ((%doc Lectures.SlidesPt.Lecture02), aula2Deck),
   ((%doc Lectures.SlidesPt.Lecture03), aula3Deck),
   ((%doc Lectures.SlidesPt.Lecture04), aula4Deck),
   ((%doc Lectures.SlidesPt.Lecture05), aula5Deck),
   ((%doc Lectures.SlidesPt.Lecture06), aula6Deck),
   ((%doc Lectures.SlidesPt.Lecture07), aula7Deck),
   ((%doc Lectures.SlidesPt.Lecture08), aula8Deck),
   ((%doc Lectures.SlidesPt.Lecture09), aula9Deck),
   ((%doc Lectures.SlidesPt.Lecture10), aula10Deck),
   ((%doc Lectures.SlidesPt.Lecture11), aula11Deck),
   ((%doc Lectures.SlidesPt.Lecture12), aula12Deck),
   ((%doc Lectures.SlidesPt.Lecture13), aula13Deck),
   ((%doc Lectures.SlidesPt.Lecture14), aula14Deck),
   ((%doc Lectures.SlidesPt.Lecture15), aula15Deck),
   ((%doc Lectures.SlidesPt.Lecture16), aula16Deck),
   ((%doc Lectures.SlidesPt.Lecture17), aula17Deck),
   ((%doc Lectures.SlidesPt.Lecture18), aula18Deck),
   ((%doc Lectures.SlidesPt.Lecture19), aula19Deck),
   ((%doc Lectures.SlidesPt.Lecture20), aula20Deck),
   ((%doc Lectures.SlidesPt.Lecture21), aula21Deck),
   ((%doc Lectures.SlidesPt.Lecture22), aula22Deck),
   ((%doc Lectures.SlidesPt.Lecture23), aula23Deck),
   ((%doc Lectures.SlidesPt.Lecture24), aula24Deck),
   ((%doc Lectures.SlidesPt.Lecture25), aula25Deck),
   ((%doc Lectures.SlidesPt.Lecture26), aula26Deck),
   ((%doc Lectures.SlidesPt.Lecture27), aula27Deck),
   ((%doc Lectures.SlidesPt.Lecture28), aula28Deck),
   ((%doc Lectures.SlidesPt.Lecture29), aula29Deck)])
