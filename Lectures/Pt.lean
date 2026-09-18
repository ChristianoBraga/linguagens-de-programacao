/-
Root of the Portuguese lecture notes. Each lecture is a module under
`Lectures/Pt/`, included here in course order.
-/
import VersoManual
import Lectures.Pt.Lecture01
import Lectures.Pt.Lecture02
import Lectures.Pt.Lecture03
import Lectures.Pt.Lecture04

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Linguagens de Programação" =>

Notas de aula da disciplina 09022, Linguagens de Programação, do curso de Engenharia de Computação do Instituto Militar de Engenharia. A disciplina estuda o significado das construções das linguagens de programação. Ela segue a estrutura de Watt e apresenta cada construção como parte de Core C++, um subconjunto bem comportado de C++17, com regras de tipos e de avaliação em semântica natural e a sua implementação em Lean 4. A unidade didática I, Introdução, ocupa as quatro primeiras aulas.

{include 0 Lectures.Pt.Lecture01}
{include 0 Lectures.Pt.Lecture02}
{include 0 Lectures.Pt.Lecture03}
{include 0 Lectures.Pt.Lecture04}
