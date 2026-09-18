/-
Root of the English lecture notes. Each lecture is a module under
`Lectures/En/`, included here in course order.
-/
import VersoManual
import Lectures.En.Lecture01
import Lectures.En.Lecture02
import Lectures.En.Lecture03
import Lectures.En.Lecture04

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Programming Languages" =>

Lecture notes of course 09022, Linguagens de Programação, of the Computer Engineering programme of the Instituto Militar de Engenharia. The course studies the meaning of the constructions of programming languages. It follows the structure of Watt and presents each construction as part of Core C++, a well behaved subset of C++17, with typing and evaluation rules in natural semantics and their implementation in Lean 4. Unit I, Introduction, takes the first four lectures.

{include 0 Lectures.En.Lecture01}
{include 0 Lectures.En.Lecture02}
{include 0 Lectures.En.Lecture03}
{include 0 Lectures.En.Lecture04}
