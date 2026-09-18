# lectures

Notas de aula e slides da disciplina 09022, Linguagens de Programação, IME,
em Verso, com a mesma infraestrutura do curso de Verificação Formal de
Software em `~/Dropbox/IME/verificacao_formal/lectures`. Repositório
`https://github.com/ChristianoBraga/linguagens-de-programacao`, sítio em
https://christianobraga.github.io/linguagens-de-programacao/.

## Convenções

- A RULE ZERO de `~/.claude/CLAUDE.md` e as convenções de `../CLAUDE.md` valem.
  Prosa em português, código, comentários e identificadores em inglês, salvo
  os nomes de exemplo nos programas Core C++ das aulas.
- Bilíngue como em Verificação Formal. Árvores paralelas `Lectures/En/` e
  `Lectures/Pt/`, um documento por aula, `LectureNN.lean`, incluído em
  `Lectures/En.lean` e `Lectures/Pt.lean`. Decks em `Lectures/SlidesEn/` e
  `Lectures/SlidesPt/`, registrados em `SlidesEnMain.lean` e `SlidesPtMain.lean`,
  cada seção de nível superior é um slide. O código Lean é idêntico nas duas
  línguas, só a prosa muda. A página de entrada `site/index.html` é em inglês
  e aponta para as duas árvores. O inglês é escrito primeiro.
- Cada aula abre com `namespace LectureN` e `open CoreCpp` em um bloco
  `lean -show`, e fecha o namespace no fim. Os decks usam `SlidesN`. As saídas
  de `#eval` vão em blocos `leanOutput` e o Verso as confere na construção.
- O foco da disciplina é o significado de cada construção, dado por regras.
  Paradigmas são famílias de construções e a comparação fica na UD VII.
- Nenhum texto reproduz recurso existente. As fontes entram como referência em
  notas de margem, e definições, exemplos e exercícios são redigidos de forma
  própria.
- Rótulos sem números, contadores em `Lectures/Meta/Label.lean`. `{figcap}`,
  `{tabcap}`, `{ex}`, `{exercise}` nos sítios de definição, `{numref}` e
  `{secref}` nas referências. Seções referenciadas levam `%%% tag := "..." %%%`.
- `{margin}[...]` só para referências bibliográficas. Explicações vão em notas
  de rodapé, `{fnref}[chave]` no texto e `{fnAnchor "chave"}[]` dentro de
  `:::footnotes` no fim da seção.
- Na prosa do Verso, `*` solto abre ênfase, `[`, `]`, `{` e `}` soltos abrem
  ligações e papéis. Escapar com `\[`, `\]`, `\{`, `\}` ou pôr em código.
  Linhas de código com mais de 60 colunas geram aviso, quebrar as strings
  dos programas em várias linhas.
- Regras de inferência e derivações em blocos de código sem linguagem nas
  notas e em blocos `tree` nos slides.

## Construção e publicação

- `lake exe lectures-en`, `lectures-pt`, `slides-en` e `slides-pt`, com
  `--output _out/en`, `_out/pt`, `_out/slides-en` e `_out/slides-pt`. `./preview.sh` monta e serve em `localhost:8000`,
  `./preview.sh --no-build` reaproveita `_out`.
- O sítio é publicado pela GitHub Actions a cada push em `main`, workflow em
  `.github/workflows/deploy.yml`, origem "GitHub Actions" nas configurações do
  Pages. `./deploy.sh` publica à mão no ramo `gh-pages`.
- Dependências. Verso `v4.32.0` e `corecpp` de `main` no GitHub. Toolchain
  `v4.32.2`, a mesma de `corecpp`. Sem Mathlib.

## Estado em 2026-09-18

UD I completa nas duas línguas, quatro aulas com slides. Languages and
Paradigms, Syntax, Semantics, Language Processors. As demais UD por escrever.
