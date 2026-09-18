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
- Um documento Verso por aula em `Lectures/Pt/AulaNN.lean`, incluído em
  `Lectures/Pt.lean`. Um deck por aula em `Lectures/SlidesPt/AulaNN.lean`,
  registrado em `SlidesPtMain.lean`, cada seção de nível superior é um slide.
- Cada aula abre com `namespace AulaN` e `open CoreCpp` em um bloco
  `lean -show`, e fecha o namespace no fim. As saídas de `#eval` vão em
  blocos `leanOutput` e o Verso as confere na construção.
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

- `lake exe lectures-pt --output _out/pt` e `lake exe slides-pt --output
  _out/slides-pt`. `./preview.sh` monta e serve em `localhost:8000`,
  `./preview.sh --no-build` reaproveita `_out`.
- O sítio é publicado pela GitHub Actions a cada push em `main`, workflow em
  `.github/workflows/deploy.yml`, origem "GitHub Actions" nas configurações do
  Pages. `./deploy.sh` publica à mão no ramo `gh-pages`.
- Dependências. Verso `v4.32.0` e `corecpp` de `main` no GitHub. Toolchain
  `v4.32.2`, a mesma de `corecpp`. Sem Mathlib.

## Estado em 2026-09-18

UD I completa, quatro aulas com slides. Linguagens e Paradigmas, Sintaxe,
Semântica, Processadores de Linguagens. As demais UD por escrever.
