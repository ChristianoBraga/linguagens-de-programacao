# Linguagens de Programação — Notas de Aula

Notas de aula da disciplina *09022, Linguagens de Programação* (IME, Engenharia
de Computação, 5º ano), escritas em [Verso](https://github.com/leanprover/verso).

**Sítio publicado:** <https://christianobraga.github.io/linguagens-de-programacao/>
([notas](https://christianobraga.github.io/linguagens-de-programacao/pt/) ·
[slides](https://christianobraga.github.io/linguagens-de-programacao/slides/aula-1.pt.html)).
Cada push em `main` reconstrói e republica o sítio pela GitHub Actions
(`.github/workflows/deploy.yml`). A página inicial fica em `site/`.

A disciplina segue a estrutura de Watt e apresenta cada conceito como uma
construção de Core C++, um subconjunto bem comportado de C++17, com regras de
tipos e de avaliação em semântica natural e a sua implementação em Lean 4. O
interpretador de Core C++ está em
[github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp),
é uma dependência deste projeto, e todo código Lean das notas é elaborado na
construção do sítio.

- `Lectures/Pt/` — as aulas em português, raiz `Lectures/Pt.lean`
- `Lectures/SlidesPt/` — os slides, um documento Verso por aula
- `Lectures/Meta/` — a maquinaria compartilhada com o curso de Verificação
  Formal de Software (rótulos e contadores, notas de rodapé, blocos `savedLean`,
  tema, slides)

## Construção

```
lake exe lectures-pt --output _out/pt
lake exe slides-pt --output _out/slides-pt
```

O HTML do Verso precisa ser servido, e não aberto do sistema de arquivos.
`./preview.sh` monta o sítio como `deploy.sh` e o serve em `http://localhost:8000/`.

## Adicionar uma aula

1. Criar `Lectures/Pt/AulaNN.lean` a partir de `Aula01.lean` e
   `Lectures/SlidesPt/AulaNN.lean` a partir de `SlidesPt/Aula01.lean`.
2. Importar e incluir a aula em `Lectures/Pt.lean`, e registrar o deck em
   `SlidesPtMain.lean`.
3. Exercícios com código Lean vão em blocos `savedLean -keep`, extraídos para
   `html-multi/example-code/`.
