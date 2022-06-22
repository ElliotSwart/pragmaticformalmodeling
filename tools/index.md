---
layout: default
title: Tools and Additional Citations
nav_order: 10
---

# {{page.title}}

## Tools for TLA+
- [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html): The fully featured (if somewhat outdated) IDE for TLA+. Includes modeling, document generation, and live syntax checking.
- [VSCode TLA+](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus): Lighter weight IDE with textfile based model configuration. Generally more responsive. The latest alpha version, [found here](https://github.com/tlaplus/vscode-tlaplus/releases), has a debugger that might be useful to you while getting a handle on the language.

## Tools for TLA+ display
- [tla2json](https://github.com/japgolly/tla2json): Used to turn trace output from toolbox into json for automatic trace widget generation.
- [LaTex](https://www.latex-project.org/): Used to render the LaTex output of TLA+ to dvi format.
- [dvisvgm](https://dvisvgm.de/): Used to convert the dvi formatted TLA+ specifications into SVGs that could be displayed inline in the website.
- [Code highlighting](https://github.com/ElliotSwart/practicalformalmodeling/blob/initial/_plugins/tla.rb): Improved / repackaged for Jekyll, but the majority of the code came from [this pull request](https://github.com/rouge-ruby/rouge/pull/1740) by Tom Lee.

## Tools for the website
- [Jekyll](https://jekyllrb.com/): A static site generator. This website heavily relied on the templating functionality Jekyll provides.
- [PlantUML](https://plantuml.com/): Used to generate UML diagrams from text.
    - [Kramdown::PlantUml](https://github.com/SwedbankPay/kramdown-plantuml): Allows rendering it in Jekyll.

- [Just the Docs](https://just-the-docs.github.io/just-the-docs/): The theme that was used and modified for this website.


## Assets
- [Favicon](https://www.flaticon.com/free-icons/diamond): Diamond icons created by Vaadin - Flaticon.


## Acknowledgments
- To [Liza Knipscher](https://github.com/knipscher) for editing and proofreading tons of text and code.
- To all the people who wrote the [learning material](../learning-material) and the tools above, your work was invaluable to the completion of this project.
