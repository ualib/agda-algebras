## doc/TYPES2021/README

Here is the workflow used to develop the document `agda-hsp.pdf`.

1. Edit/improve the literate Agda file `src/Demos/HSP.lagda`.
2. Invoke `agda --latex --latex-dir=doc/TYPES2021 src/Demos/HSP.lagda` from the main `agda-algebras` directory.
3. Invoke `pdflatex agda-hsp` from within the `doc/TYPES2021` directory.
