## doc/TYPES2021/README

Here is the workflow used to develop the document `agda-hsp.pdf`.

1. Edit/improve the literate Agda file `src/Demos/HSP.lagda`.
2. In the main agda-algebras directory, run the following command:
   `generate-tex src/Demos/HSP.lagda`
3. Copy the file `latex/Demos.HSP.tex` to `doc/TYPES2021/HSP.tex`, overwriting the latter.
4. Compile the file doc/TYPES2021/agda-hsp.tex with pdflatex.
