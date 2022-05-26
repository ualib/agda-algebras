## doc/TYPES2021/README

Here is the workflow used to develop the document `agda-hsp.pdf`.

1.  Make sure you are using the generate-tex branch of the agda-algebras repository.
    ```
    git checkout generate-tex
    ```
2.  Edit the literate Agda file `src/Demos/HSP.lagda` as needed.  The text surrounding the code is TeX.
3.  Invoke `agda --latex --latex-dir=doc/TYPES2021 src/Demos/HSP.lagda` from the main `agda-algebras` directory.
4.  Invoke `pdflatex agda-hsp` from within the `doc/TYPES2021` directory.
