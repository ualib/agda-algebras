

Command to generate latex without type-checking:


A faster variant of the backend is available by invoking QuickLaTeX from the Emacs mode, or using 

agda --latex --only-scope-checking

When this variant of the backend is used the top-level module is not type-checked, only scope-checked.

Note that this can affect the generated document. For instance, scope-checking does not resolve overloaded constructors.




Unicode characters may not be typeset properly out of the box. How to address this problem depends on what LaTeX engine is used.

pdfLaTeX:

The pdfLaTeX program does not by default understand the UTF-8 character encoding. You can tell it to treat the input as UTF-8 by using the inputenc package:

\usepackage[utf8]{inputenc}
If the inputenc package complains that some Unicode character is “not set up for use with LaTeX”, then you can give your own definition. Here is one example:

\usepackage{newunicodechar}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{←}{\ensuremath{\mathnormal\from}}
\newunicodechar{→}{\ensuremath{\mathnormal\to}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
