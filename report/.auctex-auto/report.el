(TeX-add-style-hook
 "report"
 (lambda ()
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "rep10"
    "listings"
    ""
    "amssymb"
    "graphicx"
    "lipsum"))
 :latex)

