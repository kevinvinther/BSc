(TeX-add-style-hook
 "report"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("tcolorbox" "most")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "rep10"
    "tlatex"
    "listings"
    "graphicx"
    "lipsum"
    "tcolorbox"
    "fontawesome"
    "xcolor"
    "multicol"
    "algorithm2e")
   (TeX-add-symbols
    "sans")
   (LaTeX-add-labels
    "higherids")
   (LaTeX-add-environments
    '("gathered" LaTeX-env-args ["argument"] 0))
   (LaTeX-add-bibliographies
    "bibliography")
   (LaTeX-add-tcolorbox-newtcolorboxes
    '("callout" "" "" ""))
   (LaTeX-add-xcolor-definecolors
    "mycolor"
    "offwhite"))
 :latex)

