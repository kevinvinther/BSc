(TeX-add-style-hook
 "bibliography"
 (lambda ()
   (LaTeX-add-bibitems
    "kshemkalyani2011distributed")
   (LaTeX-add-environments
    '("gathered" LaTeX-env-args ["argument"] 0)))
 '(or :bibtex :latex))

