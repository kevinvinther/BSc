(TeX-add-style-hook
 "tlatex"
 (lambda ()
   (TeX-run-style-hooks
    "latexsym"
    "ifthen"
    "verbatim")
   (TeX-add-symbols
    '("fl" 1)
    '("cl" 1)
    '("al" 3)
    '("e" 1)
    '("tdash" 1)
    '("ceqdash" 1)
    '("usdash" 1)
    '("cdash" 1)
    '("raisedDash" 3)
    '("multivspace" 1)
    '("xtest" 1)
    '("setgmargin" 1)
    '("vshade" 1)
    '("shadebox" 1)
    "implies"
    "ltcolon"
    "colongt"
    "defeq"
    "dotdot"
    "coloncolon"
    "eqdash"
    "pp"
    "mm"
    "stst"
    "slsl"
    "ct"
    "A"
    "E"
    "EE"
    "whileop"
    "ASSUME"
    "ASSUMPTION"
    "AXIOM"
    "BOOLEAN"
    "CASE"
    "CONSTANT"
    "CONSTANTS"
    "ELSE"
    "EXCEPT"
    "EXTENDS"
    "FALSE"
    "IF"
    "IN"
    "INSTANCE"
    "LET"
    "LOCAL"
    "MODULE"
    "OTHER"
    "STRING"
    "THEN"
    "THEOREM"
    "LEMMA"
    "PROPOSITION"
    "COROLLARY"
    "TRUE"
    "VARIABLE"
    "VARIABLES"
    "WITH"
    "WF"
    "SF"
    "CHOOSE"
    "ENABLED"
    "UNCHANGED"
    "SUBSET"
    "UNION"
    "DOMAIN"
    "BY"
    "OBVIOUS"
    "HAVE"
    "QED"
    "TAKE"
    "DEF"
    "HIDE"
    "RECURSIVE"
    "USE"
    "DEFINE"
    "PROOF"
    "WITNESS"
    "PICK"
    "DEFS"
    "PROVE"
    "SUFFICES"
    "NEW"
    "LAMBDA"
    "STATE"
    "ACTION"
    "TEMPORAL"
    "ONLY"
    "OMITTED"
    "bang"
    "p"
    "boxsep"
    "boxrule"
    "bottombar"
    "moduleLeftDash"
    "moduleRightDash"
    "midbar"
    "tstrut"
    "rstrut"
    "xtstrut"
    "thegmargin"
    "gmargin"
    "tlx"
    "oldin"
    "oldnotin"
    "graymargin"
    "itfam"
    "makelabel")
   (LaTeX-add-environments
    "noppcal"
    "nopcal"
    "notla"
    "ppcal"
    "pcal"
    "tla"
    '("describe" 1)
    '("mcom" 1)
    '("lcom" 1)
    '("cpar" 6))
   (LaTeX-add-counters
    "pardepth")
   (LaTeX-add-lengths
    "symlength"
    "equalswidth"
    "charwidth"
    "boxrulewd"
    "boxlineht"
    "boxruleht"
    "boxruledp"
    "pcalvspace"
    "lcomindent"
    "templena"
    "templenb"
    "vshadelen"
    "boxwidth"
    "multicommentdepth"
    "xmcomlen"
    "spacewidth"
    "alignboxwidth"
    "alignwidth")
   (LaTeX-add-saveboxes
    "tempboxa"
    "tempsbox"
    "alignbox"))
 :latex)

