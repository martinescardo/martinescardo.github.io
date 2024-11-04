(TeX-add-style-hook
 "lix"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("beamer" "aspectratio=169")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("diagrams" "nohug") ("xy" "all")))
   (add-to-list 'LaTeX-verbatim-environments-local "semiverbatim")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "beamer"
    "beamer10"
    "bbold"
    "soul"
    "diagrams"
    "xy"
    "bbm"
    "stmaryrd")
   (TeX-add-symbols
    '("df" 1)
    '("trunci" 1)
    '("trunc" 1)
    '("MM" 1)
    '("M" 1)
    '("mm" 1)
    '("mg" 1)
    '("mr" 1)
    '("m" 1)
    '("doubledual" 1)
    '("dual" 1)
    '("ts" 1)
    '("tgs" 1)
    "Pause"
    "suc"
    "comp"
    "vitem"
    "mitem"
    "greencolon"
    "greeneq"
    "gsimeq"
    "Nat"
    "pr"
    "Injective"
    "Set"
    "UA"
    "isPrime"
    "isSubsingleton"
    "Prop"
    "isprop"
    "issurjection"
    "hassection"
    "issingleton"
    "isset"
    "isSurjection"
    "isSingleton"
    "isContr"
    "isEquivalence"
    "isIsomorphism"
    "hasSection"
    "image"
    "idtoeq"
    "inr"
    "inl"
    "eqq"
    "da"
    "wellinside"
    "powerset"
    "U"
    "V"
    "W"
    "K"
    "Opens"
    "Sierp"
    "db"
    "dg"
    "grey"
    "dr"
    "N"
    "R"
    "NI"
    "base"
    "loo"
    "refl"
    "idp"
    "Id"
    "Path"
    "id"
    "transport"
    "one"
    "Z"
    "ap"
    "constant"
    "eqdef"
    "Kappa"
    "WW"
    "Zero"
    "One"
    "Two"
    "J")
   (LaTeX-add-xcolor-definecolors
    "darkblue"
    "darkgreen"
    "grey"
    "darkred"))
 :latex)

