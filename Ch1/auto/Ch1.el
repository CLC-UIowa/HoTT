(TeX-add-style-hook
 "Ch1"
 (lambda ()
   (setq TeX-command-extra-options
         "--synctex=1")
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("exam" "12pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "margin=1.5in")))
   (TeX-run-style-hooks
    "latex2e"
    "exam"
    "exam12"
    "geometry"
    "tikz"
    "tikz-cd")
   (TeX-add-symbols
    '("TypeJ" 3)
    '("Type" 2)
    '("EqJ" 4)
    '("Eq" 2)
    "Jeq")
   (LaTeX-add-labels
    "sec:ChapterOne")
   (LaTeX-add-bibliographies
    "template.bib"))
 :latex)

