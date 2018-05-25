default : EGTBS.pdf

hide : Hide.hs
	ghc --make -o hide Hide

EGTBS.hide.lagda : EGTBS.lagda
	./hide < EGTBS.lagda > EGTBS.hide.lagda

EGTBS.tex : EGTBS.hide.lagda
	lhs2TeX --agda --poly EGTBS.hide.lagda > EGTBS.tex

EGTBS.aux : EGTBS.tex
	pdflatex EGTBS

EGTBS.bbl : EGTBS.bib EGTBS.aux
	bibtex EGTBS

EGTBS.pdf : EGTBS.aux EGTBS.bbl
	pdflatex EGTBS.tex

