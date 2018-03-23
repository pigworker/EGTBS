default : EGTBS.pdf

EGTBS.tex : EGTBS.lagda
	lhs2TeX --agda --poly EGTBS.lagda > EGTBS.tex

EGTBS.aux : EGTBS.tex
	pdflatex EGTBS

EGTBS.bbl : EGTBS.bib EGTBS.aux
	bibtex EGTBS

EGTBS.pdf : EGTBS.aux EGTBS.bbl
	pdflatex EGTBS.tex

