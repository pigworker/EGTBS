default : extended.pdf

hide : Hide.hs
	ghc --make -o hide Hide

extended.hide.lagda : hide extended.lagda
	./hide < extended.lagda > extended.hide.lagda

extended.tex : extended.hide.lagda
	lhs2TeX --agda --poly extended.hide.lagda > extended.tex

extended.aux : extended.tex
	pdflatex extended

extended.bbl : EGTBS.bib extended.aux
	bibtex extended

extended.pdf : extended.aux extended.bbl
	pdflatex extended.tex

