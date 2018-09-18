default : handlers.pdf

%.tex : %.lagda
	lhs2TeX -o $@ $<

%.pdf : %.tex
	latexmk -xelatex $<

clean :
	rm -f *.aux *.log *.out *.ptb *.bbl *.blg *.agdai Check.agda Prelude.agda handlers.tex

check :
	lhs2TeX --newcode --no-pragmas handlers.lagda -o Check.agda
	cp src/Prelude.agda .
	agda --type-in-type Check.agda
#	rm -rf Check.agda* Prelude.agda*
	echo 'Check succeeded'
