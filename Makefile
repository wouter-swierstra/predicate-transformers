default : handlers.pdf

%.tex : %.lagda
	lhs2TeX --agda --poly -o $@ $<

%.pdf : %.tex
	latexmk -xelatex $<

clean :
	rm -f *.aux *.log *.out *.ptb *.bbl *.blg *.agdai *.fls Check.agda handlers.tex

check :
	lhs2TeX --newcode  --no-pragmas handlers.lagda -o Check.agda
#	cp src/Prelude.agda .
	agda --type-in-type Check.agda
#	rm -rf Check.agda*
	echo 'Check succeeded'
