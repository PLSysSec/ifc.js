all: ifc.pdf

ifc.pdf: ifc.tex
	pdflatex ifc.tex
ifc.tex: ifc.ott
	ott -i ifc.ott -o ifc.tex

clean:
	-rm *.aux
	-rm *.glob
	-rm *.log
	-rm *.pdf
	-rm *.tex
	-rm *.vo
	-rm *~
