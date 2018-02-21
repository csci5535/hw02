.PHONY: all clean cleanall

all: hw02-student.pdf

%.pdf: %.tex
	latexmk -pdf $<

clean:
	latexmk -c
cleanall:
	latexmk -C
