all: stack.html stack.pdf stack.vo

stack.glob: stack.v
	coqc stack.v

stack.pdf: stack.tex
	xelatex stack.tex

stack.tex: stack.glob
	coqdoc -latex stack.v

stack.html: stack.glob
	coqdoc stack.v

clean:
	rm -f *.aux *.log *.vo *.glob

nuke: clean
	rm -f *.html *.tex *.pdf *.hs *.ml* *.css *.sty

.PHONY: all clean nuke
