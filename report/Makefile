
LATEX=pdflatex -shell-escape

BIBTEX=bibtex
BIBFILE=report
PAPER=report
TEXFILES = $(wildcard *.tex)

SUBDIRS =
#figs

all: subdirs $(PAPER).pdf

subdirs:
	@for dir in $(SUBDIRS); do $(MAKE) -C $$dir; done;

$(PAPER).pdf: $(TEXFILES) $(BIBFILE).bib
	$(LATEX) $(PAPER)
	$(BIBTEX) $(BIBFILE)
	$(LATEX) $(PAPER)
	$(LATEX) $(PAPER)

cleantex:
	rm -f *.aux *.log *~ *.out .DS_Store *.dvi $(PAPER).ps $(PAPER).pdf \
		*.lot *.lof *.toc *.blg *.bbl *.ent *.bak *.glo *.gls *.ist

clean: cleantex
	for dir in $(SUBDIRS); do $(MAKE) -C $$dir clean; done;\

