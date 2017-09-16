DOCS = \
	haskell-for-ocaml-programmers.rst \
	Retries-in-CRDB.rst

SYNTAX_STYLE_HTML = vs
SYNTAX_STYLE_PDF = bw
CSS = aux/html4css1.css aux/math.css aux/narrow.css aux/pygments-$(SYNTAX_STYLE_HTML).css
FOOTER = aux/footer.rst
STY = aux/base.sty aux/pygments-$(SYNTAX_STYLE_PDF).sty

# Tooling
PYGMENTIZE = pygmentize
RST2HTML = rst2html.py --table-style=borderless --syntax-highlight=short --stylesheet-path=aux/all.css --link-stylesheet
RST2LATEX = rst2latex.py --use-latex-citations --table-style=borderless --use-latex-docinfo --latex-preamble="" --syntax-highlight=short --template=aux/template.tex --embed-stylesheet --documentoptions=11pt --stylesheet=$(STY_j)
CSS2STY = python aux/pygments_css2sty.py
LATEX2PDF = latexmk -pdf -g

# Target transformers
STY_j := $(shell echo $(STY) | tr ' ' ',')
PYSTYLES_ALL = $(foreach S,$(PYGMENTS_STYLES), aux/pygments-$(S).css aux/pygments-$(S).sty)
PYGMENTS_STYLES = $(shell $(PYGMENTIZE) -L styles|grep '^\*'|cut -d' ' -f2|tr -d ':')
APPEND_FOOTER = doappend() { \
  cat "$$1"; echo; echo; \
  cat "$$2"; \
  } && doappend

# What to build
# TARGETS = $(PYSTYLES_ALL) $(DOCS:.rst=.html) $(DOCS:.rst=.pdf) $(DOCS.rst=.txt) aux/min.css index.rst
TARGETS = $(PYSTYLES_ALL) $(DOCS:.rst=.html) $(DOCS.rst=.txt) aux/all.css index.rst
all: $(TARGETS)

clean:
	rm -f $(TARGETS) *.tmp *.ltx
	rm -f *\~ *.log *.aux *.fdb_latexmk *.toc *.fls

aux/all.css: $(CSS)
	rm -f $@
	cat $(CSS)>$@.tmp
	mv -f $@.tmp $@

aux/min.css: aux/all.css
	curl -X POST -s -d template=3 --data-urlencode css_text@$^ http://csscompressor.com/compress.php | \
           python -c 'import json; import sys; print json.load(sys.stdin)["mini"]' | \
	     sed -e 's/@import \([^;]*\);/@import "\1";/g'> $@.tmp
	mv -f $@.tmp $@

%.html: %.rst $(FOOTER)
	rm -f $@.tmp $@
	$(APPEND_FOOTER) $< $(FOOTER) | $(RST2HTML) | \
	    grep -v 'link.*rel.*stylesheet.*html4css1/math.css' >$@.tmp
	mv -f $@.tmp $@

%.ltx: %.rst $(STY) $(FOOTER) aux/template.tex
	rm -f $@.tmp $@
	$(APPEND_FOOTER) $< $(FOOTER) | $(RST2LATEX) >$@.tmp
	mv -f $@.tmp $@

%.txt: %.rst
	ln -sf $< $@

.PRECIOUS: $(DOCS:.rst=.txt)

.PHONY: show-files
show-files:
	@for i in $(DOCS:.rst=); do if test -d $$i; then echo $$i; fi; done
	@echo $(DOCS:.rst=.txt) $(DOCS:.rst=.html) $(DOCS:.rst=.pdf) aux/min.css

index.rst: $(DOCS:.rst=.txt) index-header.rst
	rm -f $@.tmp $@
	( cat index-header.rst; \
	for i in $(DOCS); do \
	   echo "- \`$$title\`__. $$date. (also in PDF__ and \`source form\`__)."; \
	   echo; \
	   echo "  .. __: $$slug.html"; \
	   echo "  .. __: $$slug.pdf"; \
	   echo "  .. __: $$slug.txt"; \
	   echo; \
	done ) >$@.tmp
	mv $@.tmp $@

%.pdf: %.ltx
	$(LATEX2PDF) $<

aux/pygments-%.css:
	rm -f $@
	$(PYGMENTIZE) -S $* -f html >$@.tmp
	mv $@.tmp $@

aux/pygments-%.sty: aux/pygments-%.css
	rm -f $@
	$(CSS2STY) <$< >$@.tmp
	mv $@.tmp $@
