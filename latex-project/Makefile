MAIN = main

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	latexmk -pdf -interaction=nonstopmode $(MAIN).tex

clean:
	latexmk -C
	rm -f sections/*.aux

.PHONY: all clean
