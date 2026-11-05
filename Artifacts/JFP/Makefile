# Run from this directory: make pdf / make validate
PYTHON ?= python3
TECTONIC ?= tectonic

.PHONY: pdf validate snippets style

snippets:
	$(PYTHON) prepare.py

style:
	$(PYTHON) jfp_format.py

pdf: style snippets
	$(TECTONIC) --untrusted --keep-logs sbv-tutorial.tex

validate:
	$(PYTHON) validate.py
