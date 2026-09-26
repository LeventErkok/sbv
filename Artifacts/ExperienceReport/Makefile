# Run from this directory: make pdf / make validate
PYTHON ?= python3
TECTONIC ?= tectonic

.PHONY: pdf validate snippets

snippets:
	$(PYTHON) prepare.py

pdf: snippets
	$(TECTONIC) --untrusted --keep-logs sbv-experience.tex

validate:
	$(PYTHON) validate.py
