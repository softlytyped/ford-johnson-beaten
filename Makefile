.PHONY: prepare verify

PYTHON ?= python3

prepare:
	$(PYTHON) scripts/prepare.py

verify: prepare
	lake build
	lake env lean Check.lean
