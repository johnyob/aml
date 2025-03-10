.PHONY: all watch
all:
	typst compile main.typ

watch:
	typst watch main.typ
