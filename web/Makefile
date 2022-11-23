
.PHONY: develop release src

develop: src
	nix-shell --run reload

release: src
	nix-build -A release

src: ../src/*
	mkdir -p src
	cp -vr --preserve=all ../src/*.hs ./src/
	rm -f ./src/Main.hs
