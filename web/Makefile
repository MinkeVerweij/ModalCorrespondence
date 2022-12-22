
.PHONY: develop release src cache

develop: src
	nix-shell --run reload

release: src
	nix-build -A release

src: ../src/*
	mkdir -p src
	cp -vr --preserve=all ../src/*.hs ../src/*.x ../src/*.y ./src/
	rm -f ./src/Main.hs

cache:
	nix-env -iA cachix -f https://cachix.org/api/v1/install
	cachix use miso-haskell
