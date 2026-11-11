.PHONY: all clean
all:
	@$(MAKE) -s -C ../.. build
	@bash run.sh
	@python3 ../unit-build.py

clean:
	@rm -rf out
