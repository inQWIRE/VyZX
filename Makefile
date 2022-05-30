all: Makefile _CoqProject
	git submodule update --init
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile

clean:
	rm -rf CoqMakefile CoqMakefile.conf .CoqMakefile.d .*.aux *.vo* *.glob */*/*.vo* */*/*.glob
