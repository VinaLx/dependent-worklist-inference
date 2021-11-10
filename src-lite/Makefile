COQ_PROJECT := _CoqProject
COQ_MAKEFILE := CoqMakefile

.PHONY: ott lngen coq

%_ott.v : %.ott
	ott -i $^ -o $@ -coq_lngen true
	sed -e "/Ott.ott_list_core/d" -i "" $@

ott : alg_ott.v decl_ott.v

%_inf.v : %_ott.v
	lngen --coq $@ --coq-ott $*_ott $*.ott

lngen : alg_inf.v decl_inf.v

.FILE_LIST : *_inf.v FORCE
	ls -1 *.v | sort -s > .FILE_LIST.tmp
	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT} *_ott.v *_inf.v .FILE_LIST # decl_ott.v decl_inf.v alg_ott.v alg_inf.v
	coq_makefile -o $@ -f ${COQ_PROJECT} *.v

coq : ${COQ_MAKEFILE}
	${MAKE} -f ${COQ_MAKEFILE}

clean :
	${MAKE} -f ${COQ_MAKEFILE} clean
	rm *_inf.v *_ott.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf
