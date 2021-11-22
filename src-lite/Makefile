COQ_PROJECT := _CoqProject
COQ_MAKEFILE := CoqMakefile

SYSTEMS := decl alg bidir
OTT_OUTS   := $(addsuffix _ott.v,${SYSTEMS})
LNGEN_OUTS := $(addsuffix _inf.v,${SYSTEMS})

.PHONY: ott lngen coq clean

%_ott.v : %.ott
	ott -i $^ -o $@ -coq_lngen true
	sed -e "/Ott.ott_list_core/d" -i "" $@

ott : ${OTT_OUTS}

%_inf.v : %_ott.v
	lngen --coq $@ --coq-ott $*_ott $*.ott

lngen : ${LNGEN_OUTS}

.FILE_LIST : ${LNGEN_OUTS} FORCE
	ls -1 *.v | sort -s > .FILE_LIST.tmp
	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT} .FILE_LIST ${LNGEN_OUTS}
	coq_makefile -o $@ -f ${COQ_PROJECT} *.v

coq : ${COQ_MAKEFILE}
	${MAKE} -f ${COQ_MAKEFILE}

clean :
	${MAKE} -f ${COQ_MAKEFILE} clean
	rm *_inf.v *_ott.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf .FILE_LIST
