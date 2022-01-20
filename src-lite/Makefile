COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile

OTT_FLAGS := -coq_lngen true -signal_parse_errors true

SYSTEMS := decl alg bidir erased
OTT_OUTS   := $(addsuffix _ott.v,${SYSTEMS})
LNGEN_OUTS := $(addsuffix _inf.v,${SYSTEMS})

.PHONY: ott lngen coq clean

%_ott.v : %.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" -i "" $@

ott : ${OTT_OUTS}

%_inf.v : %_ott.v
	lngen --coq $@ --coq-ott $*_ott $*.ott

lngen : ${LNGEN_OUTS}

# a hack to force makefile to detect source file changes
.FILE_LIST : ${LNGEN_OUTS} FORCE
	tree . -if | grep -E "v$$" | cut -c3- | sort -s > .FILE_LIST.tmp
	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT} .FILE_LIST ${LNGEN_OUTS}
	tree . -if | grep -E "v$$" | cut -c3- | xargs coq_makefile -o $@ -f ${COQ_PROJECT}

coq : ${COQ_MAKEFILE}
	${MAKE} -f ${COQ_MAKEFILE}

clean :
	${MAKE} -f ${COQ_MAKEFILE} clean
	rm *_inf.v *_ott.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf .FILE_LIST
