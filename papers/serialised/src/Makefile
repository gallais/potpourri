AGDAEXECNAME=Bob
IDRISEXECNAME=Alice

COMMFILE=commfile

all:
	@ cd idris && idris2 -p contrib -c ${IDRISEXECNAME}.idr -o ${IDRISEXECNAME}
	@ cd agda && agda-2.6.4 -c ${AGDAEXECNAME}.agda

	@ echo "\n\n\nBuilds successful\n"
	@ ./idris/build/exec/${IDRISEXECNAME} ${COMMFILE}
	@ echo "\n\e[1mHello I am hexdump!\e[0m"
	@ echo "Here is the content of ${COMMFILE}:"
	@ hexdump -C ${COMMFILE}
	@ echo ""
	@ ./agda/${AGDAEXECNAME} commfile
