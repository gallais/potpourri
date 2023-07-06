AGDAEXECNAME=Bob
IDRISEXECNAME=Alice

COMMFILE1=commfile1
COMMFILE2=commfile2

all: idris/build/exec/${IDRISEXECNAME} agda/${AGDAEXECNAME}
	@ ./idris/build/exec/${IDRISEXECNAME} generate ${COMMFILE1}
	@ echo "\n\e[1mHello I am hexdump!\e[0m"
	@ echo "Here is the content of the file ${COMMFILE1}:"
	@ hexdump -C ${COMMFILE1}
	@ echo ""
	@ ./agda/${AGDAEXECNAME} ${COMMFILE1} ${COMMFILE2}
	@ echo "\n\e[1mHello I am hexdump!\e[0m"
	@ echo "Here is the content of the file ${COMMFILE2}:"
	@ hexdump -C ${COMMFILE2}
	@ echo ""
	@ ./idris/build/exec/${IDRISEXECNAME} load ${COMMFILE2}

idris/build/exec/${IDRISEXECNAME}: idris/${IDRISEXECNAME}.idr
	@ echo "Compiling ${IDRISEXECNAME}"
	@ cd idris && idris2 -p contrib -c ${IDRISEXECNAME}.idr -o ${IDRISEXECNAME}

agda/${AGDAEXECNAME}: agda/${AGDAEXECNAME}.agda
	@ echo "Compiling ${AGDAEXECNAME}"
	@ cd agda && agda-2.6.4 -v0 -c ${AGDAEXECNAME}.agda

clean:
	@ echo "Removing interface files and executables"
	@ find agda/ -name "*.agdai" | xargs rm -f
	@ rm -f agda/${AGDAEXECNAME}
	@ rm -rf idris/build
