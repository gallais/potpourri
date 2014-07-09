COMPILER := ghc
TARGET   := HSubst
EXEC     := out

main:
	$(COMPILER) $(TARGET).hs -o $(EXEC)

dev:
	watch -d -n 1 '$(COMPILER) -fno-code $(TARGET).hs'
