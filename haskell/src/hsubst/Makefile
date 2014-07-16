COMPILER := ghc
TARGET   := Main
EXEC     := out

main:
	$(COMPILER) $(TARGET).hs -o $(EXEC)

dev:
	watch -d -n 1 '$(COMPILER) -fno-code $(TARGET).hs'

clean:
	rm -f *.hi *.o *~ $(EXEC)
