all: javascript vectaslist

javascript:
	idris2 -p contrib -c Main.idr
	idris2 -p contrib --cg javascript -o main Main.idr

extractView: javascript
	rm -f extracted-view.js
	awk -v RS= '/\/\* Thin.Smart.view/' build/exec/main >> extracted-view.js
	echo "" >> extracted-view.js
	awk -v RS= '/\/\* Thin.Smart.case block in view/' build/exec/main >> extracted-view.js

vectaslist:
	idris2 -c VectAsList.idr

clean:
	rm -rf build/
	rm -f extracted-view.js
