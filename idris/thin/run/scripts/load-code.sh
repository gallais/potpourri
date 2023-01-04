#!/bin/bash -eux
# A basic script to check the code shipped in the src.tar.gz tarball

echo 'Setting up environment variables'

cat >>$HOME/.bashrc <<'EOF'
export PATH=$HOME/.nix-profile/bin:$PATH
EOF
source $HOME/.bashrc

echo 'Checking installation'

which idris2
idris2 --version

echo 'Extracting the code'

cd /tmp/
tar -zxvf /tmp/src.tar.gz

cd $HOME
mv /tmp/src $HOME/src

echo 'Checking the code'

cd src/

# Building the package
idris2 --build

echo 'The `view` function was compiled to:'

# Compiling main (and its dependencies) to javascript
idris2 -p contrib --cg javascript -o main Main.idr

# Extracting the result of compiling 'view' (and the internal case block)
awk -v RS= '/\/\* Thin.Smart.view/' build/exec/main >> extracted-view.js
echo "" >> extracted-view.js
awk -v RS= '/\/\* Thin.Smart.case block in view/' build/exec/main >> extracted-view.js

cat extracted-view.js

cd $HOME

echo 'Finished'
