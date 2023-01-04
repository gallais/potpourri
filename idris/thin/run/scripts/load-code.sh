#!/bin/bash -eux
# A basic script to check the code shipped in the src.tar.gz tarball

echo 'Setting up environment variables'

cat >>$HOME/.bashrc <<'EOF'
export PATH=$HOME/.nix-profile/bin:$PATH
EOF
source $HOME/.bashrc

echo -e '\033[1m0. Checking the installation\033[0m'

which idris2
idris2 --version

echo -e '\033[1m1. Extracting the code\033[0m'

cd /tmp/
tar -zxvf /tmp/src.tar.gz

cd $HOME
mv /tmp/src $HOME/src

echo -e '\033[1m2. Checking the code\x1b[0m'

cd src/

# Building the package
idris2 --build

echo -e '\033[1m3. Compiling the code\033[0m'

# Compiling main (and its dependencies) to javascript
idris2 -p contrib --cg javascript -o main Main.idr

echo -e '\033[1mThe `view` function was compiled to:\033[0m'

# Extracting the result of compiling 'view' (and the internal case block)
awk -v RS= '/\/\* Thin.Smart.view/' build/exec/main >> extracted-view.js
echo "" >> extracted-view.js
awk -v RS= '/\/\* Thin.Smart.case block in view/' build/exec/main >> extracted-view.js

cat extracted-view.js

cd $HOME

echo 'Finished'
