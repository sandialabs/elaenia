#!/bin/bash

# cmake by default uses cc/c++ I've found more stability using GCC
CC=gcc
CXX=g++

# Build FILIB, a dependency for Kodiak
wget -P external https://www2.math.uni-wuppertal.de/wrswt/software/filib++/filibsrc-3.0.2.tar.gz
if [ $(sha256sum external/filibsrc-3.0.2.tar.gz | cut -d' ' -f 1) != 14583ca412d0a081a176e115b452386fb7078bc590cf22af86db635fbf817562 ];
then
	echo "SHA256 sum for filibsrc does not match known version"
	exit 2
fi
tar -xf external/filibsrc-3.0.2.tar.gz -C external
cd external/filibsrc
./configure CC=$CC CFLAGS=-fPIC CPPFLAGS=-fPIC CXXFLAGS="-fPIC -std=c++11"
make
export FILIB_ROOT=$(pwd)

# Build Kodiak
cd ../PRECiSA/Kodiak
mkdir -p build && cd build
cmake -DCMAKE_C_COMPILER=$CC -DCMAKE_CXX_COMPILER=$CXX ..
cmake --build .
export KODIAK_LIB_DIR=$(pwd)
cd ../../../../
cat > external/PRECiSA/cabal.project.local <<EOF
optimization: True

with-compiler: $(stack path --compiler-exe)
package precisa
   extra-lib-dirs: $KODIAK_LIB_DIR"
EOF


# While the rest of this could probably be done in Setup.hs
# I don't know how that works
echo Please run the following commands in your shell:
echo
echo export FILIB_ROOT=$FILIB_ROOT
echo export KODIAK_LIB_DIR=$KODIAK_LIB_DIR
echo export LD_LIBRARY_PATH="$KODIAK_LIB_DIR"':$LD_LIBRARY_PATH'
echo "(cd external/PRECiSA/PRECiSA && cabal v2-install)"
echo "precisa -h # test"
echo "echo 'extra-lib-dirs: [$KODIAK_LIB_DIR]' >> stack.yaml"
echo "stack build"
echo "stack exec FPCC-exe # test" 

