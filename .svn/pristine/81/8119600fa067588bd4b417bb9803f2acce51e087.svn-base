#!/bin/sh

set -e

VERSION=1660
test -z $1 && echo "usage : $0 <svn username to checkout>" && exit 1
USER=$1

set -x
#############################################
# we clone

svn checkout svn+ssh://$USER@scm.gforge.inria.fr/svnroot/simsoc-cert -r $VERSION

#############################################
# we enter

cd simsoc-cert

#############################################
# we copy

DESTINATION=correctness_ADC
D0=devel/tuong/simsoc-cert
D1=devel/xiaomu
D2=$D0/correctness_ADC

mkdir                    $DESTINATION

cp $D1/adc_compcert.v    \
   $D2/make.sh           \
   $D2/README            \
                         $DESTINATION
cp $D1/test_csem_draft.v $DESTINATION/correctness_ADC.v
cp $D0/INSTALL           .

#############################################
# we remove

rm $(find . -name TODO)
rm -rf arm6/elf2coq arm6/simlight2 arm6/test arm6/arm6.pdf
rm -rf arm7
rm -rf coq/coq-bugs 
rm -rf devel
rm -rf papers

rm -rf sh4/coq
mv sh4/parsing/manual.ml sh4 && rm sh4/parsing/* && mv sh4/manual.ml sh4/parsing
rm -rf sh4/test
rm sh4/* || true

rm simgen/run_test.sh

rm -rf tools/coqdoc tools/dependot tools/Makefile

rm README.devel

#############################################
# we exit

cd ..

#############################################
# we back up

tar czvfh simsoc-cert_$VERSION.tar.gz --exclude-vcs simsoc-cert

#############################################


# cd simsoc-cert
# less INSTALL
# ./configure /path/to/compcert 

# make -C arm6/coq
# less arm6/coq/Arm6_Inst.v

# make -C arm6/simlight all.vo
# less arm6/simlight/all.v

# cd equiv_proof_adc && ./make.sh && echo 'The equivalence proof has been typed.'
