mkdir obj
pushd chapter1
coqc Basics.v
cp *.vo ../obj
popd
pushd chapter2-induction
coqc Induction.v
cp *.vo ../obj
popd
cp ./obj/*.vo ./chapter1/ 
cp ./obj/*.vo ./chapter2-induction/
cp ./obj/*.vo ./chapter3-lists/
