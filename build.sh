mkdir obj
pushd chapter1
coqc Basics.v
cp *.vo ../obj
popd
pushd chapter2-induction
coqc Induction.v
cp *.vo ../obj
popd
pushd chapter3-lists
coqc NatList.v
cp *.vo ../obj
popd
pushd chapter4-poly
coqc Poly.v
cp *.vo ../obj
popd
pushd chapter5-tactics
popd
pushd chapter6-logic
coqc Logic.v
cp *.vo ../obj
popd
cp ./obj/*.vo ./chapter1/ 
cp ./obj/*.vo ./chapter2-induction/
cp ./obj/*.vo ./chapter3-lists/
cp ./obj/*.vo ./chapter4-poly/
cp ./obj/*.vo ./chapter5-tactics/
