#!/bin/bash

Sequents[0]='x->y * RList(y,z) |- RList(x,z)'
Sequents[1]='RList(x,y) * RList(y,z) |- RList(x,z)'
Sequents[2]='List(x,y) * y->z |- List(x,z)'
Sequents[3]='List(x,y) * List(y,z) |- List(x,z)'
Sequents[4]='PeList(x,y) * y->z |- PeList(x,z)'
Sequents[5]='PeList(x,y) * PeList(y,z) |- PeList(x,z)'
Sequents[6]='DLL(x,y,z,w) |- SLL(x,y)'
Sequents[7]='DLL(x,y,z,w) |- BSLL(z,w)'
Sequents[8]='DLL(x,y,z,w) * DLL(a,x,w,b) |- DLL(a,y,z,b)'
Sequents[9]='ListO(x,y) * ListO(y,z) |- ListE(x,z)'
Sequents[10]='ListE(x,y) * ListE(y,z) |- ListE(x,z)'
Sequents[11]='ListE(x,y) * ListO(y,z) |- ListO(x,z)'
Sequents[12]='BinListFirst(x) |- BinTree(x)'
Sequents[13]='BinListSecond(x) |- BinTree(x)'
Sequents[14]='BinPath(x,z) * BinPath(z,y) |- BinPath(x,y)'
Sequents[15]='BinPath(x,y) |- BinTreeSeg(x,y)'
Sequents[16]='BinTreeSeg(x,z) * BinTree(y) |- BinTree(x)'
Sequents[17]='x!=z * x->y * ls(y,z) |- ls(x,z)'
Sequents[18]='ls(x,y) * ls(y,nil) |- ls(x,nil)'
Sequents[19]='ListE(x,y) \/ ListO(x,y) |- List(x,y)'

qsl_res=""
sl_res=""

for ((i=0; i < ${#Sequents[@]}; i++))
do
    Sequent="${Sequents[$i]}"
    #echo "${Sequent}"
    qsl_res+=$(qsl_prove -S "${Sequent}" -D examples/sl.defs -p -t 1)
    sl_res+=$(sl_prove -S "${Sequent}" -p -t 1)
    qsl_res+=$'\n \n \n -----------------------NEEXT------------------------- \n \n \n'
    sl_res+=$'\n \n \n -----------------------NEEXT------------------------- \n \n \n'
    #read -p ""
done

echo "${sl_res}" > sl_test_res.txt
echo "${qsl_res}" > qsl_test_res.txt