#!/bin/bash

ocamlopt -o eval main.ml

for t in *.cl ; do 
	./cool --type $t
	echo "type checked  $t.cl-type" ; 
done


for t in *.cl-type ; do
	
        ./cool --type $t >& output.reference </dev/null
	./eval $t >& ouput.student </dev/null
        if diff -b -B output.reference output.student >&/dev/null ; then
		echo "pass : $t"
	else 
		echo "fail : $t"
	fi
done
~     
