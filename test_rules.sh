#!/bin/bash

res=""

#res+=$(qsl_prove -p -t 1 -test)
#res+=$(qsl_prove -S "a!=c * b!=c * ListTmp(a,b) * b->c |- a!=c * a->z' * ListTmp(z',c)" -d -s -t 3 -p)
#res+=$(qsl_prove -S "P(a,b) |- Q(a,b)" -d -s -t 1 -p)
#res+=$(qsl_prove -S "ListLenTmp(a,b)*b->c |- ListLenTmp(a,c)" -test -s -t 400 -p -d)
res+=$(qsl_prove -test -t 10 -M 0 -s)

echo "${res}" > test_rules_res.txt