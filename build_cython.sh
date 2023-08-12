#!/bin/bash

rm -vf isogeny_weber/*python*so
cd isogeny_weber
python <<EOF
from sage.misc.cython import cython
cython("ntlext.pyx", create_local_so_file=True)
cython("flintext.pyx", create_local_so_file=True)
EOF
