This is a Doxygen project setup derived from [IntelligentDV Test Project](https://github.com/SeanOBoyle/DoxygenFilterSystemVerilog).
Some files have been recreted to let them be distribited under the Apache 2.0 license (as the original
IntelligentDV code is licensed under GPLv3 or later). The other IDV files are `wget` from their
original repository during the build process.

Note that this is a minimal working example. For reuse, one would automate generation of the
Project Template Delta file, `Doxyfile.prj.delta`, to avoid needing to edit it every time.

Usage:

    make doc [WITH_DOXYGEN=...] [WITH_GRAPHVIZ_DOT=...]

