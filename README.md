hdl_api_doc_test
================

This repository is to test some API Doc generators for SystemVerilog code and provide example setup and output.

Doxygen
-------

no direct support ... utilizes a filter that performs on-fly conversion to C++ ... originally developed by Inteligent DV
... now resides on Github https://github.com/SeanOBoyle/DoxygenFilterSystemVerilog ... no longer maintained

Natural Docs
------------

### Running `nd` Example ###

```bash
# Install NaturalDocs 1.x
wget https://downloads.sourceforge.net/project/naturaldocs/Stable%20Releases/1.52/NaturalDocs-1.52.zip
mkdir nd && cd nd && unzip ../NaturalDocs-1.52.zip && export WITH_ND=$(pwd)/NaturalDocs

# Generate API doc
cd natural_docs/nd_proj/ && make

# View API doc
firefox ../doc/api/index.html
```

