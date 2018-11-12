hdl_api_doc_test
================

This repository is to test some API Doc generators for SystemVerilog code and provide example setup and output.

Doxygen
-------

no direct support ... utilizes a filter that performs on-fly conversion to C++ ... originally developed by Inteligent DV
... now resides on Github https://github.com/SeanOBoyle/DoxygenFilterSystemVerilog ... no longer maintained

Natural Docs 1.x
----------------

Natural Docs does not need to fully comprehend a language sysntax, but only needs how to identify
comments and certain syntax attributes. This makes the tool applicable to a large number of languages
with very little porting effort.

Natural Docs has been used to generate API documentation for UVM. Hence one can use UVM code
distribution as a reference (e.g. https://github.com/chiggs/UVM) and adapt it to her needs.

### Usage ###

Natural Docs ... project ... Languages.txt ... Menu.txt

### Running `nd` Example ###

Output of the following process on the prepared example is [here](natural_docs/generated/api/index.html).

```bash
# Install NaturalDocs 1.x
wget https://downloads.sourceforge.net/project/naturaldocs/Stable%20Releases/1.52/NaturalDocs-1.52.zip
mkdir nd && cd nd && unzip ../NaturalDocs-1.52.zip && export WITH_ND=$(pwd)/NaturalDocs

# Generate API doc
cd natural_docs/nd_proj/ && make

# View API doc
firefox ../doc/api/index.html
```

Comparison
----------

The following tables compares SystemVerilog features.

Feature    | Doxygen 1.82  | Natural Docs 1.52   | Natural Docs 2.x
-----------|---------------|---------------------|--------------------
JavaDoc Markup |  Yes          | No (for SV)         | No (for SV)
Text Markup   |  MarkDown     | ND Custom           | ND Custom 
Images     |  Yes          |  Yes                | Yes
Code Snippets |  Yes         |  Yes                 | Yes
Extra Doc  |  Yes          |  Yes                | Yes
ToDo Lists |  Yes          |  No                 | ?
Custom Menu   |  No           |  Yes                | No

