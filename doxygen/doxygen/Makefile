# Copyright 2018 Tomas Brabec
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Path to the Doxygen binary.
WITH_DOXYGEN ?= doxygen

# Path to the Graphviz `dot` binary.
WITH_GRAPHVIZ_DOT ?= $(shell which bash)

# Path to the Intelligent DV (IDV) script for processing Doxygen template files
# and altering them with settings from *Delta Files*.
WITH_IDV_DOXY_SCRIPT ?= idv/idv_doxyfile_tmplconv.pl

# Path to the IDV Doxygen filter to yield SV support.
WITH_IDV_DOXY_FILTER ?= idv/idv_doxyfilter_sv.pl

# The source Doxygen template. To create a genuine one use `doxygen -g`.
DOXY_TEMPLATE := doxyfile/Doxyfile.template

# An intermediate template file created from the Doxygen Template by adding
# SV specifics. 
DOXY_SV_TEMPLATE := Doxyfile.sv.template

# Generic SV Doxygen settings.
DOXY_SV_DELTA := idv/idv_doxyfile_sv.delta

# This is the final template created from the SV specific template by applying
# project specific settings (i.e. delta file).
DOXY_PRJ_TEMPLATE := Doxyfile.prj.template

# Project specific Doxygen settings.
DOXY_PRJ_DELTA := Doxyfile.prj.delta

# Create a wrapper script for the IDV filter.
dofilter.sh: $(WITH_IDV_DOXY_FILTER)
	@echo '#!/bin/bash' > $@
	@echo '$(WITH_IDV_DOXY_FILTER) --package_mode $$1' >> $@
	@chmod ug+x $@

# As the original IDV code is distributed under GPLv3, we get it online
# not to spoil Apache 2.0 licensing.
idv/idv_doxyfile_tmplconv.pl:
	mkdir -p idv && cd idv && \
    wget https://raw.githubusercontent.com/SeanOBoyle/DoxygenFilterSystemVerilog/master/scripts/idv_doxyfile_tmplconv.pl && \
    chmod ug+x idv_doxyfile_tmplconv.pl

# As the original IDV code is distributed under GPLv3, we get it online
# not to spoil Apache 2.0 license.
idv/idv_doxyfilter_sv.pl:
	mkdir -p idv  && cd idv && \
    wget https://raw.githubusercontent.com/SeanOBoyle/DoxygenFilterSystemVerilog/master/filter/idv_doxyfilter_sv.pl && \
    chmod ug+x idv_doxyfilter_sv.pl

# As the original IDV code is distributed under GPLv3, we get it online
# not to spoil Apache 2.0 license.
idv/idv_doxyfile_sv.delta:
	mkdir -p idv  && cd idv && \
    wget https://raw.githubusercontent.com/SeanOBoyle/DoxygenFilterSystemVerilog/master/doxyfile/idv_doxyfile_sv.delta && \
    wget https://raw.githubusercontent.com/SeanOBoyle/DoxygenFilterSystemVerilog/master/doxyfile/idv_doxylayout.xml

# Create a generic SV Doxygen Template.
$(DOXY_SV_TEMPLATE): dofilter.sh $(WITH_IDV_DOXY_SCRIPT) $(DOXY_SV_DELTA) $(DOXY_TEMPLATE)
	$(WITH_IDV_DOXY_SCRIPT) \
        --path_prj $(abspath ..) \
        --path_doxyscr $(abspath .) \
        --template $(DOXY_TEMPLATE) \
        --delta $(DOXY_SV_DELTA) \
        --output $@

# Create a ptoject specific Doxygen Template.
$(DOXY_PRJ_TEMPLATE): dofilter.sh $(WITH_IDV_DOXY_SCRIPT) $(DOXY_PRJ_DELTA) $(DOXY_SV_TEMPLATE)
	$(WITH_IDV_DOXY_SCRIPT) \
        --path_prj $(abspath ..) \
        --path_doxyscr $(abspath .) \
        --template $(DOXY_SV_TEMPLATE) \
        --delta $(DOXY_PRJ_DELTA) \
        --output $@

.PHONY: doc
doc: $(DOXY_PRJ_TEMPLATE)
#	mkdir -p ../doc/api && $(DOXYGEN) $(DOXY_PRJ_TEMPLATE)

.PHONY: clean
clean:
	rm -rf ../doc/api idv/ dofilter.sh $(DOXY_PRJ_TEMPLATE) $(DOXY_SV_TEMPLATE)

