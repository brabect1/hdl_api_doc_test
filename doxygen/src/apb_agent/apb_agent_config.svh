//------------------------------------------------------------
//   Copyright 2010 Mentor Graphics Corporation
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------

/**
* Encapsulates APB agent configuration settings.
*
* The configuration settings include the usual UVC knobs (active mode, coverage
* collection status) and knobs specific to APB arbitration. An important part
* of the configuration instance is a refernce to the APB bus interface.
*
* The configuration instance is to be created during the build phase of
* the agent's parent component, which is typically an environment and associated
* with an agent instance through a keyword lookup in the UVM Configuration DB.
*/
class apb_agent_config extends uvm_object;

// UVM Factory Registration Macro
//
`uvm_object_utils(apb_agent_config)

//! Reference to the physical APB bus interface.
virtual apb_if APB;

//------------------------------------------
// Data Members
//------------------------------------------
//! Identifies the usage mode of the agent. In the UVM_ACTIVE state, the agent
//! provides all the components for full control and monitoring of the APB bus.
//! In the UVM_PASSIVE mode, the agent provides only the bus monitoring functions.
uvm_active_passive_enum active = UVM_ACTIVE;
//! Makes the agent collect the functional coverage.
bit has_functional_coverage = 0;
//! Sets the agent to include an APB RAM based scoreboard.
bit has_scoreboard = 0;

//! Identifies the number of select lines used in the APB bus interface.
int no_select_lines = 1;
//! Identifies the select line used by an APB slave controlled and/or observed
//! by the APB agent.
int apb_index = 0; 
//! Identifies the base address of an APB slave controlled and/or observed by
//! the APB agent.
logic[31:0] start_address[15:0];
//! @todo Missing description.
logic[31:0] range[15:0];

//------------------------------------------
// Methods
//------------------------------------------
// Standard UVM Methods:

/**
* Conventional constructor for UVM objects.
*/
extern function new(
    //! Name to be associated with the configuration instance in the UVM
    //! Configuration DB.
    string name = "apb_agent_config"
);

endclass: apb_agent_config

function apb_agent_config::new(string name = "apb_agent_config");
  super.new(name);
endfunction
