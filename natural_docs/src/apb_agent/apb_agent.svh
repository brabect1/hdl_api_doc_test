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

/*
* Class: apb_agent
* Implements the UVC Agent component for Amba Peripheral Bus (APB).
*
* The implementation comes from the Verification Cookbook at the Verification
* Academy site (https://verificationacademy.com/). It follows the conventional
* UVC agent structure.
*
* The agent consists of the following parts: Driver, monitor, sequencer and
* a coverage collection class. The agent is configured through a specific
* configuration object. The agent exports its monitor's analysis port.
*/
class apb_agent extends uvm_component;

// UVM Factory Registration Macro
//
`uvm_component_utils(apb_agent)

//------------------------------------------
// Data Members
//------------------------------------------

// Variable: m_cfg
// Agent configuration. It will be obtained from the UVM Configuration DB during
// the build phase, under the keyword `apb_agent_config`.
apb_agent_config m_cfg;

//------------------------------------------
// Component Members
//------------------------------------------

// Variable: ap
// Analysis port exported from the agent's monitor component.
uvm_analysis_port #(apb_seq_item) ap;

// Variable: m_monitor
// An instance of the APB monitor. This component is always present (i.e. even
// in the passive mode).
apb_monitor   m_monitor;

// Variable: m_sequencer
// An instance of the APB sequencer. It is present only in the active mode.
apb_sequencer m_sequencer;

// Variable: m_driver
// An instance of the APB driver. It is present only in the active mode.
apb_driver    m_driver;

// Variable: m_fcov_monitor
// An instance collecting functional coverage. It is present only if the agent
// was configured with enabled coverage collection.
apb_coverage_monitor m_fcov_monitor;
//------------------------------------------
// Methods
//------------------------------------------

// Standard UVM Methods:

/*
* Function: new
* Implements the default UVM component constructor.
*/
extern function new(
    //! Name of the agent component. This name will be associated with the agent
    //! instance and may be used for looking up the instance in the UVM Config DB.
    string name = "apb_agent",
    //! Reference to a parent component, which the agent instance will be a part of.
    uvm_component parent = null
);

// Function: build_phase
// Builds individual components based on configured agent's settings.
extern function void build_phase(
    //! Reference to the build phase instance.
    uvm_phase phase
);

// Function: connect_phase
// Connects all the components that have been created suring the build phase.
extern function void connect_phase(
    //! Reference to the connect phase instance.
    uvm_phase phase
);

endclass: apb_agent


function apb_agent::new(string name = "apb_agent", uvm_component parent = null);
  super.new(name, parent);
endfunction

function void apb_agent::build_phase(uvm_phase phase);
  if(!uvm_config_db #(apb_agent_config)::get(this, "", "apb_agent_config", m_cfg)) begin
    `uvm_error("build_phase", "APB agent config not found")
  end
  // Monitor is always present
  m_monitor = apb_monitor::type_id::create("m_monitor", this);
  // Only build the driver and sequencer if active
  if(m_cfg.active == UVM_ACTIVE) begin
    m_driver = apb_driver::type_id::create("m_driver", this);
    m_sequencer = apb_sequencer::type_id::create("m_sequencer", this);
  end
  if(m_cfg.has_functional_coverage) begin
    m_fcov_monitor = apb_coverage_monitor::type_id::create("m_fcov_monitor", this);
  end
endfunction: build_phase

function void apb_agent::connect_phase(uvm_phase phase);
  m_monitor.APB = m_cfg.APB;
  m_monitor.apb_index = m_cfg.apb_index;
  ap = m_monitor.ap;
  // Only connect the driver and the sequencer if active
  if(m_cfg.active == UVM_ACTIVE) begin
    m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    m_driver.APB = m_cfg.APB;
  end
  if(m_cfg.has_functional_coverage) begin
    m_monitor.ap.connect(m_fcov_monitor.analysis_export);
  end

endfunction: connect_phase
