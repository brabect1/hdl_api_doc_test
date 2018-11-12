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
* Class: apb_coverage_monitor
* Collects basic functional coverage information observed by an APB agent.
*
* An instance of the coverage monitor will be part of the agent only if its
* configuration knob, <apb_agent_config>::has_functional_coverage, is set.
*
* The coverage monitor extends uvm_subscriber so it can be connected to
* <apb_monitor>.
*/
class apb_coverage_monitor extends uvm_subscriber #(apb_seq_item);

// UVM Factory Registration Macro
//
`uvm_component_utils(apb_coverage_monitor);


//------------------------------------------
// Cover Group(s)
//------------------------------------------

//! Covers that both read and write transactions were observed.
covergroup apb_cov;
OPCODE: coverpoint analysis_txn.we {
  bins write = {1};
  bins read = {0};
}
// To do:
// Monitor is not returning delay info
endgroup

//------------------------------------------
// Component Members
//------------------------------------------
//! Transaction instance to be covered. This merely a reference to the last
//! transaction received from the APB monitor this coverage monitor instance
//! connects to.
apb_seq_item analysis_txn;

//------------------------------------------
// Methods
//------------------------------------------

// Standard UVM Methods:

/*
* Function: new
* Conventional UVM component constructor.
*/
extern function new(string name = "apb_coverage_monitor", uvm_component parent = null);

/*
* Function: write
* Samples coverage on the received transaction.
*
* This method implements the UVM subsciber's observe method.
*
* Paramaters:
*   t - Transaction on which to sample the coverage.
*/
extern function void write(
    T t
);

/*
* Function: report_phase
* Reports collected coverage during the corresponding phase of UVM test execution.
*
* Parameters:
*   phase - Reference to the corresponding phase instance.
*/
extern function void report_phase(
    uvm_phase phase
);

endclass: apb_coverage_monitor

function apb_coverage_monitor::new(string name = "apb_coverage_monitor", uvm_component parent = null);
  super.new(name, parent);
  apb_cov = new();
endfunction

function void apb_coverage_monitor::write(T t);
  analysis_txn = t;
  apb_cov.sample();
endfunction:write

function void apb_coverage_monitor::report_phase(uvm_phase phase);
// Might be a good place to do some reporting on no of analysis transactions sent etc

endfunction: report_phase
