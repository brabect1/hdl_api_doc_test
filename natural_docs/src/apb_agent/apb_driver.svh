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
* Class: apb_driver
* Implements an APB bus master acting as the driver of an APB agent.
*
* The driver receives transactions through a pull port, normally connected
* to the agent's sequencer. The transactions are translated into APB bus
* transactions.
*
* This driver implementation supports only valid and properly framed bus
* transactions.
*
* The driver supports multiple bus slaves. The number of slaves and their
* address map is controlled through an agent's configuration obtained from
* the UVM Configuration DB during the build phase.
*
* @todo A more proper way to configure the driver is through a direct config
*       object assignment, rather than through the UVM Config DB.
*/
class apb_driver extends uvm_driver #(apb_seq_item, apb_seq_item);

// UVM Factory Registration Macro
//
`uvm_component_utils(apb_driver)

// Variable: apb_if
// Reference to the APB interface. The reference is obtained from the driver's
// configuration instance (and hence somewhat duplicates the information contained
// therein).
virtual apb_if APB;

//------------------------------------------
// Data Members
//------------------------------------------

// Variable: m_cfg
// Driver configuration. Normally this aliases with the parent agent configuration.
apb_agent_config m_cfg;
//------------------------------------------
// Methods
//------------------------------------------
/*
* Function: sel_lookup
* Looks up the <address> and returns a PSEL line index that should be activated.
* If the address is invalid, a non positive integer is returned to indicate an error.
*
* Parameters:
*   address - An APB address for which to find a slave index (within PSEL).
*/
extern function int sel_lookup(logic[31:0] address);
// Standard UVM Methods:

/*
* Function: new
* Conventional UVM component constructor.
*/
extern function new(string name = "apb_driver", uvm_component parent = null);
/*
* Function: run_phase
* Forks off a forever loop in which the driver pulls transactions and drives them
* on the APB bus.
*/
extern task run_phase(uvm_phase phase);
/*
* Function: build_phase
* Merely obtains the driver configuration from the UVM Configuration DB.
*/
extern function void build_phase(uvm_phase phase);


endclass: apb_driver

function apb_driver::new(string name = "apb_driver", uvm_component parent = null);
  super.new(name, parent);
endfunction

task apb_driver::run_phase(uvm_phase phase);
  apb_seq_item req;
  int psel_index;

  APB.PSEL <= 0;
  APB.PENABLE <= 0;
  APB.PADDR <= 0;
  // Wait for reset to clear
  @(posedge APB.PRESETn);

  forever
   begin
     APB.PSEL <= 0;
     APB.PENABLE <= 0;
     APB.PADDR <= 0;
     seq_item_port.get_next_item(req);
     repeat(req.delay)
       @(posedge APB.PCLK);
     psel_index = sel_lookup(req.addr);
     if(psel_index >= 0) begin
       APB.PSEL[psel_index] <= 1;
       APB.PADDR <= req.addr;
       APB.PWDATA <= req.data;
       APB.PWRITE <= req.we;
       @(posedge APB.PCLK);
       APB.PENABLE <= 1;
       while (!APB.PREADY)
         @(posedge APB.PCLK);
       if(APB.PWRITE == 0)
         begin
           req.data = APB.PRDATA;
         end
     end
     else begin
       `uvm_error("RUN", $sformatf("Access to addr %0h out of APB address range", req.addr))
       req.error = 1;
     end
     seq_item_port.item_done();
   end

endtask: run_phase

function void apb_driver::build_phase(uvm_phase phase);
  if(!uvm_config_db #(apb_agent_config)::get(this, "", "apb_agent_config", m_cfg)) begin
    `uvm_error("build_phase", "Unable to get apb_agent_config")
  end
endfunction: build_phase

function int apb_driver::sel_lookup(logic[31:0] address);
  for(int i = 0; i < m_cfg.no_select_lines; i++) begin
    if((address >= m_cfg.start_address[i]) && (address <= (m_cfg.start_address[i] + m_cfg.range[i]))) begin
      return i;
    end
  end
  return -1; // Error: Address not found
endfunction: sel_lookup
