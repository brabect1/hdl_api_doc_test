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
* Executes a simple 32-bit APB write transaction.
*/
class apb_write_seq extends uvm_sequence #(apb_seq_item);

// UVM Factory Registration Macro
//
`uvm_object_utils(apb_write_seq)

//------------------------------------------
// Data Members (Outputs rand, inputs non-rand)
//------------------------------------------
//! Transaction address.
rand logic [31:0] addr;
//! Transaction data (to be written).
rand logic [31:0] data;

//------------------------------------------
// Constraints
//------------------------------------------



//------------------------------------------
// Methods
//------------------------------------------

// Standard UVM Methods:

/**
* Conventional UVM object constructor.
*/
extern function new(string name = "apb_write_seq");

/**
* Executes a single write transaction writing #data at the #addr address.
*/
extern task body;

endclass:apb_write_seq

function apb_write_seq::new(string name = "apb_write_seq");
  super.new(name);
endfunction

task apb_write_seq::body;
  apb_seq_item req = apb_seq_item::type_id::create("req");;

  begin
    start_item(req);
    req.we = 1;
    req.addr = addr;
    req.data = data;
    finish_item(req);
  end

endtask:body
