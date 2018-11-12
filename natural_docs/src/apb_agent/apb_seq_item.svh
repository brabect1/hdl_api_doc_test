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
* Class: apb_seq_item
* Base APB transaction.
*
* The transaction is used by both <apb_driver> and <apb_monitor>. For the driver, the
* transaction type works for request and response.
*
* Implements the basic transaction attributes (address, data, read/write control).
* More advanced attributes (e.g. error injection, byte enables, etc.) are not
* supported.
*/
class apb_seq_item extends uvm_sequence_item;

// UVM Factory Registration Macro
//
`uvm_object_utils(apb_seq_item)

//------------------------------------------
// Data Members (Outputs rand, inputs non-rand)
//------------------------------------------

// Variable: addr
// Bus address.
rand logic[31:0] addr;

// Variable: data
// Read/write data.
rand logic[31:0] data;

// Variable: we
// Read/write (=0/1) transaction type.
rand logic we;

// Variable: delay
// Number of APB clock cycles since the apb_driver received the transaction to
// the actual start of the transaction on the APB bus.
rand int delay;

// Variable: error
// Indicates a failure to drive the item on the bus.
bit error;

//------------------------------------------
// Constraints
//------------------------------------------

// Constrains the randomized transactions for double-word alignment.
constraint addr_alignment {
  addr[1:0] == 0;
}

constraint delay_bounds {
  delay inside {[1:20]};
}

//------------------------------------------
// Methods
//------------------------------------------

// Standard UVM Methods:

/*
* Function: new
* Conventional UVM object constructor.
*/
extern function new(string name = "apb_seq_item");

/*
* Function: do_copy
* Implements a class specific deep copy.
*/
extern function void do_copy(uvm_object rhs);

/*
* Function: do_compare
* Implements a class specific comparison.
*/
extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

/*
* Function: convert2string
* Implements a class specific string conversion.
*/
extern function string convert2string();

/*
* Function: do_print
* Implements a class specific printing.
*/
extern function void do_print(uvm_printer printer);

/*
* Function: do_record
* Implements a class specific recording.
*/
extern function void do_record(uvm_recorder recorder);

endclass:apb_seq_item

function apb_seq_item::new(string name = "apb_seq_item");
  super.new(name);
endfunction

function void apb_seq_item::do_copy(uvm_object rhs);
  apb_seq_item rhs_;

  if(!$cast(rhs_, rhs)) begin
    `uvm_fatal("do_copy", "cast of rhs object failed")
  end
  super.do_copy(rhs);
  // Copy over data members:
  addr = rhs_.addr;
  data = rhs_.data;
  we = rhs_.we;
  delay = rhs_.delay;

endfunction:do_copy

function bit apb_seq_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  apb_seq_item rhs_;

  if(!$cast(rhs_, rhs)) begin
    `uvm_error("do_copy", "cast of rhs object failed")
    return 0;
  end
  return super.do_compare(rhs, comparer) &&
         addr == rhs_.addr &&
         data == rhs_.data &&
         we   == rhs_.data;
  // Delay is not relevant to the comparison
endfunction:do_compare

function string apb_seq_item::convert2string();
  string s;

  $sformat(s, "%s\n", super.convert2string());
  // Convert to string function reusing s:
  $sformat(s, "%s\n addr\t%0h\n data\t%0h\n we\t%0b\n delay\t%0d\n", s, addr, data, we, delay);
  return s;

endfunction:convert2string

function void apb_seq_item::do_print(uvm_printer printer);
  if(printer.knobs.sprint == 0) begin
    $display(convert2string());
  end
  else begin
    printer.m_string = convert2string();
  end
endfunction:do_print

function void apb_seq_item:: do_record(uvm_recorder recorder);
  super.do_record(recorder);

  // Use the record macros to record the item fields:
  `uvm_record_field("addr", addr)
  `uvm_record_field("data", data)
  `uvm_record_field("we", we)
  `uvm_record_field("delay", delay)
endfunction:do_record
