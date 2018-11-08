/*
* Interface: apb_if
* APB bus interface with very simple property checking.
*
* Inputs:
*   PCLK - bus clock
*   PRESETn - bus reset, active low
*/
interface apb_if(
    input PCLK,
    input PRESETn
);

  // Variable: PADDR
  // bus address
  logic[31:0] PADDR;
  // Variable: PRDATA
  // bus read data
  logic[31:0] PRDATA;
  // Variable: PWDATA
  // bus write data
  logic[31:0] PWDATA;
  // Variable: PSEL
  // Slave select lines, active high.
  // Only connect the ones that are needed.
  logic[15:0] PSEL;
  // Variable: PENABLE
  // @todo missing description
  logic PENABLE;
  // Variable: PWRITE
  // read/write control
  logic PWRITE;
  // Variable: PREADY
  // slave ready
  logic PREADY;

  property psel_valid;
    @(posedge PCLK)
    !$isunknown(PSEL);
  endproperty: psel_valid

  CHK_PSEL: assert property(psel_valid);

  COVER_PSEL: cover property(psel_valid);

endinterface: apb_if
