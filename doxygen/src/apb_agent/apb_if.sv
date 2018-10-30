/**
* APB bus interface with very simple property checking.
*/
interface apb_if(
    //! bus clock
    input PCLK,
    //! bus reset, active low
    input PRESETn
);

  //! bus address
  logic[31:0] PADDR;
  //! bus read data
  logic[31:0] PRDATA;
  //! bus write data
  logic[31:0] PWDATA;
  //! Slave select lines, active high.
  //! Only connect the ones that are needed.
  logic[15:0] PSEL;
  //! @todo missing description
  logic PENABLE;
  //! read/write control
  logic PWRITE;
  //! slave ready
  logic PREADY;

  property psel_valid;
    @(posedge PCLK)
    !$isunknown(PSEL);
  endproperty: psel_valid

  CHK_PSEL: assert property(psel_valid);

  COVER_PSEL: cover property(psel_valid);

endinterface: apb_if
