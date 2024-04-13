`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  // TODO: copy your RegFile code here
  localparam int NumRegs = 32;
  genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  assign regs[0]  = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  generate
    for (i = 0; i < NumRegs; i++) begin : g_loop
      always_ff @(posedge clk) begin
        if (rst) begin
          regs[i] <= 32'd0;
        end else begin
          if (we && rd == i && rd != 0) begin
            regs[i] <= rd_data;
          end
        end
      end
    end
  endgenerate

endmodule

/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    // parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  localparam bit [1:0] ResponseOkay = 2'b00;
  // localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
  end
`endif

  // TODO: changes will be needed throughout this module

  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
      // start out ready to accept incoming reads
      insn.ARREADY <= 1;
      data.ARREADY <= 1;
      // start out ready to accept an incoming write
      data.AWREADY <= 1;
      data.WREADY  <= 1;
      // drive RVALID and BVALID low
      insn.RVALID  <= 0;
      data.RVALID  <= 0;
      data.BVALID  <= 0;
    end else begin
      // READS
      if (insn.ARVALID && insn.ARREADY) begin
        insn.RDATA  <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]];
        insn.RRESP  <= ResponseOkay;
        insn.RVALID <= 1;
      end

      if (!insn.ARVALID && insn.RVALID) begin
        insn.RVALID <= 0;
      end

      if (data.ARVALID && data.ARREADY) begin
        data.RDATA  <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
        data.RRESP  <= ResponseOkay;
        data.RVALID <= 1;
      end

      if (!data.ARVALID && data.RVALID) begin
        insn.RVALID <= 0;
      end

      // WRITES
      if (data.AWREADY && data.AWVALID && data.WREADY && data.WVALID) begin
        if (data.WSTRB[0] == 1) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][7:0] <= data.WDATA[7:0];
          data.BRESP <= ResponseOkay;
          data.BVALID <= 1;
        end
        if (data.WSTRB[1] == 1) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][15:8] <= data.WDATA[15:8];
          data.BRESP <= ResponseOkay;
          data.BVALID <= 1;
        end
        if (data.WSTRB[2] == 1) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][23:16] <= data.WDATA[23:16];
          data.BRESP <= ResponseOkay;
          data.BVALID <= 1;
        end
        if (data.WSTRB[3] == 1) begin
          mem_array[data.AWADDR[AddrMsb:AddrLsb]][31:24] <= data.WDATA[31:24];
          data.BRESP <= ResponseOkay;
          data.BVALID <= 1;
        end
      end

      if (!data.AWVALID && data.BVALID) begin
        data.BVALID <= 0;
      end
    end
  end

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,
  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] alu_result;
  // relevant only for stores
  logic [`REG_SIZE] rs2_data;
} stage_memory_t;

/** state at the start of Writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] alu_result;
} stage_writeback_t;

module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    // Start by replacing this interface to imem...
    // output logic [`REG_SIZE] pc_to_imem,
    // input wire [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // Once imem is working, replace this interface to dmem...
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,
    // ...with this AXIL one
    // axi_if.manager dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // TODO: your code here
  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  // wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (loadStall) begin
      f_pc_current <= f_pc_current;
    end else if (fenceStall) begin
      f_pc_current <= f_pc_current;
    end else if (divStall) begin
      f_pc_current <= f_pc_current;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      if (branch_bool > 0) begin
        f_pc_current <= branch_taken;
      end else begin
        f_pc_current <= f_pc_current + 4;
      end
    end
  end

  // send PC to imem
  // assign pc_to_imem = f_pc_current;
  // assign f_insn = insn_from_imem;

  // USE AXIL
  always_comb begin
    imem.ARVALID = 1;
    imem.ARADDR  = f_pc_current;
  end

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (0),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET};
    end else if (loadStall) begin
      decode_state <= '{
          pc: decode_state.pc,
          insn: decode_state.insn,
          cycle_status: decode_state.cycle_status
      };
    end else if (fenceStall) begin
      decode_state <= '{
          pc: decode_state.pc,
          insn: decode_state.insn,
          cycle_status: decode_state.cycle_status
      };
    end else if (divStall) begin
      decode_state <= '{
          pc: decode_state.pc,
          insn: decode_state.insn,
          cycle_status: decode_state.cycle_status
      };
    end else begin
      decode_state <= '{
          pc: branch_bool > 0 ? 0 : f_pc_current,
          insn: branch_bool > 0 ? 0 : imem.RVALID ? imem.RDATA : 0,
          cycle_status: branch_bool > 0 ? CYCLE_TAKEN_BRANCH : f_cycle_status
      };
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("C")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  // instatiate register file data
  logic [`REG_SIZE] regfile_rs1_data;
  logic [`REG_SIZE] regfile_rs2_data;
  logic [`REG_SIZE] regfile_rd_data;

  // decode instruction
  // components of the instruction
  wire [6:0] d_insn_funct7;
  wire [4:0] d_insn_rs2;
  wire [4:0] d_insn_rs1;
  wire [2:0] d_insn_funct3;
  wire [4:0] d_insn_rd;
  wire [`OPCODE_SIZE] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd, d_insn_opcode} = decode_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] d_imm_i;
  assign d_imm_i = decode_state.insn[31:20];
  wire [ 4:0] d_imm_shamt = decode_state.insn[24:20];

  // S - stores
  wire [11:0] d_imm_s;
  assign d_imm_s[11:5] = d_insn_funct7, d_imm_s[4:0] = d_insn_rd;

  // B - conditionals
  wire [12:0] d_imm_b;
  assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7,
      {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd,
      d_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] d_imm_j;
  assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {
    decode_state.insn[31:12], 1'b0
  };

  wire [`REG_SIZE] d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  wire [`REG_SIZE] d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  wire [`REG_SIZE] d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  wire [`REG_SIZE] d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  logic regfile_we;

  // instatiate register file
  RegFile rf (
      .clk(clk),
      .rst(rst),
      .we(regfile_we),
      .rd(w_insn_rd),
      .rs1(d_insn_rs1),
      .rs2(d_insn_rs2),
      .rd_data(regfile_rd_data),
      .rs1_data(regfile_rs1_data),
      .rs2_data(regfile_rs2_data)
  );

  // WD bypass
  logic [31:0] wd_bypass_rs1;
  logic [31:0] wd_bypass_rs2;

  always_comb begin
    wd_bypass_rs1 = regfile_rs1_data;
    wd_bypass_rs2 = regfile_rs2_data;

    if (w_insn_rd != 0 && writeback_state.cycle_status == CYCLE_NO_STALL && regfile_we == 1 && d_insn_rs1 == w_insn_rd) begin
      wd_bypass_rs1 = writeback_state.alu_result;
    end

    if (w_insn_rd != 0 && writeback_state.cycle_status == CYCLE_NO_STALL && regfile_we == 1 && d_insn_rs2 == w_insn_rd) begin
      wd_bypass_rs2 = writeback_state.alu_result;
    end

  end

  logic illegal_insn;

  logic loadStall;

  // check for load-to-use stall
  always_comb begin
    loadStall = 1'b0;
    if (execute_state.insn[6:0] == OpcodeLoad && execute_state.cycle_status == CYCLE_NO_STALL) begin
      if (d_insn_rs1 == e_insn_rd || d_insn_rs2 == e_insn_rd) begin
        loadStall = 1'b1;
        case (decode_state.insn[6:0])
          OpcodeLui: begin
            loadStall = 1'b0;
          end
          OpcodeAuipc: begin
            loadStall = 1'b0;
          end
          OpcodeRegImm: begin
            if (d_insn_rs1 != e_insn_rd) begin
              loadStall = 1'b0;
            end
          end
          OpcodeRegReg: begin
          end
          OpcodeLoad: begin
            if (d_insn_rs1 != e_insn_rd) begin
              loadStall = 1'b0;
            end
          end
          OpcodeStore: begin
            // handle WM bypass (we don't want to stall)
            if (d_insn_rs2 == e_insn_rd && d_insn_rs1 != e_insn_rd) begin
              loadStall = 1'b0;
            end
          end
          OpcodeJal: begin
            loadStall = 1'b0;
          end
          OpcodeJalr: begin
            if (d_insn_rs1 != e_insn_rd) begin
              loadStall = 1'b0;
            end
          end
          OpcodeBranch: begin
          end
          OpcodeEnviron: begin
            loadStall = 1'b0;
          end
          OpcodeMiscMem: begin
            loadStall = 1'b0;
          end
          default: begin
            loadStall = 1'b0;
          end
        endcase
      end
    end
  end

  logic fenceStall;

  always_comb begin
    fenceStall = 1'b0;
    if ((execute_state.insn[6:0] == OpcodeStore && execute_state.cycle_status == CYCLE_NO_STALL) || (memory_state.insn[6:0] == OpcodeStore && memory_state.cycle_status == CYCLE_NO_STALL)) begin
      if (decode_state.insn[6:0] == OpcodeMiscMem && (decode_state.insn[14:12] == 3'b000 || decode_state.insn[14:12] == 3'b001)) begin
        fenceStall = 1'b1;
      end
    end
  end

  logic divStall;
  always_comb begin
    divStall = 1'b0;
    if (execute_state.insn[6:0] == OpcodeRegReg && execute_state.insn[14:12] >= 4 && execute_state.insn[31:25] == 1 && execute_state.cycle_status == CYCLE_NO_STALL) begin
      case (decode_state.insn[6:0])
        OpcodeLui: begin
        end
        OpcodeAuipc: begin
        end
        OpcodeRegImm: begin
          if (d_insn_rs1 == e_insn_rd) begin
            divStall = 1'b1;
          end
        end
        OpcodeRegReg: begin
          if (d_insn_rs1 == e_insn_rd || d_insn_rs2 == e_insn_rd) begin
            divStall = 1'b1;
          end
        end
        OpcodeLoad: begin
          if (d_insn_rs1 == e_insn_rd) begin
            divStall = 1'b1;
          end
        end
        OpcodeStore: begin
          if (d_insn_rs1 == e_insn_rd || d_insn_rs2 == e_insn_rd) begin
            divStall = 1'b1;
          end
        end
        OpcodeJal: begin
        end
        OpcodeJalr: begin
          if (d_insn_rs1 == e_insn_rd) begin
            divStall = 1'b1;
          end
        end
        OpcodeBranch: begin
          if (d_insn_rs1 == e_insn_rd || d_insn_rs2 == e_insn_rd) begin
            divStall = 1'b1;
          end
        end
        OpcodeEnviron: begin
        end
        OpcodeMiscMem: begin
        end
        default: begin
        end
      endcase
    end
  end

  // setup for register file write
  always_comb begin
    illegal_insn = 1'b0;
    // halt = 1'b0;
    if (decode_state.cycle_status == CYCLE_NO_STALL) begin
      case (d_insn_opcode)
        OpcodeLui: begin
        end
        OpcodeRegImm: begin
          case (decode_state.insn[14:12])
            // addi
            3'b000: begin
            end
            // slti
            3'b010: begin
            end
            // sltiu
            3'b011: begin
            end
            // xori
            3'b100: begin
            end
            // ori
            3'b110: begin
            end
            // andi
            3'b111: begin
            end
            // slli
            3'b001: begin
            end
            // srli & srai
            3'b101: begin
              if (decode_state.insn[31:25] == 7'd0) begin
              end else
              if (decode_state.insn[31:25] == 7'b0100000) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeRegReg: begin
          case (decode_state.insn[14:12])
            // add & sub & mul
            3'b000: begin
              // add
              if (decode_state.insn[31:25] == 7'b0) begin
                // sub
              end else if (decode_state.insn[31:25] == 7'b0100000) begin
                // mul
              end else
              if (decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // sll & mulh
            3'b001: begin
              // sll
              if (decode_state.insn[31:25] == 7'd0) begin
              end  // mulh
              else
              if (decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // slt & mulhsu
            3'b010: begin
              // slt
              if (decode_state.insn[31:25] == 7'd0) begin
              end  // mulhsu
              else
              if (decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // sltu & mulhu
            3'b011: begin
              // sltu
              if (decode_state.insn[31:25] == 7'd0) begin
              end  // mulhu
              else
              if (decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // xor
            3'b100: begin
              if (decode_state.insn[31:25] == 7'd0 || decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // srl & sra
            3'b101: begin
              if (decode_state.insn[31:25] == 7'd0) begin
              end else
              if (decode_state.insn[31:25] == 7'b0100000) begin
              end else
              if (decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // or
            3'b110: begin
              if (decode_state.insn[31:25] == 7'd0 || decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            // and
            3'b111: begin
              if (decode_state.insn[31:25] == 7'd0 || decode_state.insn[31:25] == 7'd1) begin
              end else begin
                illegal_insn = 1'b1;
              end
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeBranch: begin
          case (decode_state.insn[14:12])
            // beq
            3'b000: begin
              if (e_bypass_rs1 == e_bypass_rs2) begin
              end
            end
            // bne
            3'b001: begin
              if (e_bypass_rs1 != e_bypass_rs2) begin
              end
            end
            // blt
            3'b100: begin
              if ($signed(e_bypass_rs1) < $signed(e_bypass_rs2)) begin
              end
            end
            // bge
            3'b101: begin
              if ($signed(e_bypass_rs1) >= $signed(e_bypass_rs2)) begin
              end
            end
            // bltu
            3'b110: begin
              if (e_bypass_rs1 < e_bypass_rs2) begin
              end
            end
            // bgeu
            3'b111: begin
              if (e_bypass_rs1 >= e_bypass_rs2) begin
              end
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeEnviron: begin
          if (decode_state.insn[31:7] == 25'd0) begin
          end else begin
            illegal_insn = 1'b1;
          end
        end
        OpcodeLoad: begin
          case (decode_state.insn[14:12])
            // lb
            3'b000: begin
            end
            // lh
            3'b001: begin
            end
            // lw
            3'b010: begin
            end
            // lbu
            3'b100: begin
            end
            // lhu
            3'b101: begin
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeStore: begin
          case (decode_state.insn[14:12])
            // sb
            3'b000: begin
            end
            // sh
            3'b001: begin
            end
            // sw
            3'b010: begin
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeMiscMem: begin
          case (decode_state.insn[14:12])
            3'b000: begin
            end
            3'b001: begin
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeAuipc: begin
        end
        OpcodeJal: begin
        end
        OpcodeJalr: begin
          if (decode_state.insn[14:12] == 0) begin
          end else begin
            illegal_insn = 1'b1;
          end
        end
        default: begin
          illegal_insn = 1'b1;
        end
      endcase
    end
  end

  /*****************/
  /* EXECUTE STAGE */
  /*****************/
  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET, rs1_data: 0, rs2_data: 0};
    end else if (loadStall) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_LOAD2USE,
          rs1_data: 0,
          rs2_data: 0
      };
    end else if (fenceStall) begin
      execute_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_FENCEI, rs1_data: 0, rs2_data: 0};
    end else if (divStall) begin
      execute_state <= '{
          pc: 0,
          insn: 0,
          cycle_status: CYCLE_DIV2USE,
          rs1_data: 0,
          rs2_data: 0
      };
    end else begin
      execute_state <= '{
          pc: branch_bool > 0 ? 0 : decode_state.pc,
          insn: branch_bool > 0 ? 0 : decode_state.insn,
          cycle_status:
          illegal_insn
          ?
          CYCLE_INVALID
          :
          branch_bool
          > 0 ?
          CYCLE_TAKEN_BRANCH
          :
          decode_state.cycle_status,
          rs1_data: wd_bypass_rs1,
          rs2_data: wd_bypass_rs2
      };
    end
  end
  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("E")
  ) disasm_1execute (
      .insn  (execute_state.insn),
      .disasm(e_disasm)
  );

  // components of the instruction
  wire [6:0] e_insn_funct7;
  wire [4:0] e_insn_rs2;
  wire [4:0] e_insn_rs1;
  wire [2:0] e_insn_funct3;
  wire [4:0] e_insn_rd;
  wire [`OPCODE_SIZE] e_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {e_insn_funct7, e_insn_rs2, e_insn_rs1, e_insn_funct3, e_insn_rd, e_insn_opcode} = execute_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] e_imm_i;
  assign e_imm_i = execute_state.insn[31:20];
  wire [ 4:0] e_imm_shamt = execute_state.insn[24:20];

  // S - stores
  wire [11:0] e_imm_s;
  assign e_imm_s[11:5] = e_insn_funct7, e_imm_s[4:0] = e_insn_rd;

  // B - conditionals
  wire [12:0] e_imm_b;
  assign {e_imm_b[12], e_imm_b[10:5]} = e_insn_funct7,
      {e_imm_b[4:1], e_imm_b[11]} = e_insn_rd,
      e_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] e_imm_j;
  assign {e_imm_j[20], e_imm_j[10:1], e_imm_j[11], e_imm_j[19:12], e_imm_j[0]} = {
    execute_state.insn[31:12], 1'b0
  };

  wire [`REG_SIZE] e_imm_i_sext = {{20{e_imm_i[11]}}, e_imm_i[11:0]};
  wire [`REG_SIZE] e_imm_s_sext = {{20{e_imm_s[11]}}, e_imm_s[11:0]};
  wire [`REG_SIZE] e_imm_b_sext = {{19{e_imm_b[12]}}, e_imm_b[12:0]};
  wire [`REG_SIZE] e_imm_j_sext = {{11{e_imm_j[20]}}, e_imm_j[20:0]};

  // result of ALU
  logic [31:0] e_result;

  logic [31:0] e_bypass_rs1;
  logic [31:0] e_bypass_rs2;

  logic [31:0] e_unsigned_bypass_rs1;
  logic [31:0] e_unsigned_bypass_rs2;

  // multiply
  logic [63:0] product;

  // branch
  logic [31:0] branch_taken;
  logic branch_bool;

  // MX bypass logic
  always_comb begin
    e_bypass_rs1 = 0;
    e_bypass_rs2 = 0;
    e_unsigned_bypass_rs1 = 0;
    e_unsigned_bypass_rs2 = 0;
    if (execute_state.cycle_status == CYCLE_NO_STALL) begin
      if ((e_insn_rs1 == m_insn_rd) && m_insn_rd != 0 && memory_state.cycle_status == CYCLE_NO_STALL && memory_state.insn[6:0] != OpcodeBranch && memory_state.insn[6:0] != OpcodeStore && memory_state.insn[6:0] != OpcodeLoad && memory_state.insn[6:0] != OpcodeEnviron && memory_state.insn[6:0] != OpcodeMiscMem
      && execute_state.insn[6:0] != OpcodeLui && execute_state.insn[6:0] != OpcodeAuipc && execute_state.insn[6:0] != OpcodeJal && execute_state.insn[6:0] != OpcodeEnviron && execute_state.insn[6:0] != OpcodeMiscMem) begin
        e_bypass_rs1 = memory_state.alu_result;
        e_unsigned_bypass_rs1 = e_bypass_rs1[31] ? ~e_bypass_rs1 + 1 : e_bypass_rs1;
      end else begin
        // WX bypass logic
        if ((e_insn_rs1 == w_insn_rd) && w_insn_rd != 0 && writeback_state.cycle_status == CYCLE_NO_STALL && writeback_state.insn[6:0] != OpcodeBranch && writeback_state.insn[6:0] != OpcodeStore && writeback_state.insn[6:0] != OpcodeEnviron && writeback_state.insn[6:0] != OpcodeMiscMem
        && execute_state.insn[6:0] != OpcodeLui && execute_state.insn[6:0] != OpcodeAuipc && execute_state.insn[6:0] != OpcodeJal && execute_state.insn[6:0] != OpcodeEnviron && execute_state.insn[6:0] != OpcodeMiscMem) begin
          e_bypass_rs1 = writeback_state.alu_result;
          e_unsigned_bypass_rs1 = e_bypass_rs1[31] ? ~e_bypass_rs1 + 1 : e_bypass_rs1;
        end else begin
          e_bypass_rs1 = execute_state.rs1_data;
          e_unsigned_bypass_rs1 = e_bypass_rs1[31] ? ~e_bypass_rs1 + 1 : e_bypass_rs1;
        end
      end

      if ((e_insn_rs2 == m_insn_rd) && m_insn_rd != 0 && memory_state.cycle_status == CYCLE_NO_STALL && memory_state.insn[6:0] != OpcodeBranch && memory_state.insn[6:0] != OpcodeLoad && memory_state.insn[6:0] != OpcodeStore && memory_state.insn[6:0] != OpcodeEnviron && memory_state.insn[6:0] != OpcodeMiscMem
      && (execute_state.insn[6:0] == OpcodeRegReg || execute_state.insn[6:0] == OpcodeBranch || execute_state.insn[6:0] == OpcodeStore)) begin
        e_bypass_rs2 = memory_state.alu_result;
        e_unsigned_bypass_rs2 = e_bypass_rs2[31] ? ~e_bypass_rs2 + 1 : e_bypass_rs2;
      end else begin
        // WX bypass logic
        if ((e_insn_rs2 == w_insn_rd) && w_insn_rd != 0 && writeback_state.cycle_status == CYCLE_NO_STALL && writeback_state.insn[6:0] != OpcodeBranch && writeback_state.insn[6:0] != OpcodeStore && writeback_state.insn[6:0] != OpcodeEnviron && writeback_state.insn[6:0] != OpcodeMiscMem
        && (execute_state.insn[6:0] == OpcodeRegReg || execute_state.insn[6:0] == OpcodeBranch || execute_state.insn[6:0] == OpcodeStore)) begin
          e_bypass_rs2 = writeback_state.alu_result;
          e_unsigned_bypass_rs2 = e_bypass_rs2[31] ? ~e_bypass_rs2 + 1 : e_bypass_rs2;
        end else begin
          e_bypass_rs2 = execute_state.rs2_data;
          e_unsigned_bypass_rs2 = e_bypass_rs2[31] ? ~e_bypass_rs2 + 1 : e_bypass_rs2;
        end
      end
    end
  end

  logic [31:0] remainder1, remainder2, remainder3, remainder4;
  logic [31:0] quotient1, quotient2, quotient3, quotient4;

  // divider / remainder
  divider_unsigned_pipelined div (
      .clk(clk),
      .rst(rst),
      .i_dividend(e_unsigned_bypass_rs1),
      .i_divisor(e_unsigned_bypass_rs2),
      .o_quotient(quotient1),
      .o_remainder(remainder1)
  );
  divider_unsigned_pipelined divu (
      .clk(clk),
      .rst(rst),
      .i_dividend(e_bypass_rs1),
      .i_divisor(e_bypass_rs2),
      .o_quotient(quotient2),
      .o_remainder(remainder2)
  );
  divider_unsigned_pipelined rem (
      .clk(clk),
      .rst(rst),
      .i_dividend(e_unsigned_bypass_rs1),
      .i_divisor(e_unsigned_bypass_rs2),
      .o_quotient(quotient3),
      .o_remainder(remainder3)
  );
  divider_unsigned_pipelined remu (
      .clk(clk),
      .rst(rst),
      .i_dividend(e_bypass_rs1),
      .i_divisor(e_bypass_rs2),
      .o_quotient(quotient4),
      .o_remainder(remainder4)
  );

  always_comb begin
    branch_bool = 0;
    branch_taken = 0;
    e_result = 0;
    product = 0;
    if (execute_state.cycle_status == CYCLE_NO_STALL) begin
      case (e_insn_opcode)
        OpcodeLui: begin
          e_result = {execute_state.insn[31:12], 12'b0};
        end
        OpcodeRegImm: begin
          case (execute_state.insn[14:12])
            // addi
            3'b000: begin
              e_result = e_bypass_rs1 + e_imm_i_sext;
            end
            // slti
            3'b010: begin
              e_result = ($signed(e_bypass_rs1) < $signed(e_imm_i_sext)) ? 32'd1 : 32'd0;
            end
            // sltiu
            3'b011: begin
              e_result = (e_bypass_rs1 < e_imm_i_sext) ? 32'd1 : 32'd0;
            end
            // xori
            3'b100: begin
              e_result = e_bypass_rs1 ^ e_imm_i_sext;
            end
            // ori
            3'b110: begin
              e_result = e_bypass_rs1 | e_imm_i_sext;
            end
            // andi
            3'b111: begin
              e_result = e_bypass_rs1 & e_imm_i_sext;
            end
            // slli
            3'b001: begin
              e_result = e_bypass_rs1 << e_imm_shamt;
            end
            // srli & srai
            3'b101: begin
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = e_bypass_rs1 >> e_imm_shamt;
              end else if (execute_state.insn[31:25] == 7'b0100000) begin
                e_result = $signed(e_bypass_rs1) >>> e_imm_shamt;
              end
            end
            default: begin
            end
          endcase
        end
        OpcodeRegReg: begin
          case (execute_state.insn[14:12])
            // add & sub & mul
            3'b000: begin
              // add
              if (execute_state.insn[31:25] == 7'b0) begin
                e_result = e_bypass_rs1 + e_bypass_rs2;
                // sub
              end else if (execute_state.insn[31:25] == 7'b0100000) begin
                e_result = e_bypass_rs1 - e_bypass_rs2;
                // mul
              end else if (execute_state.insn[31:25] == 7'd1) begin
                product  = {{32{1'b0}}, e_bypass_rs1} * {{32{1'b0}}, e_bypass_rs2};
                e_result = product[31:0];
              end
            end
            // sll & mulh
            3'b001: begin
              // sll
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = e_bypass_rs1 << e_bypass_rs2[4:0];
              end  // mulh
              else if (execute_state.insn[31:25] == 7'd1) begin
                product = $signed({{32{e_bypass_rs1[31]}}, e_bypass_rs1}) *
                    $signed({{32{e_bypass_rs2[31]}}, e_bypass_rs2});
                e_result = product[63:32];
              end
            end
            // slt & mulhsu
            3'b010: begin
              // slt
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = ($signed(e_bypass_rs1) < $signed(e_bypass_rs2)) ? 32'd1 : 32'd0;
              end  // mulhsu
              else if (execute_state.insn[31:25] == 7'd1) begin
                product = $signed({{32{e_bypass_rs1[31]}}, e_bypass_rs1}) *
                    ({{32{1'b0}}, e_bypass_rs2});
                e_result = product[63:32];
              end
            end
            // sltu & mulhu
            3'b011: begin
              // sltu
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = (e_bypass_rs1 < e_bypass_rs2) ? 32'd1 : 32'd0;
              end  // mulhu
              else if (execute_state.insn[31:25] == 7'd1) begin
                product  = ({{32{1'b0}}, e_bypass_rs1}) * ({{32{1'b0}}, e_bypass_rs2});
                e_result = product[63:32];
              end
            end
            // xor & div
            3'b100: begin
              // xor
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = e_bypass_rs1 ^ e_bypass_rs2;
                // div
              end else if (execute_state.insn[31:25] == 7'd1) begin
                e_result = e_bypass_rs1;
              end
            end
            // srl & sra
            3'b101: begin
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = e_bypass_rs1 >> e_bypass_rs2[4:0];
              end else if (execute_state.insn[31:25] == 7'b0100000) begin
                e_result = $signed(e_bypass_rs1) >>> e_bypass_rs2[4:0];
              end else if (execute_state.insn[31:25] == 7'd1) begin
                e_result = e_bypass_rs1;
              end
            end
            // or & rem
            3'b110: begin
              // or
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = e_bypass_rs1 | e_bypass_rs2;
              end  // rem
              else if (execute_state.insn[31:25] == 7'd1) begin
                e_result = e_bypass_rs1;
              end
            end
            // and & remu
            3'b111: begin
              // and
              if (execute_state.insn[31:25] == 7'd0) begin
                e_result = e_bypass_rs1 & e_bypass_rs2;
              end  // remu
              else if (execute_state.insn[31:25] == 7'd1) begin
                e_result = e_bypass_rs1;
              end
            end
            default: begin
            end
          endcase
        end
        OpcodeBranch: begin
          case (execute_state.insn[14:12])
            // beq
            3'b000: begin
              if (e_bypass_rs1 == e_bypass_rs2) begin
                branch_bool  = 1;
                branch_taken = execute_state.pc + e_imm_b_sext;
              end
            end
            // bne
            3'b001: begin
              if (e_bypass_rs1 != e_bypass_rs2) begin
                branch_bool  = 1;
                branch_taken = execute_state.pc + e_imm_b_sext;
              end
            end
            // blt
            3'b100: begin
              if ($signed(e_bypass_rs1) < $signed(e_bypass_rs2)) begin
                branch_bool  = 1;
                branch_taken = execute_state.pc + e_imm_b_sext;
              end
            end
            // bge
            3'b101: begin
              if ($signed(e_bypass_rs1) >= $signed(e_bypass_rs2)) begin
                branch_bool  = 1;
                branch_taken = execute_state.pc + e_imm_b_sext;
              end
            end
            // bltu
            3'b110: begin
              if (e_bypass_rs1 < e_bypass_rs2) begin
                branch_bool  = 1;
                branch_taken = execute_state.pc + e_imm_b_sext;
              end
            end
            // bgeu
            3'b111: begin
              if (e_bypass_rs1 >= e_bypass_rs2) begin
                branch_bool  = 1;
                branch_taken = execute_state.pc + e_imm_b_sext;
              end
            end
            default: begin
            end
          endcase
        end
        OpcodeLoad: begin
          e_result = e_bypass_rs1 + e_imm_i_sext;
        end
        OpcodeStore: begin
          e_result = e_bypass_rs1 + e_imm_s_sext;
        end
        OpcodeMiscMem: begin
        end
        OpcodeAuipc: begin
          e_result = execute_state.pc + {execute_state.insn[31:12], 12'b0};
        end
        OpcodeJal: begin
          e_result = execute_state.pc + 4;
          branch_bool = 1;
          branch_taken = execute_state.pc + e_imm_j_sext;
        end
        OpcodeJalr: begin
          e_result = execute_state.pc + 4;
          branch_bool = 1;
          branch_taken = (e_bypass_rs1 + e_imm_i_sext) & ~(32'd1);
        end
        default: begin
        end
      endcase
    end
  end

  /****************/
  /* MEMORY STAGE */
  /****************/
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET, alu_result: 0, rs2_data: 0};
    end else begin
      begin
        memory_state <= '{
            pc: execute_state.pc,
            insn: execute_state.insn,
            cycle_status: execute_state.cycle_status,
            alu_result: e_result,
            // relevant for stores -> WM bypass
            rs2_data:
            e_bypass_rs2
        };
      end
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_1memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );

  // components of the instruction
  wire [6:0] m_insn_funct7;
  wire [4:0] m_insn_rs2;
  wire [4:0] m_insn_rs1;
  wire [2:0] m_insn_funct3;
  wire [4:0] m_insn_rd;
  wire [`OPCODE_SIZE] m_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {m_insn_funct7, m_insn_rs2, m_insn_rs1, m_insn_funct3, m_insn_rd, m_insn_opcode} = memory_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] m_imm_i;
  assign m_imm_i = memory_state.insn[31:20];
  wire [ 4:0] m_imm_shamt = memory_state.insn[24:20];

  // S - stores
  wire [11:0] m_imm_s;
  assign m_imm_s[11:5] = m_insn_funct7, m_imm_s[4:0] = m_insn_rd;

  // B - conditionals
  wire [12:0] m_imm_b;
  assign {m_imm_b[12], m_imm_b[10:5]} = m_insn_funct7,
      {m_imm_b[4:1], m_imm_b[11]} = m_insn_rd,
      m_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] m_imm_j;
  assign {m_imm_j[20], m_imm_j[10:1], m_imm_j[11], m_imm_j[19:12], m_imm_j[0]} = {
    memory_state.insn[31:12], 1'b0
  };

  wire [`REG_SIZE] m_imm_i_sext = {{20{m_imm_i[11]}}, m_imm_i[11:0]};
  wire [`REG_SIZE] m_imm_s_sext = {{20{m_imm_s[11]}}, m_imm_s[11:0]};
  wire [`REG_SIZE] m_imm_b_sext = {{19{m_imm_b[12]}}, m_imm_b[12:0]};
  wire [`REG_SIZE] m_imm_j_sext = {{11{m_imm_j[20]}}, m_imm_j[20:0]};

  // what we send to the writeback stage 
  logic [31:0] memoryResult;

  // memory we sent to dmem
  logic [31:0] tempAddr;
  assign addr_to_dmem = tempAddr;

  // write enable for dmem
  logic [3:0] tempWe;
  assign store_we_to_dmem = tempWe;

  // value we store in dmem
  logic [31:0] tempStore;
  assign store_data_to_dmem = tempStore;

  // bypass value
  logic [31:0] rs2_bypass;
  always_comb begin
    rs2_bypass = memory_state.rs2_data;
    if (writeback_state.cycle_status == CYCLE_NO_STALL && writeback_state.insn[6:0] == OpcodeLoad && memory_state.insn[6:0] == OpcodeStore &&
    w_insn_rd == m_insn_rs2) begin
      rs2_bypass = writeback_state.alu_result;
    end
  end

  always_comb begin
    memoryResult = memory_state.alu_result;
    tempAddr = 32'b0;
    tempWe = 4'b0000;
    if (memory_state.cycle_status == CYCLE_NO_STALL) begin
      case (memory_state.insn[6:0])
        OpcodeLui: begin
        end
        OpcodeRegImm: begin
        end
        OpcodeRegReg: begin
          case (memory_state.insn[14:12])
            3'b100:
            if (memory_state.insn[31:25] == 7'd1) begin
              if (memory_state.rs2_data == 0) begin
                memoryResult = ~(32'd0);
              end else begin
                if (memory_state.alu_result[31] != memory_state.rs2_data[31]) begin
                  memoryResult = ~(quotient1) + 1;
                end else begin
                  if (memory_state.alu_result == 32'b10000000000000000000000000000000) begin
                    if (memory_state.rs2_data == ~(32'd0)) begin
                      memoryResult = memory_state.alu_result;
                    end else begin
                      memoryResult = quotient1;
                    end
                  end else begin
                    memoryResult = quotient1;
                  end
                end
              end
            end
            3'b101:
            if (memory_state.insn[31:25] == 7'd1) begin
              if (memory_state.rs2_data == 0) begin
                memoryResult = ~(32'd0);
              end else begin
                memoryResult = quotient2;
              end
            end
            3'b110:
            if (memory_state.insn[31:25] == 7'd1) begin
              if (memory_state.rs2_data == 0) begin
                memoryResult = memory_state.alu_result;
              end else begin
                if (memory_state.alu_result[31] == 0 & memory_state.rs2_data[31] == 0) begin
                  memoryResult = remainder3;
                end else if (memory_state.alu_result[31] == 1 & memory_state.rs2_data[31] == 0) begin
                  memoryResult = ~(remainder3) + 1;
                end else if (memory_state.alu_result[31] == 0 & memory_state.rs2_data[31] == 1) begin
                  memoryResult = remainder3;
                end else begin
                  if (memory_state.alu_result == 32'b10000000000000000000000000000000) begin
                    if (memory_state.rs2_data == ~(32'd0)) begin
                      memoryResult = 0;
                    end else begin
                      memoryResult = ~(remainder3) + 1;
                    end
                  end else begin
                    memoryResult = ~(remainder3) + 1;
                  end
                end
              end
            end
            3'b111:
            if (memory_state.insn[31:25] == 7'd1) begin
              if (memory_state.rs2_data == 0) begin
                memoryResult = memory_state.alu_result;
              end else begin
                memoryResult = remainder4;
              end
            end
            default: begin
            end
          endcase
        end
        OpcodeBranch: begin
        end
        OpcodeLoad: begin
          case (memory_state.insn[14:12])
            // lb
            3'b000: begin
              tempAddr = (memory_state.alu_result & ~32'd3);
              if (memory_state.alu_result[1:0] == 2'b00) begin
                memoryResult = ({{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]});
              end else if (memory_state.alu_result[1:0] == 2'b01) begin
                memoryResult = ({{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]});
              end else if (memory_state.alu_result[1:0] == 2'b10) begin
                memoryResult = ({{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]});
              end else begin
                memoryResult = ({{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]});
              end
            end
            // lh
            3'b001: begin
              if (memory_state.alu_result[0] == 1'b0) begin
                tempAddr = (memory_state.alu_result & ~32'd3);
                if (memory_state.alu_result[1] == 1'b0) begin
                  memoryResult = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
                end else begin
                  memoryResult = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
                end
              end
            end
            // lw
            3'b010: begin
              if (memory_state.alu_result[1:0] == 2'b00) begin
                tempAddr = memory_state.alu_result;
                memoryResult = load_data_from_dmem;
              end
            end
            // lbu
            3'b100: begin
              tempAddr = (memory_state.alu_result & ~32'd3);
              if (memory_state.alu_result[1:0] == 2'b00) begin
                memoryResult = ({{24{1'b0}}, load_data_from_dmem[7:0]});
              end else if (memory_state.alu_result[1:0] == 2'b01) begin
                memoryResult = ({{24{1'b0}}, load_data_from_dmem[15:8]});
              end else if (memory_state.alu_result[1:0] == 2'b10) begin
                memoryResult = ({{24{1'b0}}, load_data_from_dmem[23:16]});
              end else begin
                memoryResult = ({{24{1'b0}}, load_data_from_dmem[31:24]});
              end
            end
            // lhu
            3'b101: begin
              if (memory_state.alu_result[0] == 1'b0) begin
                tempAddr = (memory_state.alu_result & ~32'd3);
                if (memory_state.alu_result[1] == 1'b0) begin
                  memoryResult = {{16{1'b0}}, load_data_from_dmem[15:0]};
                end else begin
                  memoryResult = {{16{1'b0}}, load_data_from_dmem[31:16]};
                end
              end
            end
            default: begin
            end
          endcase
        end
        OpcodeStore: begin
          case (memory_state.insn[14:12])
            // sb
            3'b000: begin
              tempAddr = (memory_state.alu_result & ~32'd3);
              if (memory_state.alu_result[1:0] == 2'b00) begin
                tempWe = 4'b0001;
                tempStore = {load_data_from_dmem[31:8], rs2_bypass[7:0]};
              end else if (memory_state.alu_result[1:0] == 2'b01) begin
                tempWe = 4'b0010;
                tempStore = {load_data_from_dmem[31:16], rs2_bypass[7:0], load_data_from_dmem[7:0]};
              end else if (memory_state.alu_result[1:0] == 2'b10) begin
                tempWe = 4'b0100;
                tempStore = {
                  load_data_from_dmem[31:24], rs2_bypass[7:0], load_data_from_dmem[15:0]
                };
              end else begin
                tempWe = 4'b1000;
                tempStore = {rs2_bypass[7:0], load_data_from_dmem[23:0]};
              end
            end
            3'b001: begin
              if (memory_state.alu_result[0] == 1'b0) begin
                tempAddr = (memory_state.alu_result & ~32'd3);
                if (memory_state.alu_result[1] == 1'b0) begin
                  tempWe = 4'b0011;
                  tempStore = {16'b0, rs2_bypass[15:0]};
                end else begin
                  tempWe = 4'b1100;
                  tempStore = {rs2_bypass[15:0], 16'b0};
                end
              end
            end
            3'b010: begin
              if (memory_state.alu_result[1:0] == 2'b00) begin
                tempAddr = memory_state.alu_result;
                tempWe = 4'b1111;
                tempStore = rs2_bypass;
              end
            end
            default: begin
            end
          endcase
        end
        OpcodeMiscMem: begin
        end
        OpcodeAuipc: begin
        end
        OpcodeJal: begin
        end
        OpcodeJalr: begin
        end
        default: begin
        end
      endcase
    end
  end


  /*******************/
  /* WRITEBACK STAGE */
  /*******************/
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{pc: 0, insn: 0, cycle_status: CYCLE_RESET, alu_result: 0};
    end else begin
      begin
        writeback_state <= '{
            pc:
            memory_state.cycle_status
            == (
            CYCLE_TAKEN_BRANCH | CYCLE_DIV2USE | CYCLE_FENCEI | CYCLE_INVALID | CYCLE_LOAD2USE
            ) ?
            0
            :
            memory_state.pc,
            insn:
            memory_state.cycle_status
            == (
            CYCLE_TAKEN_BRANCH | CYCLE_DIV2USE | CYCLE_FENCEI | CYCLE_INVALID | CYCLE_LOAD2USE
            ) ?
            0
            :
            memory_state.insn,
            cycle_status: memory_state.cycle_status,
            alu_result: memoryResult
        };
      end
    end
  end
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_1writeback (
      .insn  (writeback_state.insn),
      .disasm(w_disasm)
  );

  // components of the instruction
  wire [6:0] w_insn_funct7;
  wire [4:0] w_insn_rs2;
  wire [4:0] w_insn_rs1;
  wire [2:0] w_insn_funct3;
  wire [4:0] w_insn_rd;
  wire [`OPCODE_SIZE] w_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {w_insn_funct7, w_insn_rs2, w_insn_rs1, w_insn_funct3, w_insn_rd, w_insn_opcode} = writeback_state.insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] w_imm_i;
  assign w_imm_i = writeback_state.insn[31:20];
  wire [ 4:0] w_imm_shamt = writeback_state.insn[24:20];

  // S - stores
  wire [11:0] w_imm_s;
  assign w_imm_s[11:5] = w_insn_funct7, w_imm_s[4:0] = w_insn_rd;

  // B - conditionals
  wire [12:0] w_imm_b;
  assign {w_imm_b[12], w_imm_b[10:5]} = w_insn_funct7,
      {w_imm_b[4:1], w_imm_b[11]} = w_insn_rd,
      w_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] w_imm_j;
  assign {w_imm_j[20], w_imm_j[10:1], w_imm_j[11], w_imm_j[19:12], w_imm_j[0]} = {
    writeback_state.insn[31:12], 1'b0
  };

  wire [`REG_SIZE] w_imm_i_sext = {{20{w_imm_i[11]}}, w_imm_i[11:0]};
  wire [`REG_SIZE] w_imm_s_sext = {{20{w_imm_s[11]}}, w_imm_s[11:0]};
  wire [`REG_SIZE] w_imm_b_sext = {{19{w_imm_b[12]}}, w_imm_b[12:0]};
  wire [`REG_SIZE] w_imm_j_sext = {{11{w_imm_j[20]}}, w_imm_j[20:0]};

  always_comb begin
    regfile_we = 1'b0;
    halt = 1'b0;
    regfile_rd_data = 0;
    if (writeback_state.cycle_status == CYCLE_NO_STALL) begin
      case (w_insn_opcode)
        OpcodeLui: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeRegImm: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeRegReg: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeEnviron: begin
          if (writeback_state.insn[31:7] == 25'd0) begin
            halt = 1'b1;
          end
        end
        OpcodeLoad: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeStore: begin
        end
        OpcodeMiscMem: begin
        end
        OpcodeAuipc: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeJal: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeJalr: begin
          regfile_rd_data = writeback_state.alu_result;
          regfile_we = 1;
        end
        OpcodeBranch: begin
        end
        default: begin
        end
      endcase
    end
  end

  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = writeback_state.insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW5 memory interface
  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;
  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  // HW6 memory interface
  axi_clkrst_if axi_cr (
      .ACLK(clk),
      .ARESETn(~rst)
  );
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(
      .NUM_WORDS(8192)
  ) mem (
      .axi (axi_cr),
      .insn(axi_insn.subord),
      .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk(clk),
      .rst(rst),
      .imem(axi_insn.manager),
      // .dmem(axi_data.manager),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
