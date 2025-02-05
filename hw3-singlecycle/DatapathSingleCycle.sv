`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2a/divider_unsigned.sv"
`include "../hw2b/cla.sv"

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
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  assign regs[0] = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  genvar i;
    generate for (i = 0; i < NumRegs; i++) begin: g_loop
      always_ff @(posedge clk) begin
        if (rst) begin
          regs[i] <= 32'd0;
        end else begin
          if (we && rd == i && rd != 0) begin
            regs[i] <= rd_data;
          end
        end
      end
    end endgenerate


endmodule

module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output wire [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output wire [`REG_SIZE] store_data_to_dmem,
    output wire [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  // instatiate register file data
  logic [`REG_SIZE] regfile_rs1_data;
  logic [`REG_SIZE] regfile_rs2_data;
  logic [`REG_SIZE] regfile_rd_data;

  logic illegal_insn;
  logic regfile_we;

  // instatiate register file
  RegFile rf (
      .clk(clk),
      .rst(rst),
      .we(regfile_we),
      .rd(insn_rd),
      .rs1(insn_rs1),
      .rs2(insn_rs2),
      .rd_data(regfile_rd_data),
      .rs1_data(regfile_rs1_data),
      .rs2_data(regfile_rs2_data)
  );

  // temp wire for sum
  logic[31:0] sum1, sum2, sum3;
  logic[63:0] product;
  logic[31:0] remainder1, remainder2, remainder3, remainder4;
  logic[31:0] quotient1, quotient2, quotient3, quotient4;
  logic[31:0] unsignedrs1, unsignedrs2;
  logic[31:0] tempload, tempstore;

  assign tempload = regfile_rs1_data + imm_i_sext;
  assign tempstore = regfile_rs1_data + imm_s_sext;
  


  cla cla_addi(.a(regfile_rs1_data), .b(imm_i_sext), .cin(1'b0), .sum(sum1));
  cla cla_add(.a(regfile_rs1_data), .b(regfile_rs2_data), .cin(1'b0), .sum(sum2));
  cla cla_sub(.a(regfile_rs1_data), .b(~(regfile_rs2_data)), .cin(1'b1), .sum(sum3));

  assign unsignedrs1 = regfile_rs1_data[31] ? ~regfile_rs1_data + 1: regfile_rs1_data;
  assign unsignedrs2 = regfile_rs2_data[31] ? ~regfile_rs2_data + 1: regfile_rs2_data;

  
  divider_unsigned div(.i_dividend(unsignedrs1), .i_divisor(unsignedrs2), .o_quotient(quotient1), .o_remainder(remainder1));
  divider_unsigned divu(.i_dividend(regfile_rs1_data), .i_divisor(regfile_rs2_data), .o_quotient(quotient2), .o_remainder(remainder2));
  divider_unsigned rem(.i_dividend(unsignedrs1), .i_divisor(unsignedrs2), .o_quotient(quotient3), .o_remainder(remainder3));
  divider_unsigned remu(.i_dividend(regfile_rs1_data), .i_divisor(regfile_rs2_data), .o_quotient(quotient4), .o_remainder(remainder4));

  logic[31:0] temp_addr_to_dmem, temp_store_data_to_dmem;
  logic[3:0] temp_store_we_to_dmem;

  assign addr_to_dmem[31:0] = temp_addr_to_dmem[31:0];
  assign store_data_to_dmem = temp_store_data_to_dmem[31:0];
  assign store_we_to_dmem = temp_store_we_to_dmem[3:0];

  always_comb begin
    illegal_insn = 1'b0;
    regfile_we = 1'b0;
    regfile_rd_data = 32'd0;
    halt = 0;
    pcNext = pcCurrent + 4;
    temp_addr_to_dmem = 32'd0;
    temp_store_data_to_dmem = 32'd0;
    temp_store_we_to_dmem = 4'b0000;
    product = 64'd0;
    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        regfile_we = 1'b1;
        regfile_rd_data = {insn_from_imem[31:12], 12'b0};
      end
      OpAuipc: begin
        regfile_we = 1'b1;
        regfile_rd_data = pcCurrent + {insn_from_imem[31:12], 12'b0};
      end
      OpRegImm: begin
        case (insn_from_imem[14:12])
          // addi
          3'b000: begin
            regfile_we = 1'b1;
            // use CLA
            regfile_rd_data = sum1;
          end
          // slti
          3'b010: begin
            regfile_we = 1'b1;
            regfile_rd_data = ($signed(regfile_rs1_data) < $signed(imm_i_sext)) ? 32'd1 : 32'd0;
          end
          // sltiu
          3'b011: begin
            regfile_we = 1'b1;
            regfile_rd_data = (regfile_rs1_data < imm_i_sext) ? 32'd1 : 32'd0;
          end
          // xori
          3'b100: begin
            regfile_we = 1'b1;
            regfile_rd_data = regfile_rs1_data ^ imm_i_sext;
          end
          // ori
          3'b110: begin
            regfile_we = 1'b1;
            regfile_rd_data = regfile_rs1_data | imm_i_sext;
          end
          // andi
          3'b111: begin
            regfile_we = 1'b1;
            regfile_rd_data = regfile_rs1_data & imm_i_sext;
          end
          // slli
          3'b001: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data << imm_shamt;
            end
          end
          // srli & srai
          3'b101: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data >> imm_shamt;
            end else if (insn_from_imem[31:25] == 7'b0100000) begin
              regfile_we = 1'b1;
              regfile_rd_data = $signed(regfile_rs1_data) >>> imm_shamt;
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end
      OpRegReg: begin
        case (insn_from_imem[14:12])
          // add & sub
          3'b000: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              // use CLA
              regfile_rd_data = sum2;
            end else if (insn_from_imem[31:25] == 7'b0100000) begin
              regfile_we = 1'b1;
              // use CLA
              regfile_rd_data = sum3;
            // mul
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;
              product = {{32{1'b0}}, regfile_rs1_data} * {{32{1'b0}}, regfile_rs2_data};
              regfile_rd_data = product[31:0];
            end
          end
          // sll
          3'b001: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data << (regfile_rs2_data[4:0]);
            // mulh
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;
              product = $signed({{32{regfile_rs1_data[31]}}, regfile_rs1_data}) * $signed({{32{regfile_rs2_data[31]}}, regfile_rs2_data});
              regfile_rd_data = product[63:32];
            end
          end
          // slt
          3'b010: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = ($signed(regfile_rs1_data) < $signed(regfile_rs2_data)) ? 32'd1 : 32'd0;
            // mulhsu
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;
              product = $signed({{32{regfile_rs1_data[31]}}, regfile_rs1_data}) * ({{32{1'b0}}, regfile_rs2_data});
              regfile_rd_data = product[63:32];
            end
          end
          // sltu
          3'b011: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = (regfile_rs1_data < regfile_rs2_data) ? 32'd1 : 32'd0;
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;
              product = {{32{1'b0}}, regfile_rs1_data} * {{32{1'b0}}, regfile_rs2_data};
              regfile_rd_data = product[63:32];
            end
          end
          // xor
          3'b100: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data ^ regfile_rs2_data;
            // div
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;

              if (regfile_rs2_data == 0) begin
                regfile_rd_data = ~(32'd0);
              end else begin
                if (regfile_rs1_data[31] != regfile_rs2_data[31]) begin
                  regfile_rd_data = ~(quotient1) + 1;
                end else begin
                  if (regfile_rs1_data == 32'b10000000000000000000000000000000) begin
                    if (regfile_rs2_data == ~(32'd0)) begin
                      regfile_rd_data = regfile_rs1_data;
                    end else begin
                      regfile_rd_data = quotient1;
                    end
                  end else begin
                    regfile_rd_data = quotient1;
                  end
                end
              end
              
            end
          end
          // srl & sra
          3'b101: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data >> (regfile_rs2_data[4:0]);
            end else if (insn_from_imem[31:25] == 7'b0100000) begin
              regfile_we = 1'b1;
              regfile_rd_data = $signed(regfile_rs1_data) >>> (regfile_rs2_data[4:0]);
            // divu
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;
              if (regfile_rs2_data == 0) begin
                regfile_rd_data = ~(32'd0);
              end else begin
                regfile_rd_data = quotient2;
              end
            end
          end
          // or
          3'b110: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data | regfile_rs2_data;
            // rem
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;

              if (regfile_rs2_data == 0) begin
                regfile_rd_data = regfile_rs1_data;
              end else begin
                if (regfile_rs1_data[31] == 0 & regfile_rs2_data[31] == 0) begin
                  regfile_rd_data = remainder3;
                end else if (regfile_rs1_data[31] == 1 & regfile_rs2_data[31] == 0) begin
                  regfile_rd_data = ~(remainder3) + 1;
                end else if (regfile_rs1_data[31] == 0 & regfile_rs2_data[31] == 1) begin
                  regfile_rd_data = remainder3;
                end else begin
                  if (regfile_rs1_data == 32'b10000000000000000000000000000000) begin
                    if (regfile_rs2_data == ~(32'd0)) begin
                      regfile_rd_data = 0;
                    end else begin
                      regfile_rd_data = ~(remainder3) + 1;
                    end
                  end else begin
                    regfile_rd_data = ~(remainder3) + 1;
                  end
                end
              end
            end
          end
          // and
          3'b111: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              regfile_we = 1'b1;
              regfile_rd_data = regfile_rs1_data & regfile_rs2_data;
            // remu
            end else if (insn_from_imem[31:25] == 7'd1) begin
              regfile_we = 1'b1;
              if (regfile_rs2_data == 0) begin
                regfile_rd_data = regfile_rs1_data;
              end else begin
                regfile_rd_data = remainder4;
              end
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end
      OpBranch: begin
        case (insn_from_imem[14:12])
          // beq
          3'b000: begin
            if (regfile_rs1_data == regfile_rs2_data) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          // bne
          3'b001: begin
            if (regfile_rs1_data != regfile_rs2_data) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          // blt
          3'b100: begin
            if ($signed(regfile_rs1_data) < $signed(regfile_rs2_data)) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          // bge
          3'b101: begin
            if ($signed(regfile_rs1_data) >= $signed(regfile_rs2_data)) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          // bltu
          3'b110: begin
            if (regfile_rs1_data < regfile_rs2_data) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          // bgeu
          3'b111: begin
            if (regfile_rs1_data >= regfile_rs2_data) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end
      OpEnviron: begin
        if (insn_from_imem[31:7] == 25'd0) begin
          halt = 1;
        end
      end
      OpJal: begin
        regfile_we = 1'b1;
        regfile_rd_data = pcCurrent + 4;
        pcNext = pcCurrent + imm_j_sext;
      end
      OpJalr: begin
        regfile_we = 1'b1;
        regfile_rd_data = pcCurrent + 4;
        pcNext = (regfile_rs1_data + imm_i_sext) & ~(32'd1);
      end
      OpLoad: begin
        case (insn_from_imem[14:12])
          // lb
          3'b000: begin
            regfile_we = 1'b1;
            temp_addr_to_dmem = ((regfile_rs1_data + imm_i_sext) & ~32'd3);
            if (tempload[1:0] == 2'b00) begin
              regfile_rd_data = ({{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]});
            end else if (tempload[1:0] == 2'b01) begin
              regfile_rd_data = ({{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]});
            end else if (tempload[1:0] == 2'b10) begin
              regfile_rd_data = ({{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]});
            end else begin
              regfile_rd_data = ({{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]});
            end
          end
          // lh
          3'b001: begin
            regfile_we = 1'b1;
            if (tempload[0] == 1'b0) begin
              temp_addr_to_dmem = ((regfile_rs1_data + imm_i_sext) & ~32'd3);
              if (tempload[1] == 1'b1) begin
                regfile_rd_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
              end else begin
                regfile_rd_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
              end
            end
          end
          // lw
          3'b010: begin
            regfile_we = 1'b1;
            if (tempload[1:0] == 2'b00) begin
              temp_addr_to_dmem = regfile_rs1_data + imm_i_sext;
              regfile_rd_data = load_data_from_dmem;
            end           
          end
          // lbu
          3'b100: begin
            regfile_we = 1'b1;
            temp_addr_to_dmem = ((regfile_rs1_data + imm_i_sext) & ~32'd3);
            if (tempload[1:0] == 2'b00) begin
              regfile_rd_data = ({{24{1'b0}}, load_data_from_dmem[7:0]});
            end else if (tempload[1:0] == 2'b01) begin
              regfile_rd_data = ({{24{1'b0}}, load_data_from_dmem[15:8]});
            end else if (tempload[1:0] == 2'b10) begin
              regfile_rd_data = ({{24{1'b0}}, load_data_from_dmem[23:16]});
            end else begin
              regfile_rd_data = ({{24{1'b0}}, load_data_from_dmem[31:24]});
            end
          end
          // lhu
          3'b101: begin
            regfile_we = 1'b1;
            if (tempload[0] == 1'b0) begin
              temp_addr_to_dmem = ((regfile_rs1_data + imm_i_sext) & ~32'd3);
              if (tempload[1] == 1'b1) begin
                regfile_rd_data = {{16{1'b0}}, load_data_from_dmem[31:16]};
              end else begin
                regfile_rd_data = {{16{1'b0}}, load_data_from_dmem[15:0]};
              end
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end
      OpStore: begin
        case (insn_from_imem[14:12])
          // sb
          3'b000: begin
            temp_addr_to_dmem = ((regfile_rs1_data + imm_s_sext) & ~32'd3);
            if (tempstore[1:0] == 2'b00) begin
              temp_store_data_to_dmem = {load_data_from_dmem[31:8], regfile_rs2_data[7:0]};
              temp_store_we_to_dmem = 4'b0001;
            end else if (tempstore[1:0] == 2'b01) begin
              temp_store_data_to_dmem = {load_data_from_dmem[31:16], regfile_rs2_data[7:0], load_data_from_dmem[7:0]};
              temp_store_we_to_dmem = 4'b0010;
            end else if (tempstore[1:0] == 2'b10) begin
              temp_store_data_to_dmem = {load_data_from_dmem[31:24], regfile_rs2_data[7:0], load_data_from_dmem[15:0]};
              temp_store_we_to_dmem = 4'b0100;
            end else begin
              temp_store_data_to_dmem = {regfile_rs2_data[7:0], load_data_from_dmem[23:0]};
              temp_store_we_to_dmem = 4'b1000;
            end
          end
          // sh
          3'b001: begin
            if (tempstore[0] == 1'b0) begin
              temp_addr_to_dmem = ((regfile_rs1_data + imm_s_sext) & ~32'd3);
              if (tempstore[1] == 1'b1) begin
                temp_store_data_to_dmem = {regfile_rs2_data[15:0], 16'b0};
                temp_store_we_to_dmem = 4'b1100;
              end else begin
                temp_store_data_to_dmem = {16'b0, regfile_rs2_data[15:0]};
                temp_store_we_to_dmem = 4'b0011;
              end
            end
          end
          // sw
          3'b010: begin
            if (tempstore[1:0] == 2'b00) begin
              temp_addr_to_dmem = regfile_rs1_data + imm_s_sext;
              temp_store_data_to_dmem = regfile_rs2_data;
              temp_store_we_to_dmem = 4'b1111;
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end
      OpMiscMem: begin
      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

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

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
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

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
