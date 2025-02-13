
typedef enum logic[6:0] {r_type_op=7'b0110011, i_type_alu_op=7'b0010011, lw_op=7'b0000011, sw_op=7'b0100011, beq_op=7'b1100011, jal_op=7'b1101111} opcodetype;
typedef enum logic [3:0]{
    FET = 4'b0000,
    DEC = 4'b0001,
    MemAD = 4'b0010,
    MemREAD = 4'b0011,
    ExecuteR = 4'b0100,
    ExecuteI = 4'b0101,
    JAL = 4'b0110,
    BEQ = 4'b0111,
    ALUWB = 4'b1000,
    MemWB = 4'b1001,
    MemWR = 4'b1010
  }state;

  state state_next, state_curr; 



module top(input  logic        clk, reset, 
           output logic [31:0] WriteData, DataAdr, 
           output logic        MemWrite);

  logic [31:0] ReadData;
  
  // instantiate processor and memories
  riscvmulti rvmulti(clk, reset, MemWrite, DataAdr, 
                     WriteData, ReadData);
  mem mem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule



module mem(input  logic        clk, we,
           input  logic [31:0] a, wd,
           output logic [31:0] rd);

  logic [31:0] RAM[63:0];
  
  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk) begin 
    if (we) begin
       RAM[a[31:2]] <= wd;
    end 
  end 

endmodule



module riscvmulti(input  logic        clk, reset,
                  output logic        MemWrite,
                  output logic [31:0] Adr, WriteData,
                  input  logic [31:0] ReadData);




  logic[31:0] Instr; 
  logic[2:0] funct3, ALUControl;
  logic[1:0] ImmSrc, ALUSrcA, ALUSrcB, ResultSrc;
  logic PCWrite, AdrSrc, IRWrite, RegWrite, Zero, funct7b5;
  opcodetype op;
 
  assign funct3 = Instr[14:12];
  assign funct7b5 = Instr[29];
  assign op = opcodetype'(Instr[6:0]);

  datapath dp(PCWrite, AdrSrc, IRWrite, RegWrite, clk, ImmSrc, ALUSrcA, ALUSrcB, ResultSrc, ALUControl, ReadData, WriteData, Adr, Instr, Zero);
  controller ControlUnit(clk, reset, op, funct3, funct7b5, Zero, ImmSrc, ALUSrcA, ALUSrcB, ResultSrc, AdrSrc, ALUControl, IRWrite, PCWrite, RegWrite, MemWrite);

endmodule



module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;
  logic [31:0] hash;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      hash <= 0;
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
 	   	  $display("hash = %h", hash);
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end

  // Make 32-bit hash of instruction, PC, ALU
  always @(negedge clk)
    if (~reset) begin
      hash = hash ^ dut.rvmulti.dp.Instr ^ dut.rvmulti.dp.PC;
      if (MemWrite) hash = hash ^ WriteData;
      hash = {hash[30:0], hash[9] ^ hash[29] ^ hash[30] ^ hash[31]};
    end

endmodule


module controller(input  logic       clk,
                  input  logic       reset,  
                  input  opcodetype  op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
                  input  logic       Zero,
                  output logic [1:0] ImmSrc,
                  output logic [1:0] ALUSrcA, ALUSrcB,
                  output logic [1:0] ResultSrc, 
                  output logic       AdrSrc,
                  output logic [2:0] ALUControl,
                  output logic       IRWrite, PCWrite, 
                  output logic       RegWrite, MemWrite);

  logic PCUpdate, Branch; 
  logic[1:0] ALUOp;

  aludecoder ALUDEC(ALUOp,funct3,op[5],funct7b5,ALUControl);

  always_ff @(posedge clk) begin

    if(reset) begin
      state_curr <= FET;
    end
    else begin
      state_curr <= state_next;
    end
  end

  always_comb begin

    case(op)

      r_type_op: begin
        ImmSrc = 2'b00; 
      end
      i_type_alu_op: begin
        ImmSrc = 2'b00; 
      end
      lw_op : begin
        ImmSrc = 2'b00; 
      end
      sw_op : begin
        ImmSrc = 2'b01; 
      end
      beq_op : begin
        ImmSrc = 2'b10; 
      end
      jal_op : begin
        ImmSrc = 2'b11; 
      end
      default: begin
        ImmSrc = 2'b00;
      end
    endcase 

    case (state_curr)

      FET: begin
        AdrSrc = 1'b0;
        IRWrite = 1'b1; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b00;
        ALUSrcB = 2'b10;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b10;
        PCUpdate = 1'b1;
        Branch = 1'b0;

        state_next = DEC;

      end

      DEC: begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b01;
        ALUSrcB = 2'b01;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        case (op) 

          r_type_op: begin
            state_next = ExecuteR;
          end
          i_type_alu_op: begin
            state_next = ExecuteI;
          end
          lw_op : begin
            state_next = MemAD;
          end
          sw_op : begin
            state_next = MemAD;
          end
          beq_op : begin
            state_next = BEQ;
          end
          jal_op : begin
            state_next = JAL; 
          end
          default: begin
            state_next = FET; 
          end
        endcase 
      end

      MemAD :  begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b01;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        if(op == sw_op) begin
          state_next = MemWR;
        end
        else if(op == lw_op) begin
          state_next = MemREAD;
        end
        else begin
          state_next = FET;
        end
      end

      MemREAD : begin

        AdrSrc = 1'b1;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b01;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        state_next = MemWB;

      end

      ExecuteR : begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b00;
        ALUOp = 2'b10;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        state_next = ALUWB; 

      end

      ExecuteI : begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b01;
        ALUOp = 2'b10;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        state_next = ALUWB; 

      end

      JAL : begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b01;
        ALUSrcB = 2'b10;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b1;
        Branch = 1'b0;

        state_next = ALUWB; 

      end

      BEQ : begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b00;
        ALUOp = 2'b01;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b1;

        state_next = FET; 

      end

      ALUWB : begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b01;
        ALUOp = 2'b10;
        RegWrite = 1'b1;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        state_next = FET;
        
      end 

      MemWB : begin

        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b01;
        ALUOp = 2'b00;
        RegWrite = 1'b1;
        ResultSrc = 2'b01;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        state_next = FET;

      end

      MemWR : begin
        
        AdrSrc = 1'b1;
        IRWrite = 1'b0; 
        MemWrite = 1'b1;
        ALUSrcA = 2'b10;
        ALUSrcB = 2'b01;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;

        state_next = FET;

      end

      default: begin
        AdrSrc = 1'b0;
        IRWrite = 1'b0; 
        MemWrite = 1'b0;
        ALUSrcA = 2'b00;
        ALUSrcB = 2'b00;
        ALUOp = 2'b00;
        RegWrite = 1'b0;
        ResultSrc = 2'b00;
        PCUpdate = 1'b0;
        Branch = 1'b0;
        state_next = FET; 
      end

    endcase 

  end

  assign PCWrite = (Zero && Branch) || PCUpdate; 

endmodule

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  always_ff @(posedge clk)
    if (we3) begin
       if(a3 != 0) rf[a3] <= wd3;	
    end 
  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module aludecoder(input  logic [1:0] ALUOp,
                  input  logic [2:0] funct3,
                  input  logic op_5, funct7_5,
                  output logic [2:0] ALUControl);
              
	assign ALUControl[0] = (ALUOp[1] && (~funct3[0] && (funct3[1] || (funct7_5 && op_5)))) | (ALUOp[0]);
	assign ALUControl[1] = ALUOp[1] && funct3[2];   
	assign ALUControl[2] = ALUOp[1] && (~funct3[2] && funct3[1]);
    

endmodule

module ALU(
    input logic[31:0] a,
    input logic[31:0] b,
    input logic[2:0] ALUControl,
    output logic[31:0] result,
    output logic zero
);


always_comb begin

    case(ALUControl) 

        3'b000: begin
            result = a + b;
        end
        3'b001: begin
            result = a - b;
        end
        3'b010: begin
            result = a&b;
        end
        3'b011: begin
            result = a|b;
        end
        3'b100: begin
            result = (a<b) ? 32'd1 : 32'd0; 
        end
        default: begin
            result = 32'hxxxxx;
        end
    endcase

end

assign zero = ((a-b) == 32'd0);


endmodule 

module ExtendImm (

    input logic[31:7] Instr,
    input logic[1:0] ImmSrc,
    output logic[31:0] ImmExt
);


always_comb begin

    case(ImmSrc)

        2'b00: begin //I type of lw instruction, it also serves as default case for R type
            ImmExt = {{20{Instr[31]}}  , Instr[31:20]};
        end
        2'b01: begin //S type instruction, 
            ImmExt = {{20{Instr[31]}},Instr[31:25],Instr[11:7]};
        end
        2'b10: begin //B type instruction
            ImmExt = {{19{Instr[31]}},Instr[31],Instr[7],Instr[30:25],Instr[11:8],1'b0};
        end
        2'b11: begin //J Type instruction
            ImmExt = {{11{Instr[31]}},Instr[31],Instr[19:12],Instr[20],Instr[30:21],1'b0};
        end
        default: begin
            ImmExt = 32'bx; 
        end

    endcase

end

endmodule 

module datapath(

  input logic PCWrite, AdrSrc, IRWrite, RegWrite, clk,
  input logic[1:0] ImmSrc, ALUSrcA, ALUSrcB, ResultSrc,
  input logic[2:0] ALUControl,
  input logic[31:0] ReadData,
  output logic[31:0]  WriteMM,
  output logic[31:0] Adress,
  output logic[31:0] Instr,
  output logic Zero
);

logic[31:0] PC, PC_Next, IR_Curr, IR_Next, PC_OldC, PC_OldN, RD1_Next, RD1_Curr, RD2_Next, RD2_Curr, ALUResult_Next, ALUResult_Curr, Data_Curr, Data_Next, Result, SrcA, SrcB, ImmExtend;
logic[4:0] rs1, rs2, rd;

always_ff@(posedge clk) begin

  if(PCWrite) PC <= PC_Next;
  else begin
    PC <= PC;
  end

  if(IRWrite) begin
    IR_Curr <= IR_Next;
    PC_OldC <= PC_OldN;
  end
  else begin
    IR_Curr <= IR_Curr;
    PC_OldC <= PC_OldC;
  end

  RD1_Curr <= RD1_Next;
  RD2_Curr <= RD2_Next;
  ALUResult_Curr <= ALUResult_Next;
  Data_Curr <= Data_Next;

end

assign rs1 = IR_Curr[19:15];
assign rs2 = IR_Curr[24:20];
assign rs3 = IR_Curr[11:7];
assign Adress = AdrSrc ? Result : PC; 
assign IR_Next = ReadData;
assign Data_Next = ReadData;
assign PC_OldN = PC;
assign PC_Next = Result;
assign SrcA = ALUSrcA[1] ? RD1_Curr : (ALUSrcA[0] ? PC_OldC : PC);
assign SrcB = ALUSrcB[1] ? 32'd4 : (ALUSrcB[0] ? ImmExtend : RD2_Curr);  
assign Result = ResultSrc[1] ? ALUResult_Next : (ResultSrc[0] ? Data_Curr : ALUResult_Curr);
assign WriteMM = RD2_Curr;
assign Instr = IR_Curr;

ALU myALU(SrcA, SrcB, ALUControl, ALUResult_Next, Zero);
ExtendImm Extend(IR_Curr[31:7],ImmSrc,ImmExtend);
regfile RegWr(clk, RegWrite, rs1, rs2, rd, Result, RD1_Next, RD2_Next);

endmodule

///////////////////////////////////////////////////////////////


