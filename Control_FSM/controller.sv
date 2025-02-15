// controller.sv
//
// This file is for HMC E85A Lab 5.
// Place controller.tv in same computer directory as this file to test your multicycle controller.
//
// Starter code last updated by Ben Bracker (bbracker@hmc.edu) 1/14/21
// - added opcodetype enum
// - updated testbench and hash generator to accomodate don't cares as expected outputs
// Solution code by ________ (Mauricio Minaya) ________

typedef enum logic[6:0] {r_type_op=7'b0110011, i_type_alu_op=7'b0010011, lw_op=7'b0000011, sw_op=7'b0100011, beq_op=7'b1100011, jal_op=7'b1101111} opcodetype;

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

module aludecoder(input  logic [1:0] ALUOp,
                  input  logic [2:0] funct3,
                  input  logic op_5, funct7_5,
                  output logic [2:0] ALUControl);
              
    // For Lab 2, write a structural Verilog model 
    // use and, or, not
    // do not use assign statements, always blocks, or other behavioral Verilog
    // Example syntax to access bits to make ALUControl[0] = ~funct3[0]
    //  not g1(ALUControl[0], funct3[0]);
    // This is just an example; replace this with correct logic!
	assign ALUControl[0] = (ALUOp[1] && (~funct3[0] && (funct3[1] || (funct7_5 && op_5)))) | (ALUOp[0]);
	assign ALUControl[1] = ALUOp[1] && funct3[2];   
	assign ALUControl[2] = ALUOp[1] && (~funct3[2] && funct3[1]);
    

endmodule

module testbench();

  logic        clk;
  logic        reset;
  
  opcodetype  op;
  logic [2:0] funct3;
  logic       funct7b5;
  logic       Zero;
  logic [1:0] ImmSrc;
  logic [1:0] ALUSrcA, ALUSrcB;
  logic [1:0] ResultSrc;
  logic       AdrSrc;
  logic [2:0] ALUControl;
  logic       IRWrite, PCWrite;
  logic       RegWrite, MemWrite;
  
  logic [31:0] vectornum, errors;
  logic [39:0] testvectors[10000:0];
  
  logic        new_error;
  logic [15:0] expected;
  logic [6:0]  hash;


  // instantiate device to be tested
  controller dut(clk, reset, op, funct3, funct7b5, Zero,
                 ImmSrc, ALUSrcA, ALUSrcB, ResultSrc, AdrSrc, ALUControl, IRWrite, PCWrite, RegWrite, MemWrite);
  
  // generate clock
  always 
    begin
      clk = 1; #5; clk = 0; #5;
    end

  // at start of test, load vectors and pulse reset
  initial
    begin
      $readmemb("controller.tv", testvectors);
      vectornum = 0; errors = 0; hash = 0;
      reset = 1; #22; reset = 0;
    end
	 
  // apply test vectors on rising edge of clk
  always @(posedge clk)
    begin
      #1; {op, funct3, funct7b5, Zero, expected} = testvectors[vectornum];
    end

  // check results on falling edge of clk
  always @(negedge clk)
    if (~reset) begin // skip cycles during reset
      new_error=0; 

      if ((ImmSrc!==expected[15:14])&&(expected[15:14]!==2'bxx))  begin
        $display("   ImmSrc = %b      Expected %b", ImmSrc,     expected[15:14]);
        new_error=1;
      end
      if ((ALUSrcA!==expected[13:12])&&(expected[13:12]!==2'bxx)) begin
        $display("   ALUSrcA = %b     Expected %b", ALUSrcA,    expected[13:12]);
        new_error=1;
      end
      if ((ALUSrcB!==expected[11:10])&&(expected[11:10]!==2'bxx)) begin
        $display("   ALUSrcB = %b     Expected %b", ALUSrcB,    expected[11:10]);
        new_error=1;
      end
      if ((ResultSrc!==expected[9:8])&&(expected[9:8]!==2'bxx))   begin
        $display("   ResultSrc = %b   Expected %b", ResultSrc,  expected[9:8]);
        new_error=1;
      end
      if ((AdrSrc!==expected[7])&&(expected[7]!==1'bx))           begin
        $display("   AdrSrc = %b       Expected %b", AdrSrc,     expected[7]);
        new_error=1;
      end
      if ((ALUControl!==expected[6:4])&&(expected[6:4]!==3'bxxx)) begin
        $display("   ALUControl = %b Expected %b", ALUControl, expected[6:4]);
        new_error=1;
      end
      if ((IRWrite!==expected[3])&&(expected[3]!==1'bx))          begin
        $display("   IRWrite = %b      Expected %b", IRWrite,    expected[3]);
        new_error=1;
      end
      if ((PCWrite!==expected[2])&&(expected[2]!==1'bx))          begin
        $display("   PCWrite = %b      Expected %b", PCWrite,    expected[2]);
        new_error=1;
      end
      if ((RegWrite!==expected[1])&&(expected[1]!==1'bx))         begin
        $display("   RegWrite = %b     Expected %b", RegWrite,   expected[1]);
        new_error=1;
      end
      if ((MemWrite!==expected[0])&&(expected[0]!==1'bx))         begin
        $display("   MemWrite = %b     Expected %b", MemWrite,   expected[0]);
        new_error=1;
      end

      if (new_error) begin
        $display("Error on vector %d: inputs: op = %h funct3 = %h funct7b5 = %h", vectornum, op, funct3, funct7b5);
        errors = errors + 1;
      end
      vectornum = vectornum + 1;
      hash = hash ^ {ImmSrc&{2{expected[15:14]!==2'bxx}}, ALUSrcA&{2{expected[13:12]!==2'bxx}}} ^ {ALUSrcB&{2{expected[11:10]!==2'bxx}}, ResultSrc&{2{expected[9:8]!==2'bxx}}} ^ {AdrSrc&{expected[7]!==1'bx}, ALUControl&{3{expected[6:4]!==3'bxxx}}} ^ {IRWrite&{expected[3]!==1'bx}, PCWrite&{expected[2]!==1'bx}, RegWrite&{expected[1]!==1'bx}, MemWrite&{expected[0]!==1'bx}};
      hash = {hash[5:0], hash[6] ^ hash[5]};
      if (testvectors[vectornum] === 40'bx) begin 
        $display("%d tests completed with %d errors", vectornum, errors);
	      $display("hash = %h", hash);
        $stop;
      end
    end
endmodule

