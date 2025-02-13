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