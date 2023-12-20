//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #( 
    parameter BIT_W = 32                                                                                    //
                                                                          //
)(                                                                               //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        // mem_rdata_I
        output [BIT_W-1:0]  o_IMEM_addr,                                                        // mem_addr_I
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       // 
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        // mem_addr_d
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration
localparam ADD   = 7'b0110011;
    localparam SUB   = 7'b0110011;
    localparam XOR   = 7'b0110011;
    localparam MUL   = 7'b0110011;
    localparam AND   = 7'b0110011;
    // I-type
    localparam ADDI  = 7'b0010011;
    localparam SLTI   = 7'b0010011;
    localparam LW    = 7'b0000011;
    // Shift
    localparam SLLI = 7'b0010011;
    localparam SRAI = 7'b0010011;
    // B-type
    localparam BEQ   = 7'b1100011;
    localparam BGE =7'b1100011; 
    localparam BNE = 7'b1100011;
    localparam BLT = 7'b1100011;
    // S-type
    localparam SW    = 7'b0100011;
    // J-type
    localparam JAL   = 7'b1101111;
    localparam JALR  = 7'b1100111;
    // U-type
    localparam AUIPC = 7'b0010111;
    // ECALL
    localparam ECALL = 7'b1110011;
    
    //====== funct3 ======
    localparam ADD_FUNC3  = 3'b000;
    localparam SUB_FUNC3  = 3'b000;
    localparam XOR_FUNC3  = 3'b100;
    localparam ADDI_FUNC3 = 3'b000;
    localparam SLTI_FUNC3 = 3'b010;
    localparam MUL_FUNC3  = 3'b000;
    localparam AND_FUNC3 = 3'b111;
    localparam BEQ_FUNC3 = 3'b000;
    localparam BNE_FUNC3 = 3'b001;
    localparam BGE_FUNC3 = 3'b101;
    localparam BLT_FUNC3 = 3'b100;
    localparam SLLI_FUNC3 = 3'b001;
    localparam SRAI_FUNC3 = 3'b101;


    //====== funct7 ======
    localparam ADD_FUNC7 = 7'b0000000;
    localparam SUB_FUNC7 = 7'b0100000;
    localparam XOR_FUNC7 = 7'b0000000;
    localparam AND_FUNC7 = 7'b0000000;
    localparam MUL_FUNC7 = 7'b0000001;
    localparam SLLI_FUNC7 = 7'b0010011; 
    localparam SRAI_FUNC7  = 7'b0010011;

    // FSM state
    localparam S_IDLE        = 0;
    localparam S_EXEC        = 1;
    localparam S_EXEC_MULDIV = 2;
    localparam S_LW = 3;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;
        reg regWrite;
        reg finish;
        reg    [ 4:0] rs1, rs2, rd;              //
        wire   [31:0] rs1_data    ;              //
        wire   [31:0] rs2_data    ;              //
        reg    [31:0] rd_data     ;              //

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
    reg  [6:0 ] op_code_w;
    reg  [31:0] inst_w;
    reg  [1:0 ] state_w, state_r;
    reg  [2:0 ] funct3_w;
    reg  [6:0 ] funct7_w;
    reg  [31:0] imm_w;
    reg  [31:0] mem_addr_D_w, mem_wdata_D_w;
    reg         mem_wen_D_w;
    reg         mem_cen_D_w;
    reg         ins_cen_D_w;
    reg         mulDiv_vld_w;
    wire        mulDiv_rdy_w;
    reg  [2:0]  mulDiv_mode_w;
    reg  [31:0] mulDiv_in_A_w, mulDiv_in_B_w;
    wire [63:0] mulDiv_out_w;
    

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (regWrite),          
        .rs1    (rs1),                
        .rs2    (rs2),                
        .rd     (rd),                 
        .wdata  (rd_data),             
        .rdata1 (rs1_data),           
        .rdata2 (rs2_data)
    );
    // i_clk, i_rst_n, i_valid, i_A, i_B, i_inst, o_data, o_done
    MULDIV_unit mulDiv0(
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(mulDiv_vld_w),
        .i_inst(mulDiv_mode_w),
        .i_A(mulDiv_in_A_w),
        .i_B(mulDiv_in_B_w),
        .o_data(mulDiv_out_w),
         .o_done(mulDiv_rdy_w)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    assign o_IMEM_addr = PC;
    assign o_DMEM_addr = mem_addr_D_w;
    assign o_DMEM_wdata = mem_wdata_D_w;
    assign o_DMEM_wen = mem_wen_D_w;
    assign o_DMEM_cen = mem_cen_D_w;
    assign o_IMEM_cen = ins_cen_D_w;
    // Todo: any combinational/sequential circuit
    always @(*) begin
        ins_cen_D_w = 1'b1;     // pull high to read instruction
        inst_w = i_IMEM_data;
        next_PC = PC + 3'd4;
        op_code_w = inst_w[6:0];
        funct3_w = inst_w[14:12];
        funct7_w = inst_w[31:25];
        rs1 = inst_w[19:15];
        rs2 = inst_w[24:20];
        rd  = inst_w[11:7];
        rd_data = 0;
        imm_w = 0;
        mem_addr_D_w = 0;
        mem_wdata_D_w = 0;
        mem_wen_D_w = 0;
        mem_cen_D_w = 0;
        regWrite = 0;
        finish = 0;
        mulDiv_vld_w = 0;
        mulDiv_in_A_w = rs1_data;
        mulDiv_in_B_w = rs2_data;
        mulDiv_mode_w = 0;
        case (op_code_w)
            7'b0110011: begin
                regWrite = 1'b1;
                // finish = 1'b0;
                case ({funct7_w, funct3_w})
                    {ADD_FUNC7, ADD_FUNC3}: begin
                        rd_data = $signed(rs1_data) + $signed(rs2_data);
                    end
                    {SUB_FUNC7, SUB_FUNC3}: begin
                        rd_data = $signed(rs1_data) - $signed(rs2_data);
                    end
                    {XOR_FUNC7, XOR_FUNC3}: begin
                        rd_data = rs1_data ^ rs2_data;
                    end
                    {AND_FUNC7, AND_FUNC3}: begin
                        rd_data = rs1_data & rs2_data;
                    end

                    {MUL_FUNC7, MUL_FUNC3}: begin
                        if(mulDiv_rdy_w) begin
                           next_PC = PC + 3'd4; 
                            regWrite = 1'b1;
                        end
                        else begin
                            next_PC = PC;
                            regWrite = 0;
                        end
                        mulDiv_vld_w = 1'b1;
                        mulDiv_mode_w = 3'b110;
                        rd_data = mulDiv_out_w[31:0];
                    end
                endcase
            end
            7'b0010011: begin
                regWrite = 1'b1;
                // finish = 1'b0;
                imm_w[11:0] = inst_w[31:20];
                case (funct3_w)
                    ADDI_FUNC3: begin
                        rd_data = $signed(rs1_data) + $signed(imm_w[11:0]);
                    end
                    SLTI_FUNC3: begin
                        if($signed(rs1_data) < $signed(imm_w[11:0])) rd_data = 32'd1;
                        else                                         rd_data = 32'd0;
                    end
                    SLLI_FUNC3: begin
                        rd_data = rs1_data << imm_w[4:0];
                    end
                    SRAI_FUNC3: begin
                        rd_data = $signed(rs1_data) >>> imm_w[4:0];
                    end
                endcase
            end
            7'b1100011:begin
                imm_w[12:0] = {inst_w[31], inst_w[7], inst_w[30:25], inst_w[11:8], 1'b0};
                // finish = 1'b0;
                case (funct3_w)
                    BEQ_FUNC3: begin
                        // next_PC = PC;
                        // if(!i_DMEM_stall) next_PC = PC + 3'd4;
                        if($signed(rs1_data) == $signed(rs2_data)) next_PC = $signed({1'b0, PC}) + $signed(imm_w[12:0]);
                        else                     next_PC = PC + 3'd4;
                    end
                    BNE_FUNC3: begin
                        // next_PC = PC;
                        // if(!i_DMEM_stall) next_PC = PC + 3'd4;
                        if($signed(rs1_data) == $signed(rs2_data)) next_PC = PC + 3'd4;
                        else                    next_PC = $signed({1'b0, PC}) + $signed(imm_w[12:0]);
                    end
                    BGE_FUNC3: begin
                        // next_PC = PC;
                        //  if(!i_DMEM_stall) next_PC = PC + 3'd4;
                        if($signed(rs1_data) >= $signed(rs2_data)) next_PC = $signed({1'b0, PC}) + $signed(imm_w[12:0]);
                        else                    next_PC = PC + 3'd4;
                    end
                    BLT_FUNC3: begin
                        // next_PC = PC;
                        // if(!i_DMEM_stall) next_PC = PC + 3'd4;
                        if($signed(rs1_data) < $signed(rs2_data)) next_PC = $signed({1'b0, PC}) + $signed(imm_w[12:0]);
                        else                    next_PC = PC + 3'd4;
                    end

                endcase 

            end
            
            LW: begin
                // wait for stall
                next_PC = PC;
                if(!i_DMEM_stall) next_PC = PC + 3'd4;

                regWrite = 1'b1;
                mem_cen_D_w = 1'b1;
                mem_wen_D_w = 1'b0;
                // finish = 1'b0;
                imm_w[11:0] = inst_w[31:20];
                mem_addr_D_w = $signed({1'b0, rs1_data}) + $signed(imm_w[11:0]);
                rd_data = i_DMEM_rdata;
            end
            
            SW: begin
                next_PC = PC;
                if(!i_DMEM_stall) next_PC = PC + 3'd4;

                // finish = 1'b0;
                mem_cen_D_w = 1'b1;
                mem_wen_D_w = 1'b1;
                imm_w[4:0] = inst_w[11:7];
                imm_w[11:5] = inst_w[31:25];
                mem_addr_D_w = $signed({1'b0, rs1_data}) + $signed(imm_w[11:0]);
                mem_wdata_D_w = rs2_data;
            end
            AUIPC: begin
                // finish = 1'b0;
                regWrite = 1'b1;
                imm_w[31:12] = inst_w[31:12];
                rd_data = PC + imm_w;
            end
            JAL: begin
                // finish = 1'b0;
                imm_w[20:0] = {inst_w[31], inst_w[19:12], inst_w[20], inst_w[30:21], 1'b0};
                next_PC = $signed({1'b0, PC}) + $signed(imm_w[20:0]);
                regWrite = 1'b1;
                rd_data = PC + 3'd4;
            end
            JALR: begin
                // finish = 1'b0;
                imm_w[11:0] = inst_w[31:20];
                next_PC = $signed({1'b0, rs1_data}) + $signed(imm_w[11:0]);
                regWrite = 1'b1;
                rd_data = PC + 3'd4;
            end
            ECALL: begin
                finish = 1'b1;
            end
        endcase
    end
    // FSM
    always @(*) begin
        state_w = state_r;
        case (state_r)
            S_IDLE: begin
                // if(i_mem_stall) state_w = S_LW;
                state_w = (op_code_w == 7'b0110011 && ({funct7_w, funct3_w} == {MUL_FUNC7, MUL_FUNC3})) ?
                        S_EXEC_MULDIV :
                        S_EXEC;
                // if(op_code_w==7'b0000011 || op_code_w==7'b0100011){
                //     state_w = S_LW;
                // }
                
            end
            S_EXEC: begin
                state_w = (op_code_w == 7'b0110011 && ({funct7_w, funct3_w} == {MUL_FUNC7, MUL_FUNC3})) ?
                        S_EXEC_MULDIV :
                        S_EXEC;
            end
            S_EXEC_MULDIV: begin
                state_w = (mulDiv_rdy_w) ? S_EXEC : S_EXEC_MULDIV;
            end 
            S_LW: begin
                state_w = (i_DMEM_stall) ? S_LW :S_EXEC;
            end
        endcase
    end
    // sequential 
    assign o_finish = finish;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state_r <= S_IDLE;
        end
        else begin
            PC <= next_PC;
            state_r <= state_w;
            
        end
    end
endmodule
// clk, rst_n, wen, a1, a2, aw, d, q1, q2
module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module MULDIV_unit#(
        parameter BIT_W = 32,
        parameter DATA_W = 32
    )(i_clk, i_rst_n, i_valid, i_A, i_B, i_inst, o_data, o_done);
    // TODO: port declaration
    input                       i_clk;   // clock
    input                       i_rst_n; // reset
    input                       i_valid; //input valid signal
    input [BIT_W - 1 : 0]      i_A;     // input operand A
    input [BIT_W - 1 : 0]      i_B;     // input operand B
    input [         2 : 0]      i_inst;  // instruction

    output [2*BIT_W - 1 : 0]   o_data;  // output value
    output                      o_done;   // output valid signal
    
    parameter S_IDLE = 4'd0;
    parameter S_ADD  = 4'd1;
    parameter S_SUB  = 4'd2;
    parameter S_AND  = 4'd3;
    parameter S_OR   = 4'd4;
    parameter S_SLT  = 4'd5;
    parameter S_SRA  = 4'd6;
    parameter S_MUL  = 4'd7;
    parameter S_DIV  = 4'd8;
    parameter S_OUT  = 4'd9;

    // Wires & Regs
    // Todo
    // state
    reg  [3: 0] state, state_nxt; // remember to expand the bit width if you want to add more states!
    // load input
    reg  [  BIT_W-1: 0] in_data, in_data_nxt, buffer;
    reg  [  BIT_W: 0] out_data;
    // reg  [2: 0] inst, inst_nxt;
    reg  [4: 0] counter, counter_nxt;
    reg  [2*BIT_W - 1 : 0] shift, shift_nxt, data ;
    reg  done;
    // Wire Assignments
    // Todo
    // Todo: FSM
    always @(*) begin
        case(state)
            S_IDLE :begin
                done = 0;
                if (i_valid) begin
                    case(i_inst)
                            0: state_nxt = S_ADD;
                            1: state_nxt = S_SUB;
                            2: state_nxt = S_AND; 
                            3: state_nxt = S_OR;
                            4: state_nxt = S_SLT;
                            5: state_nxt = S_SRA;
                            6: state_nxt = S_MUL;
                            7: state_nxt = S_DIV;
                        endcase
                end  
                else state_nxt = S_IDLE;
            end
            S_ADD   : begin
                done = 1'b0;
                state_nxt = S_OUT;
            end
            S_SUB   : begin
               done = 1'b0;
                state_nxt = S_OUT;
            end
            S_AND : begin
                done = 1'b0;
                state_nxt = S_OUT;
            end
            S_OR : begin
                done = 1'b0;
                state_nxt = S_OUT;
            end
            S_SLT : begin
                done = 1'b0;
                state_nxt = S_OUT;
            end
            S_SRA : begin
                done = 1'b0;
                state_nxt = S_OUT;
            end
            S_MUL : begin
                done = 1'b0;
                if(counter == 31) state_nxt = S_OUT;
                else state_nxt = S_MUL;
            end
            S_DIV : begin
                done = 1'b0;
                if(counter == 31) state_nxt = S_OUT;
                else state_nxt = S_DIV;
            end
            S_OUT: begin
                done = 1'b1;
                state_nxt = S_IDLE;
            end
            default : begin
                done = 1'b0;
                state_nxt = S_IDLE;
            end
        endcase
    end
    // Todo: Counter
    always @(*) begin
        case(state)
            S_MUL: if(counter==31) counter_nxt = 0;
                    else counter_nxt =counter+1;
            S_DIV: if(counter==31) counter_nxt = 0;
                    else counter_nxt =counter+1;
            default : counter_nxt = 0;
            
        endcase
    end

    // Todo: ALU output
    always @(*) begin
        case(state)
            S_IDLE:begin
                if(i_valid) begin
                    case(i_inst)
                    // signed extend
                        0: in_data_nxt = {{32{i_B[31]}}, i_B};
                        1: in_data_nxt = {{32{i_B[31]}}, i_B};
                        4: in_data_nxt = {{32{i_B[31]}}, i_B};
                        5: in_data_nxt = {{32{i_B[31]}}, i_B};
                    default: in_data_nxt = {32'b0, i_B}; //default to 0 signed (unsigned)
                    endcase
                end
                else in_data_nxt = 0;
            end
                S_OUT : in_data_nxt = 0;
                default: in_data_nxt = in_data;
        endcase
    end

    always @(*) begin
        case(state)
            S_IDLE: out_data = 0;
            S_ADD: begin
                out_data = shift+in_data;
                if(in_data[DATA_W-1] && shift[DATA_W-1] && ~ out_data[DATA_W-1]) begin
                    out_data = 0;
                    out_data[DATA_W-1] = 1;
                end
                else if(~in_data[DATA_W-1] & ~shift[DATA_W-1] & out_data[DATA_W-1]) begin
                    buffer = 0;
                    out_data = ~buffer;
                    out_data[DATA_W-1] = 0;
                    out_data[DATA_W] = 0; //NOTICE !!;
                    
                end
                else out_data = {1'b0, out_data[DATA_W-1:0]};
            end
            S_SUB: begin
                out_data = shift - in_data;
                if(~in_data[DATA_W-1] && shift[DATA_W-1] && ~ out_data[DATA_W-1]) begin
                    out_data = 0;
                    out_data[DATA_W-1] = 1;
                end
                else if(in_data[DATA_W-1] & ~shift[DATA_W-1] & out_data[DATA_W-1]) begin
                    buffer = 0;
                    out_data = ~buffer;
                    out_data[DATA_W-1] = 0;
                    out_data[DATA_W] = 0; //NOTICE !!;
                    
                end
                else out_data = {1'b0, out_data[DATA_W-1:0]};
            end
            S_AND: out_data = shift & in_data;
            S_OR: out_data = shift | in_data;
            S_SLT: out_data = ($signed(shift)<$signed(in_data)?1:0);
            S_SRA: out_data = $signed(shift)>>>$signed(in_data);
            S_MUL: if(shift[0]) out_data = shift[63:32] + in_data;
                        else out_data = shift[63:32];
            S_DIV: begin
                if(shift[63:32]>=in_data) begin
                    out_data = {1'b1,shift[63:32]-in_data};
                end
                else out_data = {1'b0, shift[63:32]};
            end
            default: out_data = 0;
        endcase
    end

    always @(*) begin
        case(state)
            S_IDLE:begin
                data = 0;
                if(i_valid) begin
                    case(i_inst)
                        0: shift_nxt = {{32{i_A[31]}},i_A};
                        1: shift_nxt = {{32{i_A[31]}},i_A};
                        4: shift_nxt = {{32{i_A[31]}},i_A};
                        5: shift_nxt = {{32{i_A[31]}},i_A};
                        7: shift_nxt = {31'b0,i_A,1'b0};
                        default : shift_nxt = {32'b0,i_A};
                    endcase
                end
                else shift_nxt = 0;
            end
            S_ADD : begin
                data = 0;
                shift_nxt = {32'b0,out_data[31:0]};
            end
            S_SUB : begin
                data = 0;
                shift_nxt = {32'b0,out_data[31:0]};
            end
            S_AND : begin
                data = 0;
                shift_nxt = {32'b0,out_data[31:0]};
            end
            S_OR : begin
                data = 0;
                shift_nxt = {32'b0,out_data[31:0]};
            end
            S_SLT : begin
                data = 0;
                shift_nxt = {32'b0,out_data[31:0]};
            end
            S_SRA : begin
                data = 0;
                shift_nxt = {32'b0,out_data[31:0]};
            end
            S_MUL : begin
                data = 0;
                shift_nxt = {out_data,shift[31:1]}; //right shift
            end
            S_DIV : begin 
                data = 0;
                if (counter==31) shift_nxt  = {out_data[31:0],shift[30:0],out_data[32]};
                else shift_nxt = {out_data[30:0],shift[31:0],out_data[32]};
            end
            S_OUT: begin
                shift_nxt  = 0;
                if(done) data = shift;
                else data = 0;
            end
            default:begin
                shift_nxt = 0;
                data = 0;
            end
        endcase
    end
    
    // Todo: output valid signal
    assign o_data = data;
    assign o_done = done;
    // Todo: Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state       <= S_IDLE;
        end
        else begin
            state       <= state_nxt;
            counter <= counter_nxt;
            in_data <= in_data_nxt;
            shift <= shift_nxt;
        end
    end
    // Todo: HW2
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available,
        // others
        input  [ADDR_W-1: 0] i_offset
    );

    assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    
    assign o_mem_cen = i_proc_cen;              //
    assign o_mem_wen = i_proc_wen;              //
    assign o_mem_addr = i_proc_addr;            //
    assign o_mem_wdata = i_proc_wdata;          //
    assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: BONUS
    
    //==== 2-way cache structure ==============================
    /**
        - 32 bit address : 25 tag, 3 index, 4 offset.
        - 16 addresses access the same 128 bits data in memory.
        - First four addresses access the first 32 bits in the 128 bits, and so on.
        - Store 2*128 bits for data in a set.
    **/

    //==== state definition ===================================
        parameter READY = 2'b00; 
        parameter MISS  = 2'b01;
        parameter WRITE  = 2'b10; 
    //==== wire/reg definition ================================
        wire [27:0]  proc_addr; 
        reg          mem_cen,mem_wen,proc_stall;
        reg          mem_write_w, mem_write_r;
        reg  [31:0]  mem_addr_w, mem_addr_r;
        reg  [31:0]  mem_wdata_w, mem_wdata_r;
        reg  [1:0]   state_w, state_r;
        reg  [152:0]  cache_w[0:3], cache_r[0:3];  // TODO: size not sure,  1 valid + 24 tag + 128 data ?
        reg  [55:0]  tag_w[0:3], tag_r[0:3];
        reg          lru_w[0:3], lru_r[0:3];
        wire [2:0]   index; // 3 bits for index ( 2-way )
        wire [255:0]  data; // 2*128 bits for data in a set ( 2 blocks )
        wire [49:0]  tag;   // 24 bits for each tag ( 2 blocks )
        wire         lru;
        wire         hit1, hit0;
        wire         hit;
        integer i;

    //==== combinational circuit ==============================
        // 25 bits for tag, 3 bits for index, 4 bits for offset
        assign proc_addr = i_proc_addr[31:4];   // tag bits + index bits
        assign index = proc_addr[2:0];  // address[7:4] for index
        assign {tag, data, lru} = {tag_r[index], cache_r[index], lru_r[index]};
        assign hit1 = (tag[49:25] == proc_addr[27:3]);  // tag bits for subset 2
        assign hit0 = (tag[24:0] == proc_addr[27:3]);   // tag bits for subset 1
        assign hit = hit1 || hit0;
        assign o_mem_addr = mem_addr_r;
        assign o_mem_wdata = mem_wdata_r;
        assign o_mem_cen = mem_cen;
        assign o_mem_wen = mem_wen;
        assign o_proc_stall = proc_stall;
        assign o_proc_rdata = (hit1)? data[255:128]: data[127:0];  

       always @(*) begin
            case(state_r)
                READY: begin
                    if(i_proc_cen) begin
                        if(hit) begin
                            if(!i_proc_wen) begin   // active high for write
                                // read hit
                                proc_stall = 1'b0;
                                state_w = state_r;
                                mem_cen = 1'b0;
                                mem_wen = 1'b0;
                                mem_addr_w = mem_addr_r;
                                mem_wdata_w = mem_wdata_r;
                            end
                            else begin
                                // write hit
                                proc_stall = 1'b1;
                                state_w = WRITE;
                                mem_cen = 1'b1;
                                mem_wen = 1'b1;
                                mem_addr_w = i_proc_addr;
                                mem_wdata_w = i_proc_wdata;
                            end
                        end
                        else begin
                            // miss
                            proc_stall = 1'b1;
                            state_w = MISS;
                            mem_cen = 1'b1;
                            mem_wen = 1'b0;
                            mem_addr_w = i_proc_addr;
                            mem_wdata_w = lru ? data[63:32] : data[31:0];
                        end
                    end
                    else begin
                        proc_stall = 1'b0;
                        state_w = state_r;
                        mem_cen = 1'b0;
                        mem_wen = 1'b0;
                        mem_addr_w = mem_addr_r;
                        mem_wdata_w = mem_wdata_r;

                    end
                end
                MISS: begin
                    // read
                    if(~i_mem_stall) begin
                        if(!i_proc_wen) begin
                            // read miss
                            proc_stall = 1'b1;
                            state_w = READY;
                            mem_cen = 1'b0;
                            mem_wen = 1'b0;
                            mem_addr_w = i_proc_addr;
                            mem_wdata_w = lru ? data[63:32] : data[31:0];
                        end
                        else begin
                            // write miss
                            proc_stall = 1'b1;
                            state_w = WRITE;
                            mem_cen = 1'b1;
                            mem_wen = 1'b1;
                            mem_addr_w = i_proc_addr;
                            mem_wdata_w = i_proc_wdata;
                        end
                    end
                    else begin
                        proc_stall = 1'b1;
                        state_w = MISS;
                        mem_cen = 1'b1;
                        mem_wen = 1'b0;
                        mem_addr_w = mem_addr_r;
                        mem_wdata_w = lru ? data[63:32] : data[31:0];
                    end
                end
                WRITE: begin
                    if(~i_mem_stall) begin
                            proc_stall = 1'b1;
                            state_w = READY;
                            mem_cen = 1'b0;
                            mem_wen = 1'b0;
                            mem_addr_w = i_proc_addr;
                            mem_wdata_w = lru ? data[63:32] : data[31:0];
                        end
                    else begin
                            proc_stall = 1'b1;
                            state_w = WRITE;
                            mem_cen = 1'b1;
                            mem_wen = 1'b1;
                            mem_addr_w = mem_addr_r;
                            mem_wdata_w = mem_wdata_r;
                        end
                    end
                default: begin
                    proc_stall = 1'b1;
                    state_w = READY;
                    mem_cen = 1'b0;
                    mem_wen = 1'b1;
                    mem_addr_w = mem_addr_r;
                    mem_wdata_w = mem_wdata_r;
                end
            endcase
        end

    always @(*) begin
        for(i=0;i<4;i=i+1) begin
            cache_w[i] = cache_r[i];
            tag_w[i] = tag_r[i];
            lru_w[i] = lru_r[i];
        end
        case(state_r)
            READY: begin
                if(hit1) begin
                    tag_w[index] = tag_r[index];
                    lru_w[index] = 1'b0;
                    if(i_proc_wen) cache_w[index][63:32] = i_proc_wdata;
                    else cache_w[index][63:32] = cache_r[index][63:32];
                end
                else if(hit0) begin
                    tag_w[index] = tag_r[index];
                    lru_w[index] = 1'b1;
                    if(i_proc_wen) cache_w[index][31:0] = i_proc_wdata;
                    else cache_w[index][31:0] = cache_r[index][31:0];
                end
            end
            MISS: begin
                if(~i_mem_stall) begin
                    if(lru) begin
                        lru_w[index] = lru_r[index];
                        cache_w[index][63:32] = i_mem_rdata;
                        tag_w[index][55:28] = proc_addr[29:2];
                    end
                    else begin
                        lru_w[index] = lru_r[index];
                        cache_w[index][31:0] = i_mem_rdata;
                        tag_w[index][27:0] = proc_addr[29:2];
                    end
                end
            end
            WRITE: begin
                if(~i_mem_stall) begin
                    if(lru) begin
                        lru_w[index] = lru_r[index];
                        cache_w[index][63:32] = i_proc_wdata;
                        tag_w[index][55:28] = proc_addr[29:2];
                    end
                    else begin
                        lru_w[index] = lru_r[index];
                        cache_w[index][31:0] = i_proc_wdata;
                        tag_w[index][27:0] = proc_addr[29:2];
                    end
                end
            end
        endcase
    end
    
    //==== sequential circuit =================================
    always@( posedge i_clk ) begin
        if( !i_rst_n ) begin
            state_r <= READY;
            mem_write_r <= 1'b0;
            mem_addr_r <= 32'b0;
            mem_wdata_r <= 32'b0;
            for(i=0;i<4;i=i+1) begin
                cache_r[i] <= 64'b0;
                tag_r[i] <= 56'hff_ffff_ffff_ffff;
                lru_r[i] <= 1'b0;
            end
        end
        else begin
            state_r <= state_w;
            mem_write_r <= mem_write_w;
            mem_addr_r <= mem_addr_w;
            mem_wdata_r <= mem_wdata_w;
            for(i=0;i<4;i=i+1) begin
                cache_r[i] <= cache_w[i];
                tag_r[i] <= tag_w[i];
                lru_r[i] <= lru_w[i];
            end
        end
    end

endmodule