module Test_Processor_module;
reg[31:0] instruction;
reg clk, rst;
wire[31:0] Output;

Processor_module test_case(rst, clk, instruction, Output);

initial
begin
$dumpvars(0, test_case);

rst = 0; clk = 1; instruction = 32'b000000_01010_01100_01110_00000_100000; #10
$display("\n 1st Test - add $10, $12, $14 \n Read register 1 is %d, Read data 1 is %d \n Read register 2 is %d, Read data 2 is %d \n Add result is %d \n Writen data in Register File: %d", test_case.Read_register1, test_case.Read_data1_, test_case.Read_register2, test_case.Read_data2_, Output, test_case.Mux_output);

rst = 0; clk = 1; instruction = 32'b000000_10010_10000_00011_11110_100010;#10
$display("\n 2nd Test - sub $18, $16, $3 \n Read register 1 is %d, Read data 1 is %d \n Read register 2 is %d, Read data 2 is %d \n Sub result is %d \n Writen data in Register File: %d", test_case.Read_register1, test_case.Read_data1_, test_case.Read_register2, test_case.Read_data2_, Output, test_case.Mux_output);

rst = 0; clk = 1; instruction = 32'b000000_01010_10010_10110_00000_100100;#10
$display("\n 3rd Test - and $10, $12, $24 \n Read register 1 is %d, Read data 1 is %b \n Read register 2 is %d, Read data 2 is %b \n And result is %b \n Writen data in Register File: %d", test_case.Read_register1, test_case.Read_data1_, test_case.Read_register2, test_case.Read_data2_, Output, test_case.Mux_output);

rst = 0; clk = 1; instruction = 32'b000000_01010_10010_10110_00000_100101;#10
$display("\n 4rd Test - or $10, $16, $24 \n Read register 1 is %d, Read data 1 is %b \n Read register 2 is %d, Read data 2 is %b \n Or result is %b \n Writen data in Register File: %d", test_case.Read_register1, test_case.Read_data1_, test_case.Read_register2, test_case.Read_data2_, Output, test_case.Mux_output);

rst = 0; clk = 1; instruction = 32'b000000_01010_10010_10110_00000_100100;#10
$display("\n 5fth Test - slt $10, $16, $0 \n Read register 1 is %d, Read data 1 is %b \n Read register 2 is %d, Read data 2 is %b \n Slt result is %b \n Writen data in Register File: %d", test_case.Read_register1, test_case.Read_data1_, test_case.Read_register2, test_case.Read_data2_, Output, test_case.Mux_output);

//--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
rst = 0; clk = 1; instruction = 32'b001000_01010_10010_00000_00000_000001;#10
$display("\n 6th Test - addi $10, $16 $0 \n Read register 1 is %d, Read data 1 is %b \n Read register 2 is %d, Read data 2 is %b \n Addi result is %b", test_case.Read_register1, test_case.Read_data1_, test_case.Read_register2, test_case.Read_data2_, Output);

rst = 0; clk = 1; instruction = 32'b101011_01010_10010_00000_00000_000001;#10
$display("\n 7th Test - sw $10, $16, $0 \n Read register 1 is %d, Read data 1 is %b \n Read imm[15:0] is %b, Read data imm is %b", test_case.Read_register1, test_case.Read_data1_, test_case.out_32bit, test_case.out_32bit);

rst = 0; clk = 1; instruction = 32'b100011_01010_10010_00000_00000_000001;#10
$display("\n 8th Test - lw $10, $16, $0 \n Read register 1 is %d, Data to be read in memory should be 5, Read address computed is %b \n Read data in memory is %b \n lw result is %b", test_case.Read_register1, test_case.mips_alu_out, test_case.memory_output, test_case.memory_output);


end
endmodule

module Processor_module(rst, clk, instruction, Output);

input[31:0] instruction;
output[31:0] Output;
input rst, clk;

wire RegWrite, RegDst,ALUSrc, Branch, MemWrite,MemRead, MemtoReg;
wire [3:0] AluCnt;
wire [1:0] AluOp;
wire [31:0] Output;

wire[4:0] Read_register1, Read_register2, mux2_input, Write_register;
wire[31:0] Write_data, Read_data1, Read_data2, Read_data1_, Read_data2_;
wire[5:0] funct, opcode;
wire[15:0] imm;
wire[31:0] memory_output, Mux_output, out_32bit, mips_alu_out, mux_aluSrc_out, out_shifted2;
wire Zero,Cin,Cout;

assign Read_register1 = instruction[25:21];
assign Read_register2 = instruction[20:16];
assign opcode = instruction[31:26];
assign imm = instruction[15:0];
assign funct = instruction[5:0];
assign mux2_input = instruction[15:11];
assign Output = mips_alu_out;
//assign rf_write_data = Mux_output;
assign Read_data1_ = 8;
assign Read_data2_ = 5;								


       Control_Unit_Block cnt_unit_block(instruction, RegWrite, RegDest, AluSrc, AluOp, AluCnt, Branch, MemWrite, MemRead, MemtoReg); 
       mux_1 mux_inst1(Read_register2, mux2_input, RegDest, Write_register);
       Register_file reg_file_inst(rst, clk, RegWrite,Write_register, Read_register1, Read_register2, Mux_output, Read_data1, Read_data2);
       sign_exten sign_ext_inst(imm, out_32bit);
       mux_2 mux2_inst(Read_data2_, out_32bit, AluSrc, mux_aluSrc_out);
       Alu alu_inst(Read_data1_, mux_aluSrc_out, AluCnt, mips_alu_out, Zero);
       Memory32 mem_inst(rst, clk, mips_alu_out, Read_data2_, memory_output, MemWrite, MemRead);
       mux_2 mux2_inst2(mips_alu_out, memory_output, MemtoReg, Mux_output);

      // shift_left2 shift_inst(out_32bit, out_shifted2);
      // CLA32 cla32(A, B, Cin, Sum, Cout);

endmodule

//Module Declarations

module Control_Unit_Block(instruction, RegWrite, RegDest, AluSrc, AluOp, AluCnt, Branch, MemWrite, MemRead, MemtoReg);
input [31:0] instruction;
output reg RegWrite, RegDest, AluSrc, Branch, MemWrite, MemRead, MemtoReg;
output reg [1:0] AluOp;
output reg [3:0] AluCnt;

wire[5:0] opcode, functions;
assign opcode = instruction[31:26];
assign functions = instruction[5:0];

always@(opcode or functions)
begin
//_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_//_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
   if(opcode == 6'b000000 && functions == 6'b100000) //add           //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/ 
    begin	                        	                     //_/_/_/_/_/ r type instructions /_/_/_/_/
    RegWrite <= 1'b1;						     //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    RegDest <= 1'b1;                                                  //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    AluSrc <= 1'b0;                                                   //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    Branch <= 1'b0;                                                   //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    MemWrite <= 1'b0;                                                 //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    MemRead <= 1'b0;                                                  //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    MemtoReg <= 1'b0;                                                 //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    AluOp <= 2'b10;                                                   //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    AluCnt <= 4'b0010;                                                //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    end
   else if(opcode == 6'b000000 && functions == 6'b100010) //sub 
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b1;
    AluSrc <= 1'b0;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b10;
    AluCnt <= 4'b0110;
    end
   else if(opcode == 6'b000000 && functions == 6'b100100) //and
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b1;
    AluSrc <= 1'b0;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b10;
    AluCnt <= 4'b0000;
    end
   else if(opcode == 6'b000000 && functions == 6'b100101) //or 
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b1;
    AluSrc <= 1'b0;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b10;
    AluCnt <= 4'b0001;
    end
   else if(opcode == 6'b000000 && functions == 6'b100111) //nor 
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b1;
    AluSrc <= 1'b0;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b10;
    AluCnt <= 4'b1100;
    end
   else if(opcode == 6'b000000 && functions == 6'b101010) //slt
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b1;
    AluSrc <= 1'b0;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b10;
    AluCnt <= 4'b0111;
    end 
//_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_//_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
   else if(opcode == 6'b001000 ) //addi                              //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/ 
    begin	                        	                     //_/_/_/_/_/ i type instructions /_/_/_/_/
    RegWrite <= 1'b1;						     //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    RegDest <= 1'b0;						     //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    AluSrc <= 1'b1;						     //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    Branch <= 1'b0;					             //_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/_/
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b00;
    AluCnt <= 4'b0010;
    end
   else if(opcode == 6'b001100) //andi
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b1;
    AluSrc <= 1'b0;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'b0;
    AluOp <= 2'b00;
    AluCnt <= 4'b0010;
    end
   else if(opcode == 6'b000100) //beq
    begin
    RegWrite <= 1'b0;
    RegDest <= 1'bx;
    AluSrc <= 1'b0;
    Branch <= 1'b1;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'bx;
    AluOp <= 2'b01;
    AluCnt <= 4'b0110;
    end
   else if(opcode == 6'b000101) //bne
    begin
    RegWrite <= 1'b0;
    RegDest <= 1'bx;
    AluSrc <= 1'b0;
    Branch <= 1'b1;
    MemWrite <= 1'b0;
    MemRead <= 1'b0;
    MemtoReg <= 1'bx;
    AluOp <= 2'b01;
    AluCnt <= 4'b0110;
    end
   else if(opcode == 6'b100011) //lw
    begin
    RegWrite <= 1'b1;
    RegDest <= 1'b0;
    AluSrc <= 1'b1;
    Branch <= 1'b0;
    MemWrite <= 1'b0;
    MemRead <= 1'b1;
    MemtoReg <= 1'b1;
    AluOp <= 2'b00;
    AluCnt <= 4'b0010;
    end
   else if(opcode == 6'b101011) //sw
    begin
    RegWrite <= 1'b0;
    RegDest <= 1'bx;
    AluSrc <= 1'b1;
    Branch <= 1'b0;
    MemWrite <= 1'b1;
    MemRead <= 1'b0;
    MemtoReg <= 1'bx;
    AluOp <= 2'b00;
    AluCnt <= 4'b0010;
    end
end
endmodule

module Register_file(rst, clk, RegWrite, wr_reg, rd_reg1, rd_reg2, wr_Data, Out1, Out2);
input [4:0] wr_reg, rd_reg1, rd_reg2;
input [31:0] wr_Data;
input RegWrite, rst, clk;
output [31:0] Out1, Out2; 
reg [31:0] regFile[31:0];
integer i;

assign  Out1 = regFile[rd_reg1];
assign  Out2 = regFile[rd_reg2];
 
always @(*)
  begin
   if(!rst)
    begin
     if(RegWrite)
	regFile[wr_reg] <= wr_Data;
     else
       begin
	for(i = 0; i < 32; i = i + 1)
	  begin
	    regFile[i] <= 32'h0;
          end
       end
     end
  end
endmodule

module sign_exten (in_16bit, out_32bit);
  input [15:0] in_16bit;
  output [31:0] out_32bit;

 assign  out_32bit[31:0] = { {16{in_16bit[15]}},{in_16bit} };

endmodule
/*module shift_left2 (ins_sign_extended, out_shifted);
  input [31:0] ins_sign_extended;
  output [31:0] out_shifted;

  assign  out_shifted[31:0] = ins_sign_extended << 2;

endmodule*/

module Alu(A, B, AluCnt, OUT, Zero);
input signed [31:0] A, B;
input [3:0] AluCnt;
output signed [31:0] OUT;
output Zero;
reg signed [31:0] OUT;

assign Zero = (OUT == 0);

always @(*)
	begin
	case (AluCnt)
		0: OUT = A & B; //and
		1: OUT = A | B; //or
		2: OUT = A + B; //add
		6: OUT = A - B; //sub
		7: OUT = A < B ? 1 : 0; //slt
	       12: OUT = ~(A | B); //nor
		default: OUT = 0;
	endcase
	end
endmodule
module Memory32(rst, clk, address, wr_data, rd_data, memwr, memrd);
input [31:0] address; //10 bits since 2^10 = 1024
input [31:0] wr_data; //32 bit machine
output [31:0] rd_data; //32 bit machine
input rst, memwr, memrd, clk;
  
reg [31:0] register[1023:0];
reg [31:0] rd_data;
integer i;
  
 
  always @(*)
    begin
     if(!rst)
      begin
      if (memwr)
	begin
	register[address][7:0] <= wr_data[31:24];
	register[address][15:8] <= wr_data[23:16];
      	register[address][23:16] <= wr_data[15:8];
      	register[address][31:24] <= wr_data[7:0];
	end
      else
	begin
	  rd_data[31:24] <= register[address][7:0];
          rd_data[23:16] <= register[address][15:8];
          rd_data[15:8] <= register[address][23:16];
          rd_data[7:0] <= register[address][31:24];
	end
      end
    else
     begin
	for(i = 0; i < 32; i = i+1)
         begin
	   register[i] <= 32'hx;
	 end
      end
    end
endmodule

module mux_1(A, B, Sel, OUT);//mux_10_5
input[4:0] A, B;
input Sel;
output[4:0] OUT;
reg[4:0] OUT;

always @(*)
	begin
	  if(Sel == 1'b0)
	    OUT <= A;
	  else
	    OUT <= B;
	end
endmodule

module mux_2(A, B, Sel, OUT);//mux32_16
input[31:0] A, B;
input Sel;
output[31:0] OUT;
reg[31:0] OUT;

always @(*)
	begin
	  if(Sel == 1'b0)
	    OUT <= A;
	  else
	    OUT <= B;
	end
endmodule

/*module CLA32(A, B, Cin, Sum, Cout);
parameter N = 32;
input [N-1:0] A, B;
input Cin;
output [N-1:0] Sum;
output Cout;

wire [N-1:0] P, G;
wire [N:0] c;
assign c[0] = Cin;
genvar i;

for(i = 0; i < N; i = i+1)
  begin
   assign P[i] = A[i]^B[i];
   assign G[i] = A[i]&B[i];
  end

for(i = 1; i < N+1; i = i+1)
 begin
   assign c[i] = G[i-1] | (P[i-1]&c[i-1]);
 end

for(i = 0; i < N; i = i+1)
 begin
   assign Sum[i] = P[i]^c[i];
 end

assign Cout = c[N];

endmodule*/
