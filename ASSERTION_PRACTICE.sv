/////////////////////////////////////ASSERTIONS_PRACTICE///////////////////////////////////////////////////////

//----------------- Q1. Assertion to Detect the posedge of a sig_A ($rose) ?




//--------------------------------------------------------------------------------
//----------------- Q2. Assertion to Detect the negedge of a sig_A ($fell) ?


module detect_A;
  bit clk, rst;
  bit sig_A;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    sig_A = 1;
    repeat(10) begin
      sig_A = $random;
      #10;
    end
  end
  
  property prop_detect_A();
    @(posedge clk) disable iff(!rst)
    $fell(sig_A);
  endproperty : prop_detect_A
  
  assert property(prop_detect_A())
    $display("%0t ::: prop_detect_A :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop_detect_A :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : detect_A



//--------------------------------------------------------------------------------
//----------------- Q3. Assertion to Detect a sig_A is stable ($stable) ?

module detect_A;
  bit clk, rst;
  bit sig_A;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    sig_A = 1;
    repeat(10) begin
      sig_A = $random;
      #10;
    end
  end
  
  property prop_detect_A();
    @(posedge clk) disable iff(!rst)
    $stable(sig_A);
  endproperty : prop_detect_A
  
  assert property(prop_detect_A())
    $display("%0t ::: prop_detect_A :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop_detect_A :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : detect_A



//--------------------------------------------------------------------------------
//----------------- Q4. Assertion to Detect a sig_A is changed ($changed) ?

module detect_A;
  bit clk, rst;
  bit sig_A;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    sig_A = 1;
    repeat(10) begin
      sig_A = $random;
      #10;
    end
  end
  
  property prop_detect_A();
    @(posedge clk) disable iff(!rst)
    $changed(sig_A);
  endproperty : prop_detect_A
  
  assert property(prop_detect_A())
    $display("%0t ::: prop_detect_A :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop_detect_A :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : detect_A




//--------------------------------------------------------------------------------------
//----------------- Q5. Write a Assertion to check A is high after two cycles B is high?


module a_2cycle_b;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(10) begin
      A = $random; 
      B = $random;
      #10;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    	A ##2 B;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : a_2cycle_b



//--------------------------------------------------------------------------------------
//----------------- Q6. Write a Assertion to check if A is high then only B is high ?

module same_cycle_impication;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(10) begin
      A = $random; 
      B = $random;
      #10;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    	A |-> B;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : same_cycle_impication



//-------------------------------------------------------------------------------------------------
//----------------- Q7. Write a Assertion to check if A is high then only after one cycle B is high ?

module Next_cycle_impication;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(10) begin
      A = $random; 
      B = $random;
      #10;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    	A |=> B;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : Next_cycle_impication



//----------------------------------------------------------------------------------------------------
//----------------- Q8. Write a Assertion to check if A is high then only B is high for [2:3] cycles (consecutive) ?

module consecutive_repetition;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A |-> B [*2:3];    // consecutive_repetition
//  A |-> B [=2:3];    // Non_consecutive_repetition
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : consecutive_repetition



//------------------------------------------------------------------------------------------------------
//----------------- Q9. Write a Assertion to check if A is high after [2:3] cycles B is high ?

module A_2_to_3_B;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A ##[2:3] B;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #50 $finish;
  end
  
endmodule : A_2_to_3_B



//------------------------------------------------------------------------------------------------------
//----------------- Q10. Write a Assertion if A is high, check signal B was high before 2 clock  ?

module past_before_2cycles;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A  |-> $past(B,2);
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #50 $finish;
  end
  
endmodule : past_before_2cycles



//------------------------------------------------------------------------------------------------------
//----------------- Q11. Write a Assertion for non_consecutive_repetition of B?


module Non_consecutive_repetition;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A |-> B [=2];  // Non_consecutive_repetition
    //  A |-> B [*2]; // consecutive_repetition
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #50 $finish;
  end
  
endmodule : Non_consecutive_repetition




//------------------------------------------------------------------------------------------------------
//----------------- Q12. Write a Assertion for non_consecutive_repetition_goto_operator of B?


module Non_consecutive_repetition_GOTO_operator;
  bit clk, rst;
  bit A, B, C;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    C = 1;
    repeat(20) begin
      A = $random; 
      B = $random;
      C = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A |-> B [->2] ##1 C;  // Non_consecutive_repetition_GOTO_operator
    //      A |-> B [=2] ##1 C;  // Non_consecutive_repetition
    //      A |-> B [*2] ##1 C; // consecutive_repetition
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : Non_consecutive_repetition_GOTO_operator



//------------------------------------------------------------------------------------------------------
//----------------- Q13. Write a Assertion to check the number of ones must be one in sig_A for each cycle?

module onehot_of_sigA;
  bit clk, rst;
  bit sig_A;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    repeat(2) @ (posedge clk);
    sig_A = 0;
    repeat(10) begin
      sig_A = $random;
      #10;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    $onehot(sig_A);
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : onehot_of_sigA



//------------------------------------------------------------------------------------------------------
//----------------- Q14. Write a Assertion to check the number of zeros must be one in sig_A for each cycle?

module onehot_of_sigA;
  bit clk, rst;
  bit sig_A;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    repeat(2) @ (posedge clk);
    sig_A = 0;
    repeat(10) begin
      sig_A = $random;
      #10;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    not ($onehot(sig_A));
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : onehot_of_sigA



//------------------------------------------------------------------------------------------------------
//----------------- Q15. Write a Assertion to check "A |-> B[*2:3]" this comb will not happen?

module not_keyword;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  sequence seq();
    A |-> B[*2:3];
  endsequence : seq
  
  property prop();
    @(posedge clk) disable iff(!rst)
    not seq;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #50 $finish;
  end
  
endmodule : not_keyword




//------------------------------------------------------------------------------------------
/*----------------- Q16. Write a Assertion to check A should be continuously till B goes low,
			 expects A to be high in the last cycle B goes low ?
*/

module throughout_keyword;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A  throughout B;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #50 $finish;
  end
  
endmodule : throughout_keyword



//------------------------------------------------------------------------------------------------------
/*--------- Q17. Write a Assertion to check When the positive edge of A is detected, 
                 after one cycle B to be high continuously until one cycle before C goes low ?    
*/

module until_keyword;
  bit clk, rst;
  bit A, B, C;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    C = 1;
    repeat(20) begin
      A = $random; 
      B = $random;
      C = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    $rose(A) |=> (B until C);
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : until_keyword



//------------------------------------------------------------------------------------------------------
/*----------- Q18. Write a Assertion to check When the positive edge of A is detected, 
                   at same cycle B to be high continuously until C goes low ?
*/

module until_with_keyword;
  bit clk, rst;
  bit A, B, C;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    C = 1;
    repeat(20) begin
      A = $random; 
      B = $random;
      C = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    $rose(A) |-> (B until_with C);
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : until_with_keyword



//------------------------------------------------------------------------------------------------------
/*----------------- Q19. Write a Assertion to check A happens within the start and completion of B. 
			 The starting matching point of B must happen before the starting matching point of A. 
			 The ending matching point of A must happen before the ending matching point of B ?
*/

module within_keyword;
  bit clk, rst;
  bit A, B;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #2 clk = ~clk;

  initial begin
    @ (posedge clk);
    A = 1;
    B = 0;
    repeat(20) begin
      A = $random; 
      B = $random;
      #4;
    end
  end
  
  property prop();
    @(posedge clk) disable iff(!rst)
    A within B;
  endproperty : prop
  
  assert property(prop())
    $display("%0t ::: prop :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : within_keyword




//------------------------------------------------------------------------------------------------------
//----------------- Q20. Write a Assertion to check for sig_A is unknown?

module detect_A;
  bit clk, rst;
  reg sig_A;
  
  initial begin
    clk = 0;
    rst = 0;
    @(posedge clk);
    rst = 1;
  end
  
  always #5 clk = ~clk;

  initial begin
    @ (posedge clk);
    sig_A = 1;
    repeat(10) begin
      sig_A = $random;
      #10;
      sig_A = 1'bx;
      #10;
    end
  end
  
  property prop_detect_A();
    @(posedge clk) disable iff(!rst)
    $isunknown(sig_A);
  endproperty : prop_detect_A
  
  assert property(prop_detect_A())
    $display("%0t ::: prop_detect_A :----------------> PASSED", $time);
  else
    $error("%0t  ::: prop_detect_A :------------------> FAILED", $time);
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #150 $finish;
  end
  
endmodule : detect_A



//------------------------------------------------------------------------------------------------------
//----------------- Q21. Write a Assertion to check the clock frequency must be 500MHZ ?


`timescale 1ns/1ns

module checker_for_500MHZ_clk;

  bit clk, rst;

  initial begin
    clk = 0;
    rst = 0;
    repeat(2) @(posedge clk);
    rst = 1;
  end

  always #1 clk = ~clk;

  time clk_period = 1000.0/500.0ns;

  property prop(int clk_period);
    realtime current_time;
	@(posedge clk) disable iff(!rst)
	  ('1,current_time = $realtime) |=> (clk_period == $realtime - current_time);
  endproperty : prop

  assert property(prop(clk_period))
    $display("ASSERTION PASSED : %Ot", $time);
  else
    $error("ASSERTION FAILED : %Ot",$time);

  initial begin
     $dumpfile("dump.vcd");
     $dumpvars;
     #100 $finish;
  end

endmodule : checker_for_500MHZ_clk
