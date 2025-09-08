


// file: 10_examples_Boolean_exp.sv
// top_module : 


/*
_______________________________________________

1. A ##2 B;
2. A ##[*2] B;   // consequtive repetition
3. A ##[=2] B;   // non-consequtive repetition
4. A ##[->2] B;  // go-to repetition
5. A ##[*2:3] B;
6. A ##[=2:3] B;
7. A ##[->2:3examples_Boolean_exp] B;
_______________________________________________

*/



module examples_Boolean_exp;
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
        repeat(100) begin
        A = $random; 
        B = $random;
        #10;
        end
    end
    
    property prop();
        @(posedge clk) disable iff(!rst)
            // A ##2 B;
            // A ##1 B[*2];   // consequtive repetition
            // A ##1 B[=2];   // non-consequtive repetition
             A ##1 B[->2];  // go-to repetition
            // A ##[*2:3] B;
            // A ##[=2:3] B;
            // A ##[->2:3] B;
    endproperty : prop
    
    assert property(prop())
        $display("%0t ::: prop :----------------> PASSED", $time);
    else
        $error("%0t  ::: prop :------------------> FAILED", $time);
    
    
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
        # 150 $finish;
    end
  
endmodule : examples_Boolean_exp
