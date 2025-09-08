

// top_module : 05_isunknown_of_sig_a.sv
// module : isunknown_of_sig_a


module isunknown_of_sig_a;
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
        sig_A = 1'bx;
        #10;
        sig_A = 1'bz;
        #10;
        sig_A = 0;
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
        # 150 $finish;
    end

endmodule : isunknown_of_sig_a