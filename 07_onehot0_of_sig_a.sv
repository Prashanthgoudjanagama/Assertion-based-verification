

// top_module : 07_onehot0_of_sig_a.sv
// module : onehot0_of_sig_a


module onehot0_of_sig_a;
    bit clk, rst;
    int sig_A;
    
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
    
    property prop_detect_A();
        @(posedge clk) disable iff(!rst)
        $onehot0(sig_A);
    endproperty : prop_detect_A
    
    assert property(prop_detect_A())
        $display("%0t ::: prop_detect_A :----------------> PASSED", $time);
    else
        $error("%0t  ::: prop_detect_A :------------------> FAILED", $time);
    
    
    initial begin
        # 150 $finish;
    end

endmodule : onehot0_of_sig_a