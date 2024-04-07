`timescale 1ns / 1ps

/////////////////////////////////////////////////////////////////////////////////

module dpi_test;
        import "DPI-C" function int  myCFunc1();
        import "DPI-C" function int  myCFunc2( input int A, output int B );
        import "DPI-C" function real mySin( input real C);
        import "DPI-C" function real myCos( input real C);
        import "DPI-C" function real myTan( input real C);
        
        import "DPI-C" function void system_init();
        import "DPI-C" function void get_nums(output logic [15:0] a[10]);
        
        logic [15:0] nums [10];
//        int nums[10];
        
        logic signed [7:0] lgA;
        integer iA, iB, iC;
        shortreal fF;
        real dD, dE;
        
//        initial begin
//            $display("[%0t] Call C methods", $time);
//            iA = myCFunc1();
//            $display("funct_1 : %d", iA);
            
//            iC = myCFunc2(iA, iB);
//            $display("funct_2 : %d %d %d", iA, iB, iC);
            
//            dD = 3.1415/2.0;
//            $display("%m sin : %f | cos : %f | tan : %f", mySin(dD), myCos(dD), myTan(dD));
                  
//            // my test
//            lgA = iA;
//            $display("A in bin : %b", lgA);
            
//            $finish;
//        end

        initial begin
            get_nums(nums);
            foreach(nums[i]) begin
                $display(i, nums[i]);
            end
            $finish;
        end
endmodule
