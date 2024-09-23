address my_addrx {

    module one {
        
        friend my_addrx::two;
        friend my_addrx::three;


        public(friend) fun get_value(): u64 {
            return 100
        }

        #[view]
        public fun get_prices(): u64 {
            return 90
        }
    }

    module two { 
        use my_addrx::one::get_value;
        use std::debug;
    
        // #[test]
        fun test_function() {
            let result = get_value();
            debug::print(&result);

        }        

    }

    module three {
           use my_addrx::one::get_value;
           use std::debug;
    
        //  #[test]
        fun test_function() {
            let result = get_value();
            debug::print(&result);

        }       
    }
}