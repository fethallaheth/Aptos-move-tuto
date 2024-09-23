module my_addrx::simple5 {
    use std::debug::print;
    use std::string::{utf8, String};

    fun sample_aport_error(num: u64) {
         if(num == 10) 
            //write code here if condition match
            print(&utf8(b"Correct"))
          else 
            abort 123    
    }
    fun sample_assert_error(num: u64) {
         assert!(num == 10, 123);
         print(&utf8(b"Correct"));
    }

    // //    #[test]
    // #[expected_failure]
    // fun test_function() {
    //     sample_aport_error(9);
    // }
    // //   #[test]
    
    // fun test_assert_function() {
    //     sample_aport_error(10);
    // }
}