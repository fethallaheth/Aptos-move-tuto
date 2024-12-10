module my_addrx::Simple2 {
    
    const MY_ADDR: address = @my_addrx;
    
    fun confirm_value(choice: bool): (u64, bool) {
        if(choice) {
            //write code here if condition match
            return (1, choice);
        } else {
            return (0, choice);
        }
    }


    #[test_only]
    use std::debug::print;
    
    // #[test]
    fun test_function() {
        // print(&MY_ADDR)
        let (num, boolean)  = confirm_value(true);  
        print(&num);
        print(&boolean);
        }
}