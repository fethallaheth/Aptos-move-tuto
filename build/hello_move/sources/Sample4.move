module my_addrx::Sample4 {
    use std::debug;

    fun simple_for_loop(count: u64): u64 {
        let result = 0;
        for (i in 0..count){
            result = result + i;
        };
        return result 
    }
    
    fun simple_while_loop(count: u64): u64 {
        let result = 0;
        let i = 1;
        while (i <= count) {
            result = result + 1;
            i = i + 1;
        };
        result
    }

    // #[test]
    fun test_function() {
        let result = simple_for_loop(10);
        debug::print(&result);
    }

    // #[test]
    fun test_while_function() {
        let result = simple_while_loop(10);
        debug::print(&result);
    }
}