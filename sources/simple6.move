module my_addrx::simple6 {
    use std::debug::print;

    const ADD: u64 = 1;   
    const SUB: u64 = 2;   
    const MUL: u64 = 3;   
    const DIV: u64 = 4;   
    const MOD: u64 = 5;   

    fun arthemictic_op(a: u64, b: u64, operator: u64): u64 {
        if (operator == ADD) 
            return a + b 
        else if (operator == SUB)
            return a - b
        else if (operator == MUL)
            return a * b 
        else if (operator == DIV)
            return a / b 
        else 
            return a % b
    }

    const HIGHER : u64 = 1;
    const LOWER : u64 = 2;
    const HIGHER_EQ : u64 = 3;
    const LOWER_EQ : u64 = 4;
    const EQUAL : u64 = 5;
    

     fun equality_op(a: u64, b: u64, operator: u64): bool {
        if (operator == HIGHER) 
            return a > b
        else if (operator == LOWER)
            return a < b
        else if (operator == HIGHER_EQ)
            return a >= b 
        else 
            return a <= b 
        
    }
    
    // #[test]
    fun test_Op_funtion(){
        let result = equality_op(10, 2, 1);
        print(&result);

        let result = equality_op(10, 2, 2);
        print(&result);

        let result = equality_op(10, 2, 3);
        print(&result);
        
        let result = equality_op(10, 2, 4);
        print(&result)
    }

    //   #[test]
    fun test_funtion(){
        let result = arthemictic_op(10, 2, 1);
        print(&result);

        let result = arthemictic_op(10, 2, SUB);
        print(&result);

        let result = arthemictic_op(10, 2, MUL);
        print(&result);
        
        let result = arthemictic_op(10, 2, DIV);
        print(&result);

        let result = arthemictic_op(11, 2, 7);
        print(&result)
    }
}