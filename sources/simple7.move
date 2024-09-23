module my_addrx::Simple7 {
    use std::debug::print;    
    /* 
     / or - if either binary value is 1, retutn 1, else return 0
     & and -  if the two binary values are 1, return 1, else return 0
     ^ xor -  if binary values are diff return 1, else return 0
    
    8 4 2 1 
    1 0 0 1 = 9 
    
    */
    fun bitwise_or(a: u64, b: u64): u64 {
        return a | b
    }

    fun bitwise_and(a: u64, b: u64): u64 {
        return a & b
    }

    fun bitwise_xor(a: u64, b: u64): u64 {
        return a ^ b
    }


    //    #[test]
    fun test_(){
        let or = bitwise_or(7, 4);
        print(&or);
        
        let and = bitwise_and(7, 4);
        print(&and);

        let xor = bitwise_xor(7, 4);
        print(&xor);
    }


    /*
      BITSHIFT 
    to the right 7 >> 2 = 1 
    to the right 9 >> 1 = 4

    to the left 7 << 2 = 28
    to the left 9 << 1 == 18

    16 8 4 2 1 
       0 1 1 1 == 7 
    1  1 1 0 0 == 28
    1  0 0 1 0 == 18

    */

    fun bitshift_right(a: u64, b: u8): u64 {
        return a >> b
    }

      fun bitshift_left(a: u64, b: u8): u64 {
        return a << b
    }


    // #[test]
    fun test_bitShift() {
        let right = bitshift_right(7, 2);
        print(&right);

        let left = bitshift_left(7, 2);
        print(&left);
    }
}