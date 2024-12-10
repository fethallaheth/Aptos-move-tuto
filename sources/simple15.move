module my_addrx::MathModule {
    use std::debug;
    // A simple generic function that returns its input (identity function)
    public fun identity<T>(x: T): T {
        x
    }
    
    #[test]
    fun test_identity() {
        let a = Self::identity(5); // `a` is inferred to be of type u64
        let b = Self::identity(true); // `b` is inferred to be of type bool
        debug::print<u64>(&a);
        debug::print<bool>(&b) ;
        
    }
}
