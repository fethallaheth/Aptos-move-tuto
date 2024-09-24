module my_addrx::Tuples {
    use std::vector;
    use std::debug;

    fun lots_of_things() : ( u64, vector<u8>, bool) {
       let x  = 0;
       let name = b"hello";
       let trunchy = true;
        
        (x, name, trunchy) 
    }

    #[test]
    fun test_lots_of_things() {
        let (x, name, trunchy) = lots_of_things();
        debug::print(&x);
        debug::print(&name);
        debug::print(&trunchy);
    }
}