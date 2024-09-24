module my_addrx::Generics {
    use std::debug;
    
    struct Flexy<AnyType> has drop, copy, store {
        x: AnyType,
    }

    fun new_flexi(_x: u8): Flexy<u8> {
        return Flexy {
            x: _x,
        }
    }

    #[test]
    fun test_flex() {

        let f = new_flexi(10);
        debug::print(&f);
    
}
}