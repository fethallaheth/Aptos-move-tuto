module my_addrx::Simple1 {
   use std::debug;
   use std::string::{String, utf8};

   const ID: u64 = 100;

   

   fun set_val(): u64 {
    let num = 100_u8;
    let string : String = utf8(b"Hello move");

    debug::print(&num);
    debug::print(&string);
    ID
   }

   //#[test]
   fun test_function() {
    let id_value = set_val();
    debug::print(&id_value);
   }
}