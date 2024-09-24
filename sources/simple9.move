module my_addrx::simple9 {
    use std::debug::print;
    struct Person has drop {
        age: u64,
    }

    public fun set_age(new_age: u64): u64 {
        let person = Person { age: new_age };
        return person.age
    }

    // #[test]
    fun test_set_age() {
         let age = set_age(100);
         assert!(age == 100, 100);
         print(&age);
    }
}