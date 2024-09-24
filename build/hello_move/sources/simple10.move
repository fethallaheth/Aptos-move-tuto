module my_addrx::simple10 {
    use std::debug::print;
    use std::vector;

    struct Friends has store, key, drop {
         people : vector<Person>    
    }

    
    struct Person has store, key, drop , copy{
        name: vector<u8>,
        age: u64,
    }
    

    public fun create_friend(myFriend: Person, friends: &mut Friends): Person {
         let newFriend = Person { 
            name: myFriend.name,
            age: myFriend.age,
         };
        add_friend(newFriend, friends);
        return newFriend
    }

    public fun add_friend(_person: Person, friends: &mut Friends) {
        vector::push_back(&mut friends.people, _person)
    }


    #[test]
    fun test_create_friend() {
        let chaos = Person {
            name: b"chaos",
            age: 21,
        };

        let friends = Friends {
            people : (vector[chaos])
        };
        
        let createFriend = create_friend(chaos, &mut friends);

        assert!(createFriend.name == b"chaos" , 0);
    }
}