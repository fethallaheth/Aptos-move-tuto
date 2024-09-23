address my_addrx {

    module PriceOracle {
        public fun get_price(): u128 {
            return 54200
        }
    }

    module Casting {
        use my_addrx::PriceOracle;
        use std::debug::print;

        fun calc_swap() : u64 {
            let price = PriceOracle::get_price();
            let fee: u64 = 100;
            let price_with_fee : u64 = (price as u64) + fee;
            return price_with_fee
        }

        #[test]
        fun test_calc_swap(){
            let price_with_fee = calc_swap();
            print(&price_with_fee);
        }
    }
}