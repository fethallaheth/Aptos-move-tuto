module my_addrx::silenceCompany {
    use std::vector;
    friend my_addrx::simple12;
   
    public(friend) fun get_company_name() : vector<u8> {
        return b"silence company"
    }
}

script {
    use my_addrx::simple12;
    use std::debug;
    fun do_stuff() {
        let info = simple12::get_info();
        debug::print(&info);
    }
}


module my_addrx::simple12 {
    use std::vector;
    use std::debug::print;

    const CONTACT:address = @0x42; 

    struct Employees has store, key, drop , copy {
        people : vector<Employee>
    }

    struct Employee has store, key, drop , copy {
        name: vector<u8>,
        age: u8,
        income: u64,
    }

    struct Info has store, key, drop , copy {
        company_name: vector<u8>,
        owns: vector<u8>,
    }
    
    public fun get_info() : Info {
        let silenceCompanyName = my_addrx::silenceCompany::get_company_name();        let info = Info {
            company_name: b"chaos company",
            owns: silenceCompanyName,
        };
        return info
    }



    public fun create_employee(_employee: Employee, _employees: &mut Employees) : Employee {
        let newEmployee = Employee {
            name: _employee.name,
            age: _employee.age,
            income: _employee.income,
        };
        add_employee(_employees ,newEmployee);
        return newEmployee
    }

    fun add_employee(_employees: &mut Employees ,_employee: Employee) {
         vector::push_back(&mut _employees.people, _employee);
    }

    public fun increase_income(employee: &mut Employee, bonus: u64): &mut Employee {
          employee.income = employee.income + bonus;
          return employee
    }

    public fun decrease_income(employee: &mut Employee, penality: u64): &mut Employee {
          employee.income = employee.income - penality;
          return employee
    }

     public fun multiply_income(employee: &mut Employee, factor: u64): &mut Employee {
          employee.income = employee.income * factor;
          return employee
    }

    public fun div_income(employee: &mut Employee, divisor : u64): &mut Employee {
          employee.income = employee.income / divisor;
          return employee
    }

    public fun is_employee_age_even(employee: &Employee): bool {
        let isEven : bool ;
        if (employee.age % 2 == 0) {
            isEven = true
        } else {
            isEven = false
        };
        return isEven
    }
    

    // #[test]
    fun test_Friend_func() {
        let comp = get_info();
        let comp_name = comp.owns;
        print(&comp_name);
    }
    
    
}