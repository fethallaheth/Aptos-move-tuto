module my_addrx::simple11 {
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
    fun test_create_employee() {
        let chaos = Employee {
            name: b"chaos",
            age: 21,
            income: 2000,
        };
        let employees = Employees {
            people : (vector[chaos])
        };
        let createdEmployee = create_employee(chaos, &mut employees);
        assert!(createdEmployee.name == b"chaos", 0);
        assert!(createdEmployee.age == 21, 0);
        assert!(createdEmployee.income == 2000, 0)
    }

    // #[test]
    fun test_increase_income() {
        let chaos = Employee {
            name: b"chaos",
            age: 21,
            income: 2000,
        };

        let employees = Employees {
            people : (vector[chaos])
        };

        let createdEmployee = create_employee(chaos, &mut employees);
        let increasedEmp = increase_income(&mut createdEmployee, 200);
        assert!(increasedEmp.income == 2200, 0)
    }
    // #[test]
    fun test_decrease_income() {
        let chaos = Employee {
            name: b"chaos",
            age: 21,
            income: 2000,
        };

        let employees = Employees {
            people : (vector[chaos])
        };

        let createdEmployee = create_employee(chaos, &mut employees);
        let decreasedEmp = decrease_income(&mut createdEmployee, 50);
        print(&decreasedEmp.income);
        assert!(decreasedEmp.income == 1950 , 0)
    }

    
}