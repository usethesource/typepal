entity Employee  {
   boss -> Manager inverse Manager::subordinates
}

entity Manager {
   subordinates -> Set<Employee> inverse Employee::boss
}