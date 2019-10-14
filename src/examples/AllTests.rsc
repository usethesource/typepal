module examples::AllTests

import examples::aliases::Test;
import examples::calc::Test;
import examples::extending::Test;
import examples::fixedMembers::Test;
import examples::fun::Test;
import examples::fwjava::Test;
import examples::modfun::Test;
import examples::pascal::Test;
import examples::pico::Test;
import examples::ql::Test;
import examples::smallOO::Test;
import examples::staticFields::Test;
import examples::struct::Test;
import examples::structParameters::Test;
import examples::untypedFun::Test;

bool allTests(){
    return  
           aliasesTests()
        && calcTests()
        && extendingTests()
        
        && fixedMembersTests()
        && funTests()
        && fwjTests()
        && modfunTests()
        && pascalTests()
        && picoTests()
        && qlTests()
        && smallOOTests()
        && staticFieldsTests()
        && structTests()
        && structParametersTests()
        && untypedFunTests()
        ;
}

test bool allTests1() = allTests();

bool main() = allTests();