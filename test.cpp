#include <iostream>
#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <cmath>


namespace my {
using namespace llvm;


unsigned int parts(const fltSemantics &sem)
{
    unsigned int bits = APFloatBase::semanticsPrecision(sem) + 1;
    return ((bits) + APFloatBase::integerPartWidth - 1) / APFloatBase::integerPartWidth;
}

void msb_test() {
    typedef unsigned int long uint;

    uint x = 4;
    uint y = 128;
    uint v[2] = {x,y};
    uint c = APInt::tcMSB(v,2);
    std::cout << "msb is " << c << std::endl;
}

double add(double x, double y, APFloatBase::roundingMode md) {
    detail::IEEEFloat a(x);
    detail::IEEEFloat b(y);
    a.add(b, md);
    return a.convertToDouble();
}


void test() {

    std::cout << "rmNearestTiesToEven:" << add(3.5, 4.2, APFloatBase::rmNearestTiesToEven) << std::endl
              << "rmTowardPositive   :" << add(3.5, 4.2, APFloatBase::rmTowardPositive) << std::endl
              << "rmTowardNegative   :" << add(3.5, 4.2, APFloatBase::rmTowardNegative) << std::endl
              << "rmTowardZero       :" << add(3.5, 4.2, APFloatBase::rmTowardZero) << std::endl
              << "rmNearestTiesToAway:" << add(3.5, 4.2, APFloatBase::rmNearestTiesToAway) << std::endl;

    std::cout << "weird const is " << APInt::APINT_BITS_PER_WORD << std::endl;
    std::cout << "parts for: \n"
              << " half: "   << parts(APFloatBase::IEEEhalf()) << std::endl
              << " single: " << parts(APFloatBase::IEEEsingle()) << std::endl
              << " double: " << parts(APFloatBase::IEEEdouble()) << std::endl
              << " quad: "   << parts(APFloatBase::IEEEquad()) << std::endl
              << " ppc: "    << parts(APFloatBase::PPCDoubleDouble()) << std::endl
              << " x87: "    << parts(APFloatBase::x87DoubleExtended()) << std::endl;

    std::cout << "is normal 4.2 " << (detail::IEEEFloat(4.2)).isNormal() << std::endl;
    std::cout << "is normal 0.2 " << (detail::IEEEFloat(0.2)).isNormal() << std::endl;

    detail::IEEEFloat a(APFloatBase::IEEEdouble(), 419430);
    detail::IEEEFloat b(0.2);
    a.add(b, APFloatBase::rmTowardPositive);
    std::cout << "a " << a.convertToDouble() << std::endl;
}


} //namespace my

int main() {

    my::test();
    return 0;

}
