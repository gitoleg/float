#include <iostream>
#include <fstream>
#include <sstream>
#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <cmath>
#include <math.h>

namespace my {
using namespace llvm;

unsigned int parts(const fltSemantics &sem)
{
    unsigned int bits = APFloatBase::semanticsPrecision(sem) + 1;
    return ((bits) + APFloatBase::integerPartWidth - 1) / APFloatBase::integerPartWidth;
}

double add(double x, double y, APFloatBase::roundingMode md) {
    detail::IEEEFloat a(x);
    detail::IEEEFloat b(y);
    a.add(b, md);
    return a.convertToDouble();
}

double sub(double x, double y, APFloatBase::roundingMode md) {
    detail::IEEEFloat a(x);
    detail::IEEEFloat b(y);
    a.subtract(b, md);
    return a.convertToDouble();
}

double mul(double x, double y, APFloatBase::roundingMode md) {
    detail::IEEEFloat a(x);
    detail::IEEEFloat b(y);
    a.multiply(b, md);
    return a.convertToDouble();
}

double my_sqrt(double x) {
    APFloatBase::roundingMode rm = APFloatBase::rmNearestTiesToEven;
    detail::IEEEFloat src(x);
    detail::IEEEFloat two(2.0);
    detail::IEEEFloat xm(x / 2.0);
    detail::IEEEFloat tmp(x);

    for (std::size_t i = 0; i < 25; ++i) {
        tmp.divide(xm, rm);
        xm.add(tmp, rm);
        xm.divide(two, rm);
        tmp = src;
    }
    return xm.convertToDouble();
}

std::string int64_to_bits(uint64_t x) {
    APInt y(64, x);
    return y.toString(2, false);
}

int fact(int x) {
    int res = 1;
    while (x != 0) {
        res = res * x;
        x -= 1;
    }
    return res;
}

detail::IEEEFloat pow(const detail::IEEEFloat &x, std::size_t n) {
    if (n == 0) return detail::IEEEFloat(double(1.0));
    else {
        detail::IEEEFloat res(x);
        for (std::size_t i = 1; i < n; ++i) {
            res.multiply(x, APFloatBase::rmNearestTiesToEven);
        }
        return res;
    }
}

typedef detail::IEEEFloat apf;

void mysin(double a) {
    apf arg(a);
    apf res(double(0.0));
    for (std::size_t i = 0; i < 10; ++i) {
        apf s = pow(apf(double(-1.0)), i);
        apf f((double)fact(2 * i + 1));
        apf x = pow(arg, 2 * i + 1);
        s.divide(f,APFloatBase::rmNearestTiesToEven);
        s.multiply(x, APFloatBase::rmNearestTiesToEven);
        res.add(s, APFloatBase::rmNearestTiesToEven);

        APInt n = res.bitcastToAPInt();
        std::string r = n.toString(2, false);
        std::cout << i << ", bits: " << r << std::endl;
    }


    std::cout << " res " << res.convertToDouble() << std::endl;

    // APInt i = res.bitcastToAPInt();
    // std::string s = i.toString(2, false);
    // std::cout << "bits: " << s << std::endl;
}


void test() {

    apf a(APFloatBase::IEEEdouble(),  APInt(64, 4653933137958313667L));
    apf b(APFloatBase::IEEEdouble(), APInt(64, 4660200489909900540L));
    a.subtract(b, APFloatBase::rmNearestTiesToEven);
    APInt i = a.bitcastToAPInt();
    std::string s = i.toString(2, false);
    std::cout << "bits: " << s << std::endl;
    std::cout << std::boolalpha << "res " << a.convertToDouble() << std::endl;

}

using namespace llvm;
using namespace llvm::detail;

void test16 () {
    std::size_t max = 20;

    std::ofstream f("my.out");

    std::stringstream s;

    uint64_t op1 = 0;
    uint64_t op2 = 0;
    uint64_t r = 0;
    for (std::size_t i = 0; i < max; ++i) {
        for (std::size_t j = 0; j < max; ++j) {
            IEEEFloat a(APFloatBase::IEEEhalf(), APInt(16, i));
            IEEEFloat b(APFloatBase::IEEEhalf(), APInt(16, j));
            op1 = *a.bitcastToAPInt().getRawData();
            op2 = *b.bitcastToAPInt().getRawData();

            a.add(b, APFloatBase::rmNearestTiesToEven);
            r = *a.bitcastToAPInt().getRawData();
            s << op1 << " " << op2 << " " << r << std::endl;
            // f << s.str();
            std::cout << i << " " << j << " " << s.str() ;

            s.clear();
        }
    }
    f.close();

}

} //namespace my

int main() {
//    my::test16();
    my::test();
    return 0;
}
