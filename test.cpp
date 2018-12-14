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

enum lost {
  lfExactlyZero,
  lfLessThanHalf,
  lfExactlyHalf,
  lfMoreThanHalf
};

std::string string_of_lost(const lost &lf) {
    if (lf == lfExactlyZero)
        return "lfExactlyZero";
    else if (lf == lfLessThanHalf)
        return "lfLessThanHalf";
    else if (lf == lfExactlyHalf)
        return "lfExactlyHalf";
    else return "lfMoreThanHalf";
}


std::string int64_to_bits(uint64_t x) {
    APInt y(64, x);
    return y.toString(2, false);
}

lost combine_lost(lost moreSignificant,
                  lost lessSignificant) {
    if (lessSignificant != lfExactlyZero) {
        if (moreSignificant == lfExactlyZero)
            moreSignificant = lfLessThanHalf;
        else if (moreSignificant == lfExactlyHalf)
            moreSignificant = lfMoreThanHalf;
    }

    return moreSignificant;
}


struct My{

    My(double x) {
        APInt bits = APInt::doubleToBits(x);
        uint64_t i = *bits.getRawData();
        uint64_t myexponent = (i >> 52) & 0x7ff;
        uint64_t mysignificand = i & 0xfffffffffffffLL;

        expn = myexponent - 1023;
        significand = mysignificand | 0x10000000000000LL;
        sign = false;

        std::cout << "creation of " << x << "; expn is " << expn << std::endl;
        std::cout << "  " << int64_to_bits(significand) << std::endl;
    }

    APInt to_bits() {
        uint64_t myexponent = expn+1023;
        uint64_t mysignificand = significand;
        return APInt(64, ((((uint64_t)(sign & 1) << 63) |
                           ((myexponent & 0x7ff) <<  52) |
                           (mysignificand & 0xfffffffffffffLL))));

    }

    std::string to_bitstring() {
        APInt x = to_bits();
        return x.toString(2, false);
    }

    double to_double() {
        APInt x = to_bits();
        return x.bitsToDouble();

    }

    void norm(lost &lf) {
        unsigned int omsb = APInt::tcMSB(&significand, 1) + 1;
        int exponentChange = omsb - 53;

        std::cout << "exp change is " << exponentChange << std::endl;

        if (exponentChange < 0)
            lshift(-exponentChange);
        else if (exponentChange > 0) {
            lost lf1 = rshift(exponentChange);
            lf = combine_lost(lf, lf1);
            std::cout << "lost full " << string_of_lost(lf) << std::endl;

            if (omsb > (unsigned) exponentChange)
                omsb -= exponentChange;
            else
                omsb = 0;

            if (lf == lfMoreThanHalf)
                APInt::tcIncrement(&significand, 1);

        }
    }

    lost get_lost(unsigned int bits) {
        unsigned int lsb = APInt::tcLSB(&significand,1);
        if (bits <= lsb)
            return lfExactlyZero;
        if (bits == lsb + 1)
            return lfExactlyHalf;
        if (APInt::tcExtractBit(&significand, bits - 1))
            return lfMoreThanHalf;

        return lfLessThanHalf;
    }

    lost rshift(unsigned int bits) {
        lost x = get_lost(bits);
        APInt::tcShiftRight(&significand, 1, bits);
        expn += bits;
        return x;
    }

    void lshift(unsigned int bits) {
        APInt::tcShiftLeft(&significand, 1, bits);
        expn -= bits;
    }

    void sub(My &rhs) {
        bool reverse = false;
        lost lf = lfExactlyZero;
        std::cout << "exps: " << expn << " " << rhs.expn << std::endl;
        uint64_t bits = expn - rhs.expn;
        std::cout << "bits " << bits << std::endl;

        if (bits > 0) {
            std::cout << "case 1" << std::endl;
            lf = rhs.rshift(bits - 1);
            lshift(1);
            reverse = false;
        } else {
            std::cout << "case 2" << std::endl;
            lf = rshift(-bits - 1);
            rhs.lshift(1);
            reverse=true;
        }

        std::cout << "expn is " << expn << std::endl;

        if (lf == lfLessThanHalf)
            lf = lfMoreThanHalf;
        else if (lf == lfMoreThanHalf)
            lf = lfLessThanHalf;

        std::cout << "lost is " << string_of_lost(lf) << std::endl;

        if (reverse) {
            std::cout << "TODO 1" << std::endl;
        } {
            APInt::tcSubtract(&significand, &rhs.significand, !(lf == lfExactlyZero), 1);
            norm(lf);
        }
    }

private:
    uint64_t significand;
    int64_t expn;
    bool sign;
};


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

    apf a(APFloatBase::IEEEdouble(), APInt(64, 0xFFFFFFFFFFFFFL));
    apf b(APFloatBase::IEEEdouble(), APInt(64, 0x1L));
    a.add(b, APFloatBase::rmNearestTiesToEven);
    std::cout << std::boolalpha << "res " << a.isNormal() << std::endl;

    // apf a(APFloatBase::IEEEquad(), APInt(128, 4602688819172646912L));
    // apf b(APFloatBase::IEEEquad(), APInt(128, 2L));
    // a.divide(b, APFloatBase::rmNearestTiesToEven);
    // std::cout << std::boolalpha << "res " << a.isFiniteNonZero() << std::endl;
//    std::cout << "res is " << a.convertToDouble() << std::endl;

    // double cc = my_sqrt(bb);
    // double dd = sqrt(bb);
    // std::cout << "llvm res " << cc << ", correct is " << dd << std::endl;
    // std::cout << "rmNearestTiesToEven:" << add(3.5, 4.2, APFloatBase::rmNearestTiesToEven) << std::endl
    //           << "rmTowardPositive   :" << add(3.5, 4.2, APFloatBase::rmTowardPositive) << std::endl
    //           << "rmTowardNegative   :" << add(3.5, 4.2, APFloatBase::rmTowardNegative) << std::endl
    //           << "rmTowardZero       :" << add(3.5, 4.2, APFloatBase::rmTowardZero) << std::endl
    //           << "rmNearestTiesToAway:" << add(3.5, 4.2, APFloatBase::rmNearestTiesToAway) << std::endl;

    // std::cout << "weird const is " << APInt::APINT_BITS_PER_WORD << std::endl;
    // std::cout << "parts for: \n"
    //           << " half: "   << parts(APFloatBase::IEEEhalf()) << std::endl
    //           << " single: " << parts(APFloatBase::IEEEsingle()) << std::endl
    //           << " double: " << parts(APFloatBase::IEEEdouble()) << std::endl
    //           << " quad: "   << parts(APFloatBase::IEEEquad()) << std::endl
    //           << " ppc: "    << parts(APFloatBase::PPCDoubleDouble()) << std::endl
    //           << " x87: "    << parts(APFloatBase::x87DoubleExtended()) << std::endl;

    // std::cout << "is normal 4.2 " << (detail::IEEEFloat(4.2)).isNormal() << std::endl;
    // std::cout << "is normal 0.2 " << (detail::IEEEFloat(0.2)).isNormal() << std::endl;

    // to get zero from division
    // float x = 0.0000000000000000000000000000000000000021452525;
    // float y = 9911115.0;
    // to get inf from muliplication
    // float x = 231313123123131349294424.0;
    // float y = 9111112321833131.0;


    // double s1 = 0.01;
    // double s2 = 0.0002;

    // detail::IEEEFloat a(s1);
    // detail::IEEEFloat b(s2);
    // a.subtract(b, APFloatBase::rmNearestTiesToEven);
    // APInt i = a.bitcastToAPInt();
    // std::string s = i.toString(2, false);
    // std::cout << "ideals res " << a.convertToDouble() << std::endl;
    // std::cout << "ideals bits are " << s << std::endl;


    // My x(s1);
    // My y(s2);
    // x.sub(y);
    // std::cout << "result bits are " << x.to_bitstring() << std::endl;
    // std::cout << "res is " << x.to_double() << std::endl;
}


} //namespace my

int main() {

    my::test();
    return 0;
}
