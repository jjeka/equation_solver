#define USE_INT64
//#define USE_DOUBLE

int64_t get10PowNumberDigits(int64_t val)
{
    int64_t n = 1;

    if (val < 0)
        val = -val;

    for (int i = 0; val >= n; i++)
    {
        assert(i < 30);
        n *= 10;
    }

    return n;
}

class Number
{
public:
    Number(int64_t numValue = 0);

    bool fromDecimalPoint(int64_t numValue);

    bool isInteger() const;
    int64_t getIntegerValue() const;

    bool isNegative() const;

    bool changeSign();
    bool add(const Number& other);
    bool mul(const Number& other);
    bool div(const Number& divider);
    bool pow(const Number& power);

private:

#if defined(USE_INT64)
    int64_t val;
#elif defined(USE_DOUBLE)
    double val;
#else
    #error Invalid impl
#endif
};

#if defined(USE_INT64)

#define COEF (8 * 9 * 7 * 5 * 5)

Number::Number(int64_t numValue):
        val(numValue * COEF)
{
}

int64_t gcd(int64_t a, int64_t b)
{
    return (a == 0) ? b : gcd(b % a, a);
}

bool Number::fromDecimalPoint(int64_t numValue)
{
    int64_t n = get10PowNumberDigits(numValue);
    int64_t gcdValue = gcd(n, numValue);

    if (COEF % gcdValue != 0)
        return false;

    int a = numValue / gcdValue;
    int b = n / gcdValue;
    val = COEF;
    if (!mul(a))
        return false;
    if (!div(b))
        return false;

    return true;
}

bool Number::isInteger() const
{
    return val % COEF == 0;
}

int64_t Number::getIntegerValue() const
{
    return val / COEF;
}

bool Number::isNegative() const
{
    return val < 0;
}

bool Number::changeSign()
{
    if (val == LLONG_MIN)
        return false;

    val = -val;

    return true;
}

bool Number::add(const Number& other)
{
    return !__builtin_add_overflow(val, other.val, &val);
}

bool Number::mul(const Number& other)
{
    if (__builtin_mul_overflow(val, other.val, &val))
        return false;
    if (val % COEF != 0)
        return false;
    val /= COEF;

    return true;
}

bool Number::div(const Number& divider)
{
    if (__builtin_mul_overflow(val, COEF, &val))
        return false;
    if (divider.val == 0 || (val == LLONG_MAX && divider.val == -1) || val % divider.val != 0)
        return false;
    val = val / divider.val;

    return true;
}

bool Number::pow(const Number& power)
{
    int64_t result;

    if (val == COEF)
        result = COEF;
    else if (val == 0)
    {
        if (power.val == 0)
            return false;
        result = 0;
    }
    else
    {
        if (power.val < 0 || power.val % COEF != 0)
            return false;

        result = COEF;
        for (int i = 0; i < (power.val / COEF); i++)
        {
            if (__builtin_mul_overflow(result, val, &result))
                return false;
            if (result % COEF != 0)
                return false;
            result /= COEF;
        }
    }

    val = result;

    return true;
}

#elif defined(USE_DOUBLE)

#define EPS 0.00000001

Number::Number(int64_t numValue):
        val((double)numValue)
{
}

bool Number::fromDecimalPoint(int64_t numValue)
{
    val = 1.0 / get10PowNumberDigits(numValue) * numValue;
    return std::isfinite(val);
}

bool Number::isInteger() const
{
    return fabs(val - floor(val + EPS)) < EPS;
}

int64_t Number::getIntegerValue() const
{
    return (int64_t)floor(val + EPS);
}

bool Number::isNegative() const
{
    return val < 0;
}

bool Number::changeSign()
{
    val = -val;

    return true;
}

bool Number::add(const Number& other)
{
    val += other.val;

    return std::isfinite(val);
}

bool Number::mul(const Number& other)
{
    val *= other.val;

    return std::isfinite(val);
}

bool Number::div(const Number& divider)
{
    val /= divider.val;

    return std::isfinite(val);
}

bool Number::pow(const Number& power)
{
    val = std::pow(val, power.val);

    return std::isfinite(val);
}

#else
    #error Invalid impl
#endif
