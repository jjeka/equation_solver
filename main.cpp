#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cmath>
#include <cassert>
#include <cstring>
#include <vector>
#include <string>
#include <mutex>
#include <thread>
#include <queue>
#include <atomic>

//#define SKIP_EMPTY
#define NUM_THREADS 16
#define DISABLE_ASSERTS

#ifdef DISABLE_ASSERTS
#undef assert
#define assert(a)
#endif // DISABLE_ASSERTS

#include "number.h"

#define MAX_ANSWER 15000
#define MAX_NUMBERS 10
#define MAX_STR_SIZE 256
#define TREE_SIZE (1 << MAX_NUMBERS)
#define TASK_SIZE 8
#define MAX_FACTORIAL 7
#define MAX_NODE_FACTORIALS 2

#define MAX_POWER 30
#define MAX_DIV_BY 100000

#define ALIGN_UP(a,b) ((((a) + (b) - 1) / (b)) * (b))
#define min(a,b) (((a) < (b)) ? (a) : (b))

typedef std::string equation;

std::vector<equation> equationsForAnswer[MAX_ANSWER + 1];
std::mutex equationMutexes[MAX_ANSWER + 1];

enum GlobalOperation
{
    GLOP_CONCATENATE,
    GLOP_MINUS,
    GLOP_DECIMAL,
    GLOP_REPEATING_DECIMAL,
    GLOP_ADD,
    GLOP_MULTIPLY,
    GLOP_DIVIDE,
    GLOP_POWER,
    GLOP_FACTORIAL,
    GLOP_SQRT,
    GLOP_NUM
};

struct Statistics
{
    std::atomic<uint64_t> numEquations;
    std::atomic<uint64_t> numEquationsWithAnswer;
    std::atomic<uint64_t> numEquationsWithAnswerInRange;
};

Statistics statistics = {};

bool globalOperation[GLOP_NUM] = {};
int numInputNumbers;
int numSolved;
std::mutex numSolvedMutex;
int numSolveTasks;
int* solveTasks = NULL;
std::mutex solveTaskMutex;
int maxAnswer;
int maxSolutons;

enum Operation
{
    OP_ADD,
    OP_MUL,
    OP_DIV,
    OP_POW,
    OP_NUM,

    OP_EXIST = OP_NUM,
    OP_NONE
};

struct NumberSetNumber
{
    Number n;
    int64_t originalValue;
    bool originalValueDecimal;
    bool originalValueRepeatingDecimal;
};

struct NumberSet
{
    int numNumbers;
    NumberSetNumber number[MAX_NUMBERS];

    NumberSetNumber& getNumber(int index)
    {
        assert(index < MAX_NUMBERS);
        return number[index];
    }
    const NumberSetNumber& getNumber(int index) const
    {
        assert(number < MAX_NUMBERS);
        return number[index];
    }
};

enum ExtraOp
{
    EXOP_FACTORIAL = 1,
    EXOP_SQRT = 2
};

struct Node
{
    int op;
    bool cachedValueValid;
    Number cachedValue;
    int numFactorials;

    bool originalValueDecimal;
    bool originalValueRepeatingDecimal;
    int64_t originalValue;
};

struct Tree
{
    int numLeaves;
    Node node[TREE_SIZE];

    Node& getNode(int index)
    {
        assert(index < TREE_SIZE);
        return node[index];
    }
    const Node& getNode(int index) const
    {
        assert(index < TREE_SIZE);
        return node[index];
    }
};

std::vector<NumberSet> numberSets[MAX_NUMBERS + 1];
std::vector<Tree> nLeafTrees[MAX_NUMBERS + 1];

#define GET_LEFT(n) (((n) + 1) * 2 - 1)
#define GET_RIGHT(n) (((n) + 1) * 2)
#define GET_PARENT(n) ((n + 1) / 2 - 1)

int getDepth(int node)
{
    int depth = 0;
    while (node != 0)
    {
        node = GET_PARENT(node);
        depth++;
    }
    return depth;
}

Tree getEmptyTree()
{
    Tree tree = {};
    for (int i = 0; i < TREE_SIZE; i++)
    {
        tree.getNode(i).op = OP_NONE;
        tree.getNode(i).cachedValueValid = false;
        tree.getNode(i).numFactorials = 0;
    }
    return tree;
}

void copyTreePart(Tree& dst, const Tree& src, int dstPos, int srcPos)
{
    assert(srcPos < TREE_SIZE && dstPos < TREE_SIZE);

    if (src.getNode(srcPos).op == OP_NONE)
        return;

    dst.getNode(dstPos).op = OP_EXIST;

    copyTreePart(dst, src, GET_LEFT(dstPos), GET_LEFT(srcPos));
    copyTreePart(dst, src, GET_RIGHT(dstPos), GET_RIGHT(srcPos));
}

void createNLeafTrees(int n)
{
    if (n == 1)
    {
        Tree tree = getEmptyTree();
        tree.numLeaves = n;
        nLeafTrees[n].push_back(tree);
        return;
    }

    for (int split = 1; split < n; split++)
    {
        std::vector<Tree>& leftTrees = nLeafTrees[split];
        std::vector<Tree>& rightTrees = nLeafTrees[n - split];

        assert(leftTrees.size());
        assert(rightTrees.size());

        for (Tree& left : leftTrees)
        {
            for (Tree& right : rightTrees)
            {
                Tree tree = getEmptyTree();
                tree.numLeaves = n;
                tree.getNode(0).op = OP_EXIST;
                copyTreePart(tree, left, GET_LEFT(0), 0);
                copyTreePart(tree, right, GET_RIGHT(0), 0);
                nLeafTrees[n].push_back(tree);
            }
        }
    }
}

int getLeftMostDigit(int number, int* divisor)
{
    *divisor = 1;
    int i;
    for (i = number; i > 9; i /= 10)
        *divisor *= 10;
    return number / (*divisor);
}

bool prepareData()
{
    FILE* f = fopen("input.txt", "r");
    assert(f);

    char str[MAX_STR_SIZE];

    int64_t numbers[MAX_NUMBERS] = {};

    fgets(str, MAX_STR_SIZE, f);

    numInputNumbers = 0;

    int currentPos = 0;
    for (;;)
    {
        int64_t n;
        int tmp;
        if (sscanf(str + currentPos, "%lld %n", &n, &tmp) != 1)
            break;
        currentPos += tmp;

        if (numInputNumbers > MAX_NUMBERS)
        {
            printf("Error: maximum %d numbers!\n", MAX_NUMBERS);
            return false;
        }
        if (n < 0)
        {
            printf("Error: negative number\n");
            return false;
        }

        numbers[numInputNumbers] = n;
        numInputNumbers++;
    }

    if (numInputNumbers == 0)
    {
        printf("Error: 0 input numbers\n");
        return false;
    }

    if (fscanf(f, "%d %d", &maxAnswer, &maxSolutons) != 2)
    {
        printf("Error: max answer and max solutions are expected\n");
        return false;
    }
    if (maxAnswer < 0)
    {
        printf("Error: max answer should be greater than or equal to zero");
        return false;
    }
    if (maxSolutons < 1)
    {
        printf("Error: max answer should be greater than zero");
        return false;
    }

    if (fscanf(f, "%s", str) != 1)
    {
        printf("Error: operations are expected\n");
        return false;
    }

    if (strstr(str, "|"))
        globalOperation[GLOP_CONCATENATE] = true;
    if (strstr(str, "-"))
        globalOperation[GLOP_MINUS] = true;
    if (strstr(str, "."))
        globalOperation[GLOP_DECIMAL] = true;
    if (strstr(str, "r"))
        globalOperation[GLOP_REPEATING_DECIMAL] = true;
    if (strstr(str, "+"))
        globalOperation[GLOP_ADD] = true;
    if (strstr(str, "*"))
        globalOperation[GLOP_MULTIPLY] = true;
    if (strstr(str, "/"))
        globalOperation[GLOP_DIVIDE] = true;
    if (strstr(str, "^"))
        globalOperation[GLOP_POWER] = true;
    if (strstr(str, "!"))
        globalOperation[GLOP_FACTORIAL] = true;
    if (strstr(str, "s"))
        globalOperation[GLOP_SQRT] = true;

    if (!globalOperation[GLOP_CONCATENATE] && !globalOperation[GLOP_ADD]
        && !globalOperation[GLOP_MULTIPLY] && !globalOperation[GLOP_DIVIDE]
        && !globalOperation[GLOP_POWER])
    {
        printf("Eror: at least one of: |+*/^ is required\n");
        return false;
    }

    int numConcatenations = globalOperation[GLOP_CONCATENATE]
        ? (1 << (numInputNumbers - 1)) : 1;
    for (int i = 0; i < numConcatenations; i++)
    {
        int numNumbers = 1;
        for (int j = 0; j < (numInputNumbers - 1); j++)
        {
            if (!(i & (1 << j)))
                numNumbers++;
        }

        int numSigns = globalOperation[GLOP_MINUS] ? (1 << numNumbers) : 1;
        for (int j = 0; j < numSigns; j++)
        {
            int numDecimalsOrRepeatingDecimals = 1;
            if (globalOperation[GLOP_DECIMAL])
                numDecimalsOrRepeatingDecimals *= 1 << numNumbers;
            if (globalOperation[GLOP_REPEATING_DECIMAL])
                numDecimalsOrRepeatingDecimals *= 1 << numNumbers;
            bool decimalsAndRepeatingDecimals = globalOperation[GLOP_DECIMAL] &&
                globalOperation[GLOP_REPEATING_DECIMAL];

            for (int k = 0; k < numDecimalsOrRepeatingDecimals; k++)
            {
                NumberSet numberSet;
                numberSet.numNumbers = numNumbers;
                bool badNumberSet = false;

                if (decimalsAndRepeatingDecimals &&
                    (k & (1 << numNumbers)) & (k >> numNumbers))
                    continue;

                numberSet.getNumber(0).n = numbers[0];

                if (j & 1)
                    numberSet.getNumber(0).n.changeSign();

                int n = 0;
                for (int l = 0; l < numInputNumbers - 1; l++)
                {
                    if (!(i & (1 << l)))
                    {
                        assert(numberSet.n[n].isInteger());
                        numberSet.getNumber(n).originalValue = numberSet.getNumber(n).n.getIntegerValue();
                        numberSet.getNumber(n).originalValueDecimal =
                            globalOperation[GLOP_DECIMAL] ? (k & (1 << n)) : false;
                        numberSet.getNumber(n).originalValueRepeatingDecimal =
                            globalOperation[GLOP_REPEATING_DECIMAL]
                                ? (globalOperation[GLOP_DECIMAL] ? (k & (1 << (numNumbers + n)))
                                : (k & (1 << n))) : false;
                        if (numberSet.getNumber(n).originalValueDecimal
                            || numberSet.getNumber(n).originalValueRepeatingDecimal)
                        {
                            if (!numberSet.getNumber(n).n.fromDecimal(
                                    numberSet.getNumber(n).n.getIntegerValue(),
                                    numberSet.getNumber(n).originalValueRepeatingDecimal))
                            {
                                badNumberSet = true;
                                break;
                            }
                        }

                        n++;
                        numberSet.getNumber(n).n = numbers[l + 1];
                        if (j & (1 << n))
                        {
                            if (!numberSet.getNumber(n).n.changeSign())
                            {
                                printf("Error: internal changeSign error\n");
                                return false;
                            }
                        }
                    }
                    else
                    {
                        // concatenate
                        int64_t newNumber = numbers[l + 1];
                        int64_t mulValue = get10PowNumberDigits(newNumber);
                        Number result = numberSet.getNumber(n).n;

                        if (!result.mul(mulValue))
                        {
                            printf("Warning: skip big number %llu%llu",
                                   numberSet.getNumber(n).n.getIntegerValue(), newNumber);
                            badNumberSet = true;
                            break;
                        }

                        bool negative = result.isNegative();
                        if (negative)
                        {
                            if (!result.changeSign())
                            {
                                printf("Error: internal changeSign error\n");
                                return false;
                            }
                        }

                        if (!result.add(newNumber))
                        {
                            printf("Warning: skip big number %llu%llu",
                                   numberSet.getNumber(n).n.getIntegerValue(), newNumber);
                            badNumberSet = true;
                            break;
                        }

                        if (negative)
                        {
                            if (!result.changeSign())
                            {
                                printf("Error: internal changeSign error\n");
                                return false;
                            }
                        }

                        numberSet.getNumber(n).n = result;
                    }
                }

                assert(numberSet.n[n].isInteger());
                numberSet.getNumber(n).originalValue = numberSet.getNumber(n).n.getIntegerValue();
                numberSet.getNumber(n).originalValueDecimal =
                    globalOperation[GLOP_DECIMAL] ? (k & (1 << n)) : false;
                numberSet.getNumber(n).originalValueRepeatingDecimal =
                    globalOperation[GLOP_REPEATING_DECIMAL]
                        ? (globalOperation[GLOP_DECIMAL] ? (k & (1 << (numNumbers + n)))
                        : (k & (1 << n))) : false;
                if (numberSet.getNumber(n).originalValueDecimal
                    || numberSet.getNumber(n).originalValueRepeatingDecimal)
                {
                    if (!numberSet.getNumber(n).n.fromDecimal(
                        numberSet.getNumber(n).n.getIntegerValue(),
                        numberSet.getNumber(n).originalValueRepeatingDecimal))
                    {
                        badNumberSet = true;
                        break;
                    }
                }


                if (!badNumberSet)
                    numberSets[numNumbers].push_back(numberSet);
            }
        }
    }

    for (int i = 1; i <= numInputNumbers; i++)
        createNLeafTrees(i);

    printf("DATA PREPARED\n");

    printf("%d NUMBERS: ", numInputNumbers);
    for (int i = 0; i < numInputNumbers; i++)
        printf("%lld ", numbers[i]);
    printf("\n");

    printf("MAX ANSWER %d\n", maxAnswer);
    printf("MAX SOLUTIONS %d\n", maxSolutons);

    printf("OPERATIONS: ");
    if (globalOperation[GLOP_CONCATENATE])
        printf("concatenate ");
    if (globalOperation[GLOP_MINUS])
        printf("minus ");
    if (globalOperation[GLOP_DECIMAL])
        printf("decimal ");
    if (globalOperation[GLOP_REPEATING_DECIMAL])
        printf("repeating_decimal ");
    if (globalOperation[GLOP_ADD])
        printf("add ");
    if (globalOperation[GLOP_MULTIPLY])
        printf("multiply ");
    if (globalOperation[GLOP_DIVIDE])
        printf("divide ");
    if (globalOperation[GLOP_POWER])
        printf("power ");
    if (globalOperation[GLOP_FACTORIAL])
        printf("factorial ");
    if (globalOperation[GLOP_SQRT])
        printf("sqrt ");
    printf("\n");

    printf("\nITERATIONS\n");
    int64_t sum = 0;
    for (int i = 1; i <= numInputNumbers; i++)
    {
        int64_t num = (int)numberSets[i].size() * (int)nLeafTrees[i].size();
        printf("%d numbers: %lld iterations (%d numbers * %d trees)\n", i, num,
               (int)numberSets[i].size(), (int)nLeafTrees[i].size());
        sum += num;
    }
    printf("TOTAL %lld ITERATIONS\n\n", sum);

    return true;
}

void printResult()
{
    FILE* f = fopen("output.txt", "w");

    for (int i = 0; i <= maxAnswer; i++)
    {
#ifdef SKIP_EMPTY
        if (!equationsForAnswer[i].size())
            continue;
#endif

        fprintf(f, "%i", i);
        if (!equationsForAnswer[i].size())
            fprintf(f, " = NO RESULT");
        for (equation& e : equationsForAnswer[i])
            fprintf(f, " = %s", e.c_str());
        fprintf(f, "\n");
    }
    fclose(f);

    printf("RESULT SAVED\n");
}

void addNumber(int64_t n, bool decimal, bool repeatingDecimal, bool ignoreMinus, char* str, int* offset)
{
    if (n < 0)
    {
        if (!ignoreMinus)
        {
            str[*offset] = '-';
            (*offset)++;
        }
        n = -n;
    }

    if (decimal || repeatingDecimal)
    {
        str[*offset] = '.';
        (*offset)++;
    }
    if (repeatingDecimal)
    {
        str[*offset] = '(';
        (*offset)++;
    }

    do
    {
        int divisor;
        int digit = getLeftMostDigit(n, &divisor);

        n -= digit * divisor;

        str[*offset] = digit + '0';
        (*offset)++;
    }
    while (n != 0);

    if (repeatingDecimal)
    {
        str[*offset] = ')';
        (*offset)++;
    }
}

void addAnswerPart(const Tree& tree, int node, bool ignoreMinus, char* str, int* offset)
{
    if (tree.getNode(node).op == OP_NONE)
    {
        assert(tree.getNode(node).cachedValueValid);

        addNumber(tree.getNode(node).originalValue,
                  tree.getNode(node).originalValueDecimal,
                  tree.getNode(node).originalValueRepeatingDecimal,
                  ignoreMinus, str, offset);

        for (int i = 0; i < tree.getNode(node).numFactorials; i++)
        {
            str[*offset] = '!';
            (*offset)++;
        }

        return;
    }

    assert(GET_RIGHT(node) < TREE_SIZE);

    int op = tree.getNode(node).op;
    int parentOp = node != 0 ? tree.getNode(GET_PARENT(node)).op : OP_NONE;
    bool omitSum = parentOp == OP_ADD;
    bool omitMul = parentOp == OP_MUL && (op == OP_MUL || op == OP_DIV || op == OP_POW);
    bool omitDiv = parentOp == OP_DIV && op == OP_DIV && node != 0 && node == GET_LEFT(GET_PARENT(node));
    bool omitBrackets = !tree.getNode(node).numFactorials && (node == 0 || omitSum || omitMul || omitDiv);

    // TODO: proper fix
    bool factorialFix = tree.getNode(node).numFactorials && tree.getNode(node).cachedValue.isNegative();
    bool addFix = op == OP_ADD && tree.getNode(GET_RIGHT(node)).op == OP_NONE
        && tree.getNode(GET_RIGHT(node)).originalValue < 0;
    bool powFix = op == OP_POW && tree.getNode(GET_LEFT(node)).cachedValue.isNegative();
    bool powFixLeftNumber = powFix && tree.getNode(GET_LEFT(node)).op == OP_NONE;

    if (factorialFix)
    {
        str[*offset] = '-';
        (*offset)++;
    }

    if (!omitBrackets)
    {
        str[*offset] = '(';
        (*offset)++;
    }

    if (factorialFix)
    {
        str[*offset] = '-';
        (*offset)++;
        str[*offset] = '(';
        (*offset)++;
    }

    if (powFix)
    {
        str[*offset] = '-';
        (*offset)++;
        str[*offset] = '(';
        (*offset)++;
        if (!powFixLeftNumber)
        {
            str[*offset] = '-';
            (*offset)++;
        }
    }

    addAnswerPart(tree, GET_LEFT(node), powFixLeftNumber, str, offset);

    if (powFix && !powFixLeftNumber)
    {
        str[*offset] = ')';
        (*offset)++;
    }

    str[*offset] = ' ';
    (*offset)++;
    switch (op)
    {
    case OP_ADD: str[*offset] = addFix ? '-' : '+'; break;
    case OP_MUL: str[*offset] = '*'; break;
    case OP_DIV: str[*offset] = '/'; break;
    case OP_POW: str[*offset] = '^'; break;
    default: assert(0); break;
    }
    (*offset)++;
    str[*offset] = ' ';
    (*offset)++;

    addAnswerPart(tree, GET_RIGHT(node), addFix, str, offset);

    if (powFix)
    {
        str[*offset] = ')';
        (*offset)++;
    }

    if (factorialFix)
    {
        str[*offset] = ')';
        (*offset)++;
    }

    if (!omitBrackets)
    {
        str[*offset] = ')';
        (*offset)++;
    }

    for (int i = 0; i < tree.getNode(node).numFactorials; i++)
    {
        str[*offset] = '!';
        (*offset)++;
    }
}

void addAnswer(const Tree& tree, int64_t answer)
{
    if (answer < 0 || answer > maxAnswer)
        return;

    statistics.numEquationsWithAnswerInRange++;

    equationMutexes[answer].lock();
    if ((int)equationsForAnswer[answer].size() >= maxSolutons)
    {
        equationMutexes[answer].unlock();
        return;
    }
    equationMutexes[answer].unlock();

    char str[MAX_STR_SIZE];
    int offset = 0;
    addAnswerPart(tree, 0, false, str, &offset);
    assert(offset < MAX_STR_SIZE);
    str[offset] = 0;

    equationMutexes[answer].lock();
    equationsForAnswer[answer].push_back(str);
    equationMutexes[answer].unlock();
}


int64_t getFactorial(int64_t n)
{
    bool negative = n < 0;
    if (negative)
        n = -n;

    int64_t result = 1;
    for (int i = 2; i <= n; i++)
        result *= i;

    if (negative)
        result = -result;

    return result;
}

Number solveEquationPart(Tree& tree, int node, bool* valid)
{
    if (tree.getNode(node).cachedValueValid)
    {
        *valid = true;
        return tree.getNode(node).cachedValue;
    }

    if (tree.getNode(node).op == OP_NONE)
    {
        int64_t n = tree.getNode(node).originalValue;
        for (int i = 0; i < tree.getNode(node).numFactorials; i++)
            n = getFactorial(n);

        tree.getNode(node).cachedValue = n;
        tree.getNode(node).cachedValueValid = true;
        *valid = true;
        return tree.getNode(node).cachedValue;
    }

    bool leftValid, rightValid;

    Number left = solveEquationPart(tree, GET_LEFT(node), &leftValid);
    Number right = solveEquationPart(tree, GET_RIGHT(node), &rightValid);

    if (!leftValid || !rightValid)
    {
        *valid = false;
        return left;
    }

    bool leftNegative = false;

    switch (tree.getNode(node).op)
    {
    case OP_ADD:
        if (!left.add(right))
        {
            *valid = false;
            return left;
        }
        break;
    case OP_MUL:
        if (!left.mul(right))
        {
            *valid = false;
            return left;
        }
        break;
    case OP_DIV:
        if (right.getIntegerValue() < -MAX_DIV_BY || right.getIntegerValue() > MAX_DIV_BY)
        {
            *valid = false;
            return left;
        }

        if (!left.div(right))
        {
            *valid = false;
            return left;
        }
        break;
    case OP_POW:
        if (right.getIntegerValue() > MAX_POWER
            || right.getIntegerValue() < -MAX_POWER)
        {
            *valid = false;
            return left;
        }

        if (left.isNegative())
        {
            leftNegative = true;
            if (!left.changeSign())
            {
                *valid = false;
                return left;
            }
        }

        if (!left.pow(right))
        {
            *valid = false;
            return left;
        }

        if (leftNegative)
        {
            if (!left.changeSign())
            {
                *valid = false;
                return left;
            }
        }
        break;
    default: assert(0); break;
    }

    if (tree.getNode(node).numFactorials)
    {
        assert(left.isInteger());
        int64_t n = left.getIntegerValue();
        for (int i = 0; i < tree.getNode(node).numFactorials; i++)
            n = getFactorial(n);
        left = n;
    }

    tree.getNode(node).cachedValueValid = true;
    tree.getNode(node).cachedValue = left;

    *valid = true;
    return left;
}

void solveEquation(Tree& tree, int nodePositions[][MAX_NUMBERS], int depth, bool needSolve)
{
    bool valid = true;

    if (needSolve)
    {
        statistics.numEquations++;

        Number result = solveEquationPart(tree, 0, &valid);

        if (valid)
            statistics.numEquationsWithAnswer++;

        if (valid && result.isInteger())
            addAnswer(tree, result.getIntegerValue());
    }

    if (globalOperation[GLOP_FACTORIAL] && depth != 0 && valid)
    {
        int factorialPositions[2 * MAX_NUMBERS];
        int numFactorialPositions = 0;

        int numNodes = 0;
        for (; numNodes < (1 << depth); numNodes++)
        {
            if (nodePositions[depth][numNodes] == -1)
                break;
        }

        for (int i = 0; i < numNodes; i++)
        {
            int node = nodePositions[depth][i];
            assert(tree.getNode(node).cachedValueValid);
            if (tree.getNode(node).cachedValue.isInteger())
            {
                int64_t val = tree.getNode(node).cachedValue.getIntegerValue();
                if (val >= -MAX_FACTORIAL && val <= MAX_FACTORIAL
                    && val != 1 && val != -1 && val != 2 && val != -2)
                {
                    factorialPositions[numFactorialPositions] = node;
                    numFactorialPositions++;

                    if (val == 3 || val == -3)
                    {
                        factorialPositions[numFactorialPositions] = node;
                        numFactorialPositions++;
                    }
                }
            }
        }

        for (int i = 0; i < (1 << numFactorialPositions); i++)
        {
            Tree newTree = tree;
            bool skip = false;
            for (int j = 0; j < numFactorialPositions; j++)
            {
                if (j != 0 && factorialPositions[j] == factorialPositions[j - 1]
                    && (i & (1 << j)) && !(i & (1 << (j - 1))))
                {
                    skip = true;
                    continue;
                }

                if (i & (1 << j))
                {
                    newTree.getNode(factorialPositions[j]).numFactorials++;
                    int node = factorialPositions[j];
                    for (;;)
                    {
                        newTree.getNode(node).cachedValueValid = false;
                        if (!node)
                            break;

                        node = GET_PARENT(node);
                    }
                }
            }

            if (!skip)
                solveEquation(newTree, nodePositions, depth - 1, i != 0);
        }
    }
}

void setLeafCachedValuesPart(const NumberSet& numSet, int* currentNumber, Tree& tree, int node)
{
    if (tree.getNode(node).op == OP_NONE)
    {
        Number number = numSet.getNumber(*currentNumber).n;
        tree.getNode(node).cachedValue = number;
        tree.getNode(node).cachedValueValid = true;
        tree.getNode(node).originalValue = numSet.getNumber(*currentNumber).originalValue;
        tree.getNode(node).originalValueDecimal =
            numSet.getNumber(*currentNumber).originalValueDecimal;
        tree.getNode(node).originalValueRepeatingDecimal =
            numSet.getNumber(*currentNumber).originalValueRepeatingDecimal;
        (*currentNumber)++;
        return;
    }

    setLeafCachedValuesPart(numSet, currentNumber, tree, GET_LEFT(node));
    setLeafCachedValuesPart(numSet, currentNumber, tree, GET_RIGHT(node));
}

void setLeafCachedValues(const NumberSet& numSet, Tree& tree)
{
    int currentNumber = 0;
    setLeafCachedValuesPart(numSet, &currentNumber, tree, 0);
    assert(currentNumber == numSet.numNumbers);
}

void solveEquationSetWithParams(Tree& tree, int opPositions[], int nodePositions[][MAX_NUMBERS])
{
    int numOps = tree.numLeaves - 1;
    int numTrees = 1 << (2 * numOps); // XXX: 2 bits per op

    int maxDepth = 0;
    for (int i = 0; i < MAX_NUMBERS - 1; i++)
    {
        if (nodePositions[i][0] != -1)
            maxDepth++;
    }

    for (int i = 0; i < numTrees; i++)
    {
        bool doNotSolve = false;
        for (int j = 0; j < numOps; j++)
        {
            int op = (i >> (2 * (numOps - 1) - 2 * j)) & 3;
            if ((op == OP_ADD && !globalOperation[GLOP_ADD])
                || (op == OP_MUL && !globalOperation[GLOP_MULTIPLY])
                || (op == OP_DIV && !globalOperation[GLOP_DIVIDE])
                || (op == OP_POW && !globalOperation[GLOP_POWER]))
            {
                doNotSolve = true;
                break;
            }

            int node = opPositions[j];
            int parent = GET_PARENT(node);

            // add/mul incorrect order skip
            if ((op == OP_ADD || op == OP_MUL)
                && node != 0 && tree.getNode(parent).op == op
                && GET_RIGHT(parent) == node)
            {
                doNotSolve = true;
                break;
            }

            // a / (b / c) skip
            if (op == OP_DIV
                && node != 0 && tree.getNode(parent).op == OP_DIV
                && GET_RIGHT(parent) == node)
            {
                doNotSolve = true;
                break;
            }

            int rightMostLeftNode = GET_RIGHT(node);
            while (tree.getNode(rightMostLeftNode).op != OP_NONE)
                rightMostLeftNode = GET_LEFT(rightMostLeftNode);

            // a * -b skip | a / -b skip
            // note: there could we: -a * (b - c), where b - c < 0
            if ((op == OP_MUL || op == OP_DIV)
                && tree.getNode(rightMostLeftNode).originalValue < 0)
            {
                doNotSolve = true;
                break;
            }

            if (tree.getNode(node).op != op)
            {
                int n = node;
                for (;;)
                {
                    tree.getNode(n).cachedValueValid = false;
                    if (!n)
                        break;

                    n = GET_PARENT(n);
                }
            }

            tree.getNode(node).op = op;
        }
        if (!doNotSolve)
            solveEquation(tree, nodePositions, maxDepth, true);
    }
}

void getOpAndNodePositions(const Tree& tree, int opPositions[], int nodePositions[][MAX_NUMBERS])
{
    int opIndex = 0;

    std::queue<int> q;
    q.push(0);

    int nodeIndex[MAX_NUMBERS - 1] = {};

    for (int i = 0; i < MAX_NUMBERS - 1; i++)
        for (int j = 0; j < MAX_NUMBERS; j++)
        nodePositions[i][j] = -1;

    while (!q.empty())
    {
        int node = q.front();
        q.pop();

        int depth = getDepth(node);
        nodePositions[depth][nodeIndex[depth]] = node;
        nodeIndex[depth]++;

        if (tree.getNode(node).op != OP_NONE)
        {
            opPositions[opIndex] = node;
            opIndex++;

            q.push(GET_LEFT(node));
            q.push(GET_RIGHT(node));
        }
    }

    assert(opIndex == tree.numLeaves - 1);
}

void solveEquationSet(const NumberSet& numSet, const Tree& tree)
{
    assert(numSet.numNumbers == tree.numLeaves);

    int opPositions[MAX_NUMBERS - 1];
    int nodePositions[MAX_NUMBERS - 1][MAX_NUMBERS];
    getOpAndNodePositions(tree, opPositions, nodePositions);

    Tree t = tree;
    setLeafCachedValues(numSet, t);

    solveEquationSetWithParams(t, opPositions, nodePositions);
}

int findTask()
{
    solveTaskMutex.lock();

    for (int i = 0; i < numSolveTasks; i++)
    {
        if (solveTasks[i] != -1)
        {
            int task = solveTasks[i];
            solveTasks[i] = -1;
            solveTaskMutex.unlock();
            return task;
        }
    }

    solveTaskMutex.unlock();
    return -1;
}

void solveThread(int n)
{
    int num = (int)numberSets[n].size() * (int)nLeafTrees[n].size();

    int task;
    while ((task = findTask()) != -1)
    {
        int numSetsInTask = min(TASK_SIZE, (int)numberSets[n].size() - task * TASK_SIZE);
        for (int i = 0; i < numSetsInTask; i++)
        {
            int numSetN = task * TASK_SIZE + i;
            for (int j = 0; j < (int)nLeafTrees[n].size(); j++)
            {
                solveEquationSet(numberSets[n][numSetN], nLeafTrees[n][j]);
            }
        }
        int addSolved = numSetsInTask * (int)nLeafTrees[n].size();

        numSolvedMutex.lock();
        numSolved += addSolved;
        int currentSolved = numSolved;
        numSolvedMutex.unlock();
        printf("%d / %d\n", currentSolved, num);
    }
}

void solveForNumber(int n)
{
    numSolveTasks = ((int)numberSets[n].size() + TASK_SIZE - 1) / TASK_SIZE;
    solveTasks = new int[numSolveTasks];
    numSolved = 0;

    for (int i = 0; i < numSolveTasks; i++)
        solveTasks[i] = i;

    if (NUM_THREADS == 1)
        solveThread(n);
    else
    {
        std::thread threads[NUM_THREADS];

        for (int i = 0; i < NUM_THREADS; i++)
            threads[i] = std::thread(solveThread, n);

        for (int i = 0; i < NUM_THREADS; i++)
            threads[i].join();
    }

    delete[] solveTasks;
}

void solve()
{
    printf("SOLVING\n");

    for (int i = 1; i <= numInputNumbers; i++)
    {
        printf("START NUMBER %d\n", i);
        solveForNumber(i);
    }

    printf("DONE\n");
}

void printStatistics()
{
    printf("\nSTATISTICS\n");
    printf("Num equations                     : %llu\n", statistics.numEquations.load());
    printf("Num equations with answer         : %llu\n", statistics.numEquationsWithAnswer.load());
    printf("Num equations with answer in range: %llu\n", statistics.numEquationsWithAnswerInRange.load());
}

int main()
{
    if (!prepareData())
        return 1;

    solve();

    printResult();
    printStatistics();

    return 0;
}
