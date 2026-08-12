// test_dce_safe.tc
// 测试死代码删除是否安全
// 包含多个函数，每个函数都有"看起来像死代码"但实际上有用的指令

const int A = 10;
const int B = 20;

// ===== 测试1：返回值被使用 =====
int test1(int x) {
    int a = x * 2;      // 使用
    int b = a + 5;      // 使用
    return b;           // 返回 b
}

// ===== 测试2：中间变量被使用 =====
int test2(int x) {
    int a = x + 10;     // 使用
    int b = a * 2;      // 使用
    int c = b - 5;      // 使用
    return c;           // 返回 c
}

// ===== 测试3：条件分支中的变量 =====
int test3(int x) {
    int a = x * 2;      // 在条件外使用
    int result = 0;
    if (a > 10) {
        int b = a + 5;  // then 分支使用
        result = b;
    } else {
        int c = a - 5;  // else 分支使用
        result = c;
    }
    return result;
}

// ===== 测试4：循环中的变量 =====
int test4(int n) {
    int sum = 0;
    int i = 0;
    int step = 2;       // 循环中使用
    while (i < n) {
        int temp = i * step;  // 循环中使用
        sum = sum + temp;
        i = i + 1;
    }
    return sum;         // 返回 sum
}

// ===== 测试5：全局常量 =====
int test5() {
    int x = A;          // 使用
    int y = B;          // 使用
    return x + y;       // 30
}

// ===== 测试6：函数调用链 =====
int helper(int x) {
    return x + 5;
}

int test6(int x) {
    int a = helper(x);  // 调用结果使用
    int b = a * 2;      // 使用
    return b;           // 返回 b
}

// ===== 主函数 =====
int main() {
    int result = 0;
    
    result = result + test1(5);     // 5*2+5 = 15
    result = result + test2(3);     // (3+10)*2-5 = 21
    result = result + test3(10);    // 10*2=20, 20+5=25
    result = result + test4(5);     // 0+2+4+6+8 = 20
    result = result + test5();      // 10+20 = 30
    result = result + test6(10);    // (10+5)*2 = 30
    
    return result;  // 15+21+25+20+30+30 = 141
}