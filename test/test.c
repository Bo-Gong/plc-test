// 叶子函数：只做算术运算，不调用别人
int add(int a) {
    return a+10;
}


int main() {
    int a = 10;
    int b = 5;
    int c = a + b;
    int d = add(a);
    return d;  // (10+5)+3 = 18
}