// 叶子函数：只做算术运算，不调用别人
int add(int a,int b) {
    return a*4;
}


int main() {
    int a = 10;
    int b = a*2;
    int c = a + b;
    int d = add(a,c);
    return d;  // (10+5)+3 = 18
}