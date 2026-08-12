// 测试大整数常量（超出 12 位立即数范围）
int main() {
    int a = 32767;
    int b = 32768;
    int c = 65535;
    int result=0;
    
    result = a + b + c;
    result = result % 10000;
    
    return result;
}