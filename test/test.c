// test_cross_block_prop.tc
// 测试常量传播能否跨基本块

const int A = 10;
const int B = 20;
const int C = 30;

int main() {
    int x = A;           // 10
    int y = B;           // 20
    int z = C;           // 30
    
    int result=0;
    if (x > y) {         // 10 > 20 = false
        result = x + y;  // 不执行
    } else {
        result = x + z;  // 10 + 30 = 40
    }
    
    return result;       // 40
}