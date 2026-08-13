int main() {
    int i = 0;
    int n = 100;
    int a = 5;
    int b = 3;
    int c = 2;
    int sum = 0;
    
    while (i < n) {
        sum = sum + a * b + c;
        i = i + 1;
    }
    
    return sum;
}