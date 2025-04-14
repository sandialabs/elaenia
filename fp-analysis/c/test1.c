int foo (double x) {
    if (x >= 12) {
        x = x + 5.7;
    } else {
        x = 3.1 * x;
    }

    return x;
}

int main() 
{
    return foo(10);
}
