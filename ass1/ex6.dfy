// successfully verifies
method SumOfSquares(n:int) returns (sum:int)
requires n >= 0;
ensures sum == ((n * (n + 1) * (2 * n + 1)) / 6);
{
    sum := 0;
    var i := 0;
    while i <= n
    invariant 0 <= i <= n + 1 && sum == (((i - 1) * ((i - 1) + 1) * (2 * (i - 1) + 1)) / 6);
    decreases n - i;
    {
        sum := sum + i * i;
        i := i + 1;
    }
}