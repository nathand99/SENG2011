lemma {:induction false} Divby6(n: nat)
ensures (n*n*n - n) % 6 == 0
{
    if (n == 0) {
        assert (0*0*0 - 0) % 6 == 0; // base case
    } else {
        Divby6(n - 1); // case n - 1
        assert n * n * n - n == n * (n * n - 1);
        assert n * (n * n - 1) == n * (n - 1) * (n + 1); // 3 consecutive numbers
        assert n % 3 == 0 || (n - 1) % 3 == 0 || (n + 1) % 3 == 0; // one number must be divisible by 3
        assert n % 2 == 0 || (n - 1) % 2 == 0 || (n + 1) % 2 == 0; // at least one number must be divisible by 2
        assert (n * (n - 1) * (n + 1)) % 2 == 0; // if divisible by 2 and 3, must be divisible by 2 * 3 = 6
        assert (n * (n - 1) * (n + 1)) % 3 == 0;
        assert (n * (n - 1) * (n + 1)) % 6 == 0;
    }
}