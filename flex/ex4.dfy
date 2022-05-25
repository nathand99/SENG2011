method combine(a: array<int>, b: array<int>) returns (c:array<int>)
{
    var d := new int[a.Length + b.Length];
    var i := 0;
    while (i < a.Length) 
    invariant 0 <= i <= a.Length;
    //invariant forall x :: 0 <= x < k ==> b[x] == a[a.Length - x - 1]
    {
        d[i] := a[i];
        i := i + 1;
    }
    var k := 0;
    var j := i;
    while (k < b.Length) 
    invariant 0 <= k <= b.Length;
    invariant 0 <= j <= d.Length
    //invariant forall x :: 0 <= x < k ==> b[x] == a[a.Length - x - 1]
    {
        d[j] := b[k];
        j := j + 1;
        k := k + 1;
    }

    c := new int[i];
    k := 0;
    while (k < a.Length) 
    invariant 0 <= k <= c.Length;
    //invariant forall x :: 0 <= x < k ==> b[x] == a[a.Length - x - 1]
    {
        if !(d[k] in c[..]) {
            c[k] := d[k];
        }
        k := k + 1;
    }

}