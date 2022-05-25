// does not verify
// cannot verify in the loop that everything between 0 and i is sorted - needs more invariants
// also cannot verify multiset condition because it is not a multiset
// verifies that the elements between m and n - 1 of the array c are sorted in ascending order
predicate sortedarray(c:array<char>, m:nat, n:nat) reads c
requires 0 <= m <= n <= c.Length;
{ 
    forall j, k :: m <= j < k < n ==> c[j] <= c[k]
}
// insertion sort using a shuffle-based strategy
method ShuffleSort(a: array<char>) returns (b: array<char>)
ensures sortedarray(b, 0, b.Length); 
ensures multiset(b[..]) == multiset(a[..]);
ensures a.Length == b.Length;
{
    // copy array a to new array b
    b := new char[a.Length];
    var k := 0;
    while (k < a.Length) 
    invariant 0 <= k <= a.Length;
    invariant forall i :: 0 <= i < k ==> a[i] == b[i];
    {
        b[k] := a[k];
        k := k + 1;
    }

    if (a.Length == 0) {
        return b;
    } else {
        var i := 1;
        var copy;
        while (i < b.Length) 
        invariant 1 <= i <= b.Length;
        invariant sortedarray(b, 0, i);
        invariant multiset(b[..i]) == multiset(a[..i]);
        {
            if (b[i] < b[i - 1]) {
                copy := b[i];
                b[i] := b[i - 1];
                var j := i - 1;
                if (j == 0) {
                    b[j] := copy;
                    break;
                }
                while (j >= 0) 
                invariant i > j;
                invariant 0 <= j < b.Length;
                invariant sortedarray(b, j + 1, i);
                {
                    if (j == 0 || b[j - 1] > copy) {                
                        b[j] := copy;
                        break;
                    } else {
                        b[j] := b[j - 1];
                    }
                    j := j - 1;
                }
            }
            i := i + 1;
        }
    }
}

method check() {
    var a := new char[5]['e','d','c','b','a'];
    assert a[0]=='e' && a[1]=='d' && a[2]=='c' && a[3]=='b' && a[4]=='a';
    var b := ShuffleSort(a);
    assert sortedarray(b, 0, b.Length);
    assert multiset(b[..]) == multiset(a[..]);
}
