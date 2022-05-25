method AbsIt(a:array<int>) modifies a; 
ensures forall x :: 0 <= x < a.Length ==> old(a[x]) < 0 ==> a[x] == -old(a[x])
ensures forall x :: 0 <= x < a.Length ==> old(a[x]) >= 0 ==> a[x] == old(a[x])
{ 
    var i:int := 0; 
    while (i < a.Length) 
    invariant 0 <= i <= a.Length 
    invariant forall x :: 0 <= x < i ==> old(a[x]) < 0 ==> a[x] == -old(a[x])
    invariant forall x :: 0 <= x < i ==> old(a[x]) >= 0 ==> a[x] == old(a[x])
    //invariant forall k:: i <= k < a.Length ==> old(a[k]) == a[k]              // not yet touched 
    { 
        if (a[i] < 0) 
        { 
            a[i] := -a[i]; 
        } 
        i := i + 1; 
    } 
}