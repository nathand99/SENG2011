method Deli(a: array<char>, i: int) modifies a
requires 0 <= i < a.Length
requires a.Length > 0
ensures forall m :: 0 <= m < i ==> a[m] == old(a[m])
ensures a[i..a.Length - 1] == old(a[i + 1..a.Length])
ensures a[a.Length - 1] == '.';
{
    var j:int := i;
    while j < a.Length - 1
    invariant 0 <= j < a.Length
    invariant forall m :: 0 <= m < i ==> a[m] == old(a[m])
    invariant a[i..j] == old(a[i+1..j+1])
    invariant a[j..] == old(a[j..])
    decreases a.Length - j
    {
        a[j] := a[j + 1];
        j := j + 1;
    }
    a[a.Length - 1] := '.';

}

method Main()
{
var z := new char[]['b','r','o','o','m'];
Deli(z, 1);
print(z[..]);
assert z[..] == "boom.";
z := new char[]['x'];
Deli(z, 0);
assert z[..] == ".";
}