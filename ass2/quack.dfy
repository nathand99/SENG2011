class Quack
{
    var buf:array<char>;
    var m:int, n:int;

    ghost var shadow: seq<char>;

    predicate Valid() reads this, this.buf
    { buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int)
    requires size > 0;
    ensures shadow == []
    ensures fresh(buf)
    ensures Valid()
    {
        buf := new char[size];
        m, n:= 0, 0;
        shadow:= [];
    }

    method Empty() returns (x: bool)
    requires Valid();
    ensures x <==> shadow==[] // an empty shadow means x is true
    ensures Valid()           // can be better to make this last
    {
       x := m==n;             // no elements means x is true
    }      

    method Push(x: char) modifies this, this.buf, this`m, this`n
    requires Valid();
    // code
    ensures if old(n)   == old(buf.Length) then fresh(buf) else buf==old(buf)
    ensures if old(n-m) == old(buf.Length) then buf.Length==2*old(buf.Length) else buf.Length==old(buf.Length)
    ensures 0<n<=buf.Length ==> buf[n-1]==x
    // shadow
    ensures |shadow|    == |old(shadow)|+1
    ensures   shadow    == old(shadow) + [x]; // new tail
    ensures Valid()
    {
        if n==buf.Length
        {
            var b:= new char[buf.Length];          // temporary
            if m==0 { b:= new char[2*buf.Length]; }// double size
            forall (i | 0<=i<n-m) { b[i]:= buf[m+i]; } // copy m..n to 0..n-m
            buf, m, n:= b, 0, n-m;                     // copy b to buf, reset m,n
        }
        buf[n], n:= x, n+1;         // now we definitely have room
        shadow:= shadow + [x];      // same as previous slide: concat 'x'
    }   

    method Pop() returns(x: char) modifies this, this`n
    requires Valid()
    requires  shadow != [] 
    // code
    ensures   buf    == old(buf)                  // buf name does not change 
    ensures   x      == old(buf[n-1])             // element n-1 is returned
    ensures   n      == old(n-1)                  // n moves down
    // shadow
    ensures |shadow| == |old(shadow)|-1           // popped an elem
    ensures   x      == old(shadow[|shadow|-1])   // last element
    ensures shadow   == old(shadow[..|shadow|-1]) // chop off tail
    ensures Valid()                               // check okay at end
    {
        x, n:= buf[n-1], n-1;                     // get tail, decr n
        shadow:= shadow[..|shadow|-1];            // chop tail off shadow
    }

    method TopSort() modifies this, this.buf
    requires Valid()
    ensures buf == old(buf) // pointer does not change
    ensures buf.Length == old(buf.Length) // length does not change
    ensures n == old(n)
    ensures m == old(m)
    ensures (n - m) < 2 || buf.Length < 2 ==> buf[..] == old(buf[..])
    // second element smaller than first - no change
    ensures (n - m) >= 2 && 1 < n <= buf.Length && old(buf[n - 1]) > old(buf[n - 2]) ==> buf[..] == old(buf[..]) 
    // if second element larger than first, they are swaped
    ensures (n - m) >= 2 && 1 < n <= buf.Length && old(buf[n - 1]) < old(buf[n - 2]) ==> buf[n - 1] == old(buf[n - 2]) && buf[n - 2] == old(buf[n - 1]) 
    // no change to array indexes that are not the first or second (from top stack) no matter the order of the first 2
    ensures forall i :: 0 <= i < buf.Length && i != (n - 1) && i != (n - 2) ==> buf[i] == old(buf[i]) 
    ensures multiset(buf[..]) == multiset(old(buf[..]))
    
    ensures |shadow| == |old(shadow)|
    ensures multiset(shadow[..]) == multiset(old(shadow[..]))
    // shadow size < 2 - no change
    ensures |shadow| <= 0 ==> shadow[..] == old(shadow[..])
    // correct order - no change
    ensures |shadow| > 1 && old(shadow[(|shadow| - 1)]) > old(shadow[(|shadow| - 2)]) ==> shadow[..] == old(shadow[..])
    // wrong order - new order of shadow
    ensures |shadow| > 1 && old(shadow[(|shadow| - 1)]) < old(shadow[(|shadow| - 2)]) ==> shadow[..] == old(shadow[..(|shadow| - 2)]) + old([shadow[(|shadow| - 1)]]) + old([shadow[(|shadow| - 2)]])
    ensures Valid()
    {
        if ((n - m) >= 2 && 1 < n <= buf.Length) {
            if (buf[n - 1] < buf[n - 2]) {
                buf[n - 2], buf[n - 1] := buf[n - 1], buf[n - 2];
                assert |shadow| > 1;
                shadow := shadow[(|shadow| - 1) := shadow[(|shadow| - 2)]][(|shadow| - 2) := shadow[(|shadow| - 1)]];
            }
        }
    }
} // end of Quack class


/*********************************************************************************/
method Checker()
{
    var p:char, e:bool;
    var q:= new Quack(6);

    q.Push('3');
    q.Push('2');
    q.Push('1');
    q.TopSort();
    p:= q.Pop();    assert p=='2';
    q.TopSort();
    p:= q.Pop();    assert p=='3';
    p:= q.Pop();    assert p=='1';
    e := q.Empty(); assert e;
    q.TopSort();
    e := q.Empty(); assert e;
}