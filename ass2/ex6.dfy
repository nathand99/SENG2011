// verifies
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