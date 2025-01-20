import os
import sys
from io import BytesIO, IOBase
from types import GeneratorType
import math
import bisect
from collections import Counter
from collections import defaultdict
from functools import reduce
from itertools import permutations
from itertools import combinations
from itertools import combinations_with_replacement
from itertools import product


BUFSIZE = 8192
class FastIO(IOBase):
    newlines = 0
    def _init_(self, file):
        self._fd = file.fileno()
        self.buffer = BytesIO()
        self.writable = "x" in file.mode or "r" not in file.mode
        self.write = self.buffer.write if self.writable else None
    def read(self):
        while True:
            b = os.read(self._fd, max(os.fstat(self._fd).st_size, BUFSIZE))
            if not b:
                break
            ptr = self.buffer.tell()
            self.buffer.seek(0, 2), self.buffer.write(b), self.buffer.seek(ptr)
        self.newlines = 0
        return self.buffer.read()
    def readline(self):
        while self.newlines == 0:
            b = os.read(self._fd, max(os.fstat(self._fd).st_size, BUFSIZE))
            self.newlines = b.count(b"\n") + (not b)
            ptr = self.buffer.tell()
            self.buffer.seek(0, 2), self.buffer.write(b), self.buffer.seek(ptr)
        self.newlines -= 1
        return self.buffer.readline()
    def flush(self):
        if self.writable:
            os.write(self._fd, self.buffer.getvalue())
            self.buffer.truncate(0), self.buffer.seek(0)
class IOWrapper(IOBase):
    def _init_(self, file):
        self.buffer = FastIO(file)
        self.flush = self.buffer.flush
        self.writable = self.buffer.writable
        self.write = lambda s: self.buffer.write(s.encode("ascii"))
        self.read = lambda: self.buffer.read().decode("ascii")
        self.readline = lambda: self.buffer.readline().decode("ascii")
sys.stdin, sys.stdout = IOWrapper(sys.stdin), IOWrapper(sys.stdout)
input = lambda: sys.stdin.readline().rstrip("\r\n")
def print(*args, **kwargs):
    """Prints the values to a stream, or to sys.stdout by default."""
    sep, file = kwargs.pop("sep", " "), kwargs.pop("file", sys.stdout)
    at_start = True
    for x in args:
        if not at_start:
            file.write(sep)
        file.write(str(x))
        at_start = False
    file.write(kwargs.pop("end", "\n"))
    if kwargs.pop("flush", False):
        file.flush()
def gcd(a,b):
    if b==0:
        return a
    return gcd(b,a%b)
def sortByKeys(mp):
    return { i:mp[i] for i in sorted(mp.keys()) }
def sortByValues(mp):
    return { i:mp[i] for i in mp.values() }
def seive(n):
    prime=[True for i in range(n+1)]
    p=2
    while p*p<=n:
        if prime[p]==True:
            for i in range(p*p,n+1,p):
                prime[i]=False
        p+=1
    return [x for x in range(2,n) if prime[x]]
def isPrime(n):
    if n<=1:
        return False
    if n<=3:
        return True
    if n%2==0 or n%3==0:
        return False
    i=5
    while i*i<=n:
        if n%i==0 or n%(i+2)==0:
            return False
        i+=6
    return True
def primeFactors(n):
    factors = {}
    while n % 2 == 0:
        if 2 in factors:
            factors[2] += 1
        else:
            factors[2] = 1
        n = n // 2
    for i in range(3,int(n**0.5)+1,2):
        while n % i== 0:
            if i in factors:
                factors[i] += 1
            else:
                factors[i] = 1
            n = n // i
    if n > 2:
        factors[n] = 1
    return factors
def factors(n):
    fact = []
    for i in range(1, int(n**0.5) + 1):
        if n % i == 0:
            if n // i == i:
                fact.append(i)
            else:
                fact.append(i)
                fact.append(n//i)
    return fact
def zAlgorithm(text,pattern):
    ans = []
    z = pattern + "$" + text
    n = len(z)
    l,r = 0,0
    z = [0]*n
    for i in range(1,n):
        if i <= r:
            z[i] = min(r-i+1,z[i-l])
        while i + z[i] < n and z[i] + i < len(pattern) and z[i] == pattern[z[i]+i]:
            z[i] += 1
        if i + z[i] - 1 > r:
    
            l = i
            r = i + z[i] - 1
        if z[i] == len(pattern):
            ans.append(i-len(pattern)-1)
    return ans
def kmp(text,pattern):
    ans = []
    n = len(text)
    m = len(pattern)
    lps = [0]*m
    j = 0
    i = 1
    while i < m:
        if pattern[i] == pattern[j]:
            j += 1
            lps[i] = j
            i += 1
        else:
            if j != 0:
                j = lps[j-1]
            else:
                lps[i] = 0
                i += 1
    i = 0
    j = 0
    while i < n:
        if pattern[j] == text[i]:
            i += 1
            j += 1
        if j == m:
            ans.append(i-j)
            j = lps[j-1]
        elif i < n and pattern[j] != text[i]:
            if j != 0:
                j = lps[j-1]
            else:
                i += 1
    return ans
def segmentTree(arr):
    n = len(arr)
    tree = [0]*(4*n)
    def build(node,start,end):
        if start == end:
            tree[node] = arr[start]
        else:
            mid = (start+end)//2
            build(2*node,start,mid)
            build(2*node+1,mid+1,end)
            tree[node] = tree[2*node] + tree[2*node+1]
    def update(node,start,end,idx,val):
        if start == end:
            arr[idx] = val
            tree[node] = val
        else:
            mid = (start+end)//2
            if start <= idx <= mid:
                update(2*node,start,mid,idx,val)
            else:
                update(2*node+1,mid+1,end,idx,val)
            tree[node] = tree[2*node] + tree[2*node+1]
    def query(node,start,end,l,r):
        if r < start or end < l:
            return 0
        if l <= start and end <= r:
            return tree[node]
        mid = (start+end)//2
        p1 = query(2*node,start,mid,l,r)
        p2 = query(2*node+1,mid+1,end,l,r)
        return p1 + p2
    build(1,0,n-1)
    return [build,update,query]
def binarySearch(arr,x):
    l,r = 0,len(arr)-1
    while l <= r:
        mid = (l+r)//2
        if arr[mid] == x:
            return mid
        elif arr[mid] < x:
            l = mid + 1
        else:
            r = mid - 1
    return -1
def isPalindrome(s):
    return s == s[::-1]
def isVowel(ch):
    return ch in ['A','E','I','O','U','a','e','i','o','u']
def isConsonant(ch):
    return not isVowel(ch)
def isPowerOfTwo(n):
    return (n & (n-1)) == 0
def isPerfectSquare(n):
    return n*0.5 == int(n*0.5)
def isPerfectCube(n):
    return n*(1/3) == int(n*(1/3))
def upperBound(arr,x):
    l,r = 0,len(arr)
    while l < r:
        mid = (l+r)//2
        if arr[mid] <= x:
            l = mid + 1
        else:
            r = mid
    return l
def lowerBound(arr,x):
    l,r = 0,len(arr)
    while l < r:
        mid = (l+r)//2
        if arr[mid] < x:
            l = mid + 1
        else:
            r = mid
    return l
def range_bitwise_or(a, b):
    if a == b:
        return a
    result = a | b
    mask = 1
    while mask <= b - a:
        result |= mask
        mask <<= 1
    return result


def solve():
    # n=int(input())
    n,m=map(int,input().split())
    # arr=list(map(int,input().split()))
    st=n-m
    if st<0:
        st=0
    en=n+m
    # print(st,en)
    return range_bitwise_or(st,en)
    
for _ in range(int(input())):
    print(solve())