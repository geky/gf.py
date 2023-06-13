#!/usr/bin/env python3

import math
import itertools as it


# some useful math operations on "normal" numbers
def factor(a):
    # handle multiples of 2 specially, since this is ~1/2 of all numbers
    if a % 2 == 0:
        if a == 2:
            return None
        else:
            return 2

    # test division of all numbers <= sqrt(a)
    for f in range(3, math.ceil(math.sqrt(a))+1, 2):
        if a % f == 0:
            return f

    return None

def factors(a):
    b = a
    while True:
        f = factor(b)
        if f is None:
            if b != a:
                yield b
            break
        else:
            yield f
            b //= f

def isprime(a):
    return factor(a) is None

def primes():
    for a in it.count(2):
        if isprime(a):
            yield a


# polynomial operations as functions
def pmul(a, b):
    x = 0
    for i in range(a.bit_length()):
        if a & (1 << i):
            x ^= b << i
    return x

def pdiv(a, b):
    assert b != 0
    b_bits = b.bit_length()
    x = 0
    while True:
        a_bits = a.bit_length()
        if a_bits < b_bits:
            return x
        x ^= 1 << (a_bits-b_bits)
        a ^= b << (a_bits-b_bits)

def pmod(a, b):
    assert b != 0
    b_bits = b.bit_length() 
    x = 0
    while True:
        a_bits = a.bit_length() 
        if a_bits < b_bits:
            return a
        a ^= b << (a_bits-b_bits)

def ppow(a, e):
    b = 1
    while True:
        if e & 1 != 0:
            b = pmul(b, a)
        e >>= 1

        if e == 0:
            return b

        a = pmul(a, a)

def pdeg(a):
    return a.bit_length()-1

def pcount(a):
    return sum(1 for i in range(a.bit_length()) if a & (1 << i))

def pfactor(a):
    # handle multiples of 2 specially, since this is ~1/2 of all polynomials
    if pmod(a, 2) == 0:
        if a == 2:
            return None
        else:
            return 2

    # test division of all polynomias <= psqrt(a), or the simpler
    # heuristic < 2^(log2(a)/2)
    for f in range(3, 1 << math.ceil(a.bit_length()/2), 2):
        if pmod(a, f) == 0:
            return f

    return None

def pfactors(a):
    b = a
    while True:
        f = pfactor(b)
        if f is None:
            if b != a:
                yield b
            break
        else:
            yield f
            b = pdiv(b, f)

def pisirreducible(a):
    return pfactor(a) is None

def pirreducibles(deg):
    # brute force really
    for a in range(1 << deg, 1 << (deg+1)):
        if pisirreducible(a):
            yield a

def pisprimitive(g, p):
    if g == 0 or g == 1:
        return False

    # define some finite-field over p operation real quick
    def gfmul(a, b):
        return pmod(pmul(a, b), p)

    def gfpow(a, e):
        b = 1
        while True:
            if e & 1 != 0:
                b = gfmul(b, a)
            e >>= 1

            if e == 0:
                return b

            a = gfmul(a, a)

    # test if g generates a multiplicative cycle m = size of our field - 1,
    # this is true when g^m = 1 and g^e != 1 for all e < m.
    #
    # however, it turns out we don't need to test all e, just e < m where
    # m/e is a prime factor of m, this is because any multiplicative group
    # must divie the largest multiplicative group evenly.
    #
    m = (1 << pdeg(p)) - 1

    # test g^e != 1 for all e < m
    for f in factors(m):
        if gfpow(g, m//f) == 1:
            return False

    # don't forget to test g^m == 1
    return gfpow(g, m) == 1

def pprimitives(p):
    # brute force really
    for g in range(1 << pdeg(p)):
        if pisprimitive(g, p):
            yield g


class P:
    """ A polynomial type """
    __slots__ = ('x',)

    def __init__(self, x):
        if isinstance(x, str):
            self.x = int(x, 0)
        else:
            self.x = x.__index__()

    # repr stuff
    def __repr__(self):
        return '%s(0x%x)' % (P.__name__, self.x)

    def __index__(self):
        return self.x

    def __bool__(self):
        return bool(self.x)

    def deg(self):
        return pdeg(self.x)

    def count(self):
        return pcount(self.x)

    # equality stuff
    def __eq__(self, other):
        return self.x == other.x

    def __hash__(self):
        return hash(self.x)

    # math stuff
    def __add__(self, other):
        return P(self.x ^ other.x)

    def __sub__(self, other):
        return P(self.x ^ other.x)

    def __and__(self, other):
        return P(self.x & other.x)

    def __or__(self, other):
        return P(self.x | other.x)

    def __xor__(self, other):
        return P(self.x ^ other.x)

    def __lshift__(self, e):
        return P(self.x << e)

    def __rshift__(self, e):
        return P(self.x >> e)

    def __mul__(self, other):
        return P(pmul(self.x, other.x))

    def __pow__(self, e):
        return P(ppow(self.x, other.x))

    def __div__(self, other):
        return P(pdiv(self.x, other.x))

    def __mod__(self, other):
        return P(pmod(self.x, other.x))

    # advanced things
    def factor(self):
        f = pfactor(self.x)
        return P(f) if f is not None else None

    def factors(self):
        for f in pfactors(self.x):
            yield P(f)

    def isirreducible(self):
        return pisirreducible(self.x)

    @staticmethod
    def irreducibles(deg):
        for f in pirreducibles(deg):
            yield P(f)

    def isprimitive(self, g):
        return pisprimitive(g.x, self.x)

    def primitives(self):
        for g in pprimitives(self.x):
            yield P(g)


def Gf(deg=None, *, p=None, g=None, name=None):
    """ Dynamically create finite-field classes """
    assert p is not None or deg is not None

    if p is None:
        # find a minimal p with degree deg and primitive element 0x2
        p = next(f
            for f in pirreducibles(deg)
            if pisprimitive(0x2, f))

        if g is None:
            g = 0x2

    p = p.__index__()
    deg = pdeg(p)

    if g is None:
        # find a primitive element
        g = next(pprimitives(p))

    g = g.__index__()

    if name is None:
        # shorthand for fields > 256
        if deg > 8:
            name = 'Gf2p%d' % deg
        else:
            name = 'Gf%d' % (2**deg)

    class Gf:
        """ A finite-field type """
        P = P(p)
        G = None # filled in below
        N = 2**deg
        M = 2**deg - 1

        __slots__ = ('x',)

        def __init__(self, x):
            self.x = P(x)
            assert self.x.__index__() < self.N

        # repr stuff
        def __repr__(self):
            return '%s(0x%x)' % (Gf.__name__, self.x)

        def __index__(self):
            return self.x.__index__()

        def __bool__(self):
            return bool(self.x)

        def count(self):
            return self.x.count()

        # equality stuff
        def __eq__(self, other):
            return self.x == other.x

        def __hash__(self):
            return hash(self.x)

        # math stuff
        def __add__(self, other):
            return Gf(self.x + other.x)

        def __sub__(self, other):
            return Gf(self.x - other.x)

        def __and__(self, other):
            return Gf(self.x & other.x)

        def __or__(self, other):
            return Gf(self.x | other.x)

        def __xor__(self, other):
            return Gf(self.x ^ other.x)

        def __mul__(self, other):
            return Gf((self.x * other.x) % self.P)

        def __pow__(self, e):
            a = self
            b = Gf(1)
            while True:
                if e & 1 != 0:
                    b *= a
                e >>= 1

                if e == 0:
                    return b

                a *= a

        def __truediv__(self, other):
            assert other.x != 0
            return self * other**(self.M-1)

    Gf.__name__ = name
    Gf.G = Gf(g)
    return Gf


# Some fields!
#
Gf16   = Gf(p=0x13, g=0x2)
Gf256  = Gf(p=0x11d, g=0x2)
Gf2p16 = Gf(p=0x1002d, g=0x2)
Gf2p32 = Gf(p=0x1000000af, g=0x2)
Gf2p64 = Gf(p=0x1000000000000001b, g=0x2)



def Crc(deg=None, *, p=None, q=None, g=None, e=None, name=None):
    """ Dynamically create CRC ring classes """
    assert p is not None or deg is not None or q is not None

    if p is None:
        if q is None:
            # find a minimal q with degree deg-1 and primitive element 0x2
            q = next(f
                for f in pirreducibles(deg-1)
                if pisprimitive(0x2, f))

            if g is None:
                g = 0x2

        # p = q*0x3, this makes our crc parity preserving
        p = pmul(q, 0x3)

    p = p.__index__()
    deg = pdeg(p)

    if q is None:
        # find q, the largest irreducible factor of p
        q = max(pfactors(p), default=p)

    q = q.__index__()

    if g is None:
        # find a primitive element in q
        g = next(pprimitives(q))

    g = g.__index__()

    if e is None:
        m = (1 << pdeg(q)) - 1
        fs = factors(m)

        # find the smallest odd number coprime with our multiplicative group
        e = next(e
            for e in range(3, m, 2)
            if all(e % f != 0 for f in fs))

    e = e.__index__()

    if name is None:
        name = 'Crc%d' % deg

    class Crc:
        """ A CRC ring type """
        Q = P(q)
        P = P(p)
        G = None # filled in below
        E = e
        N = 2**deg
        M = 2**pdeg(q) - 1

        __slots__ = ('x',)

        def __init__(self, x):
            if isinstance(x, bytes):
                self.x = Crc(0).crc(x).x
            else:
                self.x = P(x)

            assert self.x.__index__() < self.N

        def crc(self, data):
            x = self.x

            for b in data:
                x = ((x^P(b)) << 8) % self.P
                
            return Crc(x)

        # repr stuff
        def __repr__(self):
            return '%s(0x%x)' % (Crc.__name__, self.x)

        def __index__(self):
            return self.x.__index__()

        def __bool__(self):
            return bool(self.x)

        def count(self):
            return self.x.count()

        # equality stuff
        def __eq__(self, other):
            return self.x == other.x

        def __hash__(self):
            return hash(self.x)

        # math stuff
        def __add__(self, other):
            return Crc(self.x + other.x)

        def __sub__(self, other):
            return Crc(self.x - other.x)

        def __and__(self, other):
            return Crc(self.x & other.x)

        def __or__(self, other):
            return Crc(self.x | other.x)

        def __xor__(self, other):
            return Crc(self.x ^ other.x)

        def __mul__(self, other):
            return Crc((self.x * other.x) % self.P)

        def __pow__(self, e):
            a = self
            b = Crc(1)
            while True:
                if e & 1 != 0:
                    b *= a
                e >>= 1

                if e == 0:
                    return b

                a *= a

    Crc.__name__ = name
    Crc.G = Crc(g)
    return Crc


# Some CRC ring types!
#
# found from https://users.ece.cmu.edu/~koopman/crc/crc32.html
#
# note except for crc32c, these may not be standard
#
Crc4   = Crc(p=0x17, q=0xb, g=0x2, e=3)
Crc8   = Crc(p=0x17f, q=0xd5, g=0x2, e=3)
Crc16  = Crc(p=0x1a2eb, q=0x9e59, g=0x2, e=3)
Crc32c = Crc(p=0x11edc6f41, q=0xf5b4253f, g=0x2, e=3)


# some experiments
def powers(Gf=Gf16):
    nibbles = math.ceil((Gf.N.bit_length()-1) / 4)
    print(' '.join('%*s' % (nibbles+2, '^%d' % (i+1)) for i in range(Gf.M)))

    uniqs = [set() for _ in range(Gf.M)]
    for i in range(Gf.N):
        cycle = 0
        seen = set()
        for j in range(Gf.M):
            power = Gf(i)**(j+1)

            print('0x%0*x' % (nibbles, power), end=' ')
            if power not in seen:
                cycle += 1
                seen.add(power)
            uniqs[j].add(power)
        print(' %*d' % (nibbles+2, cycle))

    print('-'.join('-'*(nibbles+2) for _ in range(Gf.M)))
    print(' '.join('%*d' % (nibbles+2, len(uniqs[j])) for j in range(Gf.M)))


def gcrcs(Crc=Crc4, *, g=None):
    if g is None:
        g = Crc.G
    nibbles = math.ceil((Crc.N.bit_length()-1) / 4)

    print('%s%s' % (
        ' '*(3+nibbles+2),
        ' '.join('0x%0*x' % (nibbles, i) for i in range(Crc.N))))
    print('%s+%s>' % (
        ' '*(1+nibbles+2),
        '-'*((1+nibbles+2)*Crc.N-1)))

    i_uniqs = [set() for _ in range(Crc.N)]
    for j in range(Crc.N):
        print('0x%0*x' % (nibbles, j), end=' ')
        print('v' if j == Crc.N-1 else '|', end=' ')
        j_uniqs = set()
        for i in range(Crc.N):
            gcrc = Crc(j) + Crc(i)*g

            print('0x%0*x' % (nibbles, gcrc), end=' ')
            j_uniqs.add(gcrc)
            i_uniqs[i].add(gcrc)
        print(' %*d' % (nibbles+2, len(j_uniqs)))

    print()
    print('%s%s' % (
        ' '*(3+nibbles+2),
        ' '.join('%*d' % (nibbles+2, len(i_uniqs[i])) for i in range(Crc.N))))

def deltas(Crc=Crc4, *, g=None, e=None):
    if g is None:
        g = Crc.G
    if e is None:
        e = Crc.E
    nibbles = math.ceil((Crc.N.bit_length()-1) / 4)

    print('%s%s' % (
        ' '*(3+nibbles+2),
        ' '.join('0x%0*x' % (nibbles, i) for i in range(Crc.N))))
    print('%s+%s>' % (
        ' '*(1+nibbles+2),
        '-'*((1+nibbles+2)*Crc.N-1)))

    i_uniqs = [set() for _ in range(Crc.N)]
    for j in range(Crc.N):
        print('0x%0*x' % (nibbles, j), end=' ')
        print('v' if j == Crc.N-1 else '|', end=' ')
        j_uniqs = set()
        for i in range(Crc.N):
            gcrc = Crc(j)
            gcrc_ = Crc(j) + Crc(i)*g
            delta = gcrc_**e - gcrc**e

            print('0x%0*x' % (nibbles, delta), end=' ')
            j_uniqs.add(delta)
            i_uniqs[i].add(delta)
        print(' %*d' % (nibbles+2, len(j_uniqs)))

    print()
    print('%s%s' % (
        ' '*(3+nibbles+2),
        ' '.join('%*d' % (nibbles+2, len(i_uniqs[i])) for i in range(Crc.N))))

def entropy(Crc=Crc4, *, g=None, i=1):
    if g is None:
        g = Crc.G
    nibbles = math.ceil((Crc.N.bit_length()-1) / 4)

    best = (0, 0, 0)

    print('%*s  %*s  %*s' % (
        nibbles+2, '',
        nibbles+2, 'g',
        nibbles+2, 'd'))
    for e in range(Crc.M+1):
        g_uniqs = set()
        d_uniqs = set()
        for j in range(Crc.N):
            g_ = (Crc(i)+Crc(j)*g)**e - Crc(i)**e
            d_ = (Crc(j)+Crc(i)*g)**e - Crc(j)**e
            g_uniqs.add(g_)
            d_uniqs.add(d_)

        print('%*s: %*d  %*d' % (
            nibbles+2, '^%d' % e,
            nibbles+2, len(g_uniqs),
            nibbles+2, len(d_uniqs)))
        if (len(g_uniqs), len(d_uniqs)) > best[1:]:
            best = (e, len(g_uniqs), len(d_uniqs))

    print('-'*(3*(nibbles+2)+4))
    print('%*s: %*d  %*d' % (
        nibbles+2, '^%d' % best[0],
        nibbles+2, best[1],
        nibbles+2, best[2]))



