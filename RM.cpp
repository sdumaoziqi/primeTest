#include <iostream>
#include <fstream>
#include <algorithm>
#include <map>
#include <vector>
#include <set>
#include <queue>
#include <utility>
#include <random>
#include <chrono>
#include <string>
using namespace std;

#define forn(i,n) for (int i=0;i<(int)(n);i++)
#define dforn(i,n) for(int i=(int)((n)-1);i>=0;i--)
typedef long long tint;
typedef tint tipo;
#define BASEXP 6
#define BASE 1000000
#define LMAX 200  

struct Long {
	int l;
	tipo n[LMAX];
	Long(tipo x) { l = 0; forn(i, LMAX) { n[i]=x%BASE; l+=!!x||!i; x/=BASE;} }
	Long(){*this = Long(0);}
	Long(string x) {
		l=(x.size()-1)/BASEXP+1;
		fill(n, n+LMAX, 0);
		tipo r=1;
		forn(i, x.size()){
			n[i / BASEXP] += r * (x[x.size()-1-i]-'0');
			r*=10; if(r==BASE)r=1;
		}
	}
};
void out(Long& a) {

	char msg[BASEXP+1];
	cout << a.n[a.l-1];
	dforn(i, a.l-1) {
		sprintf(msg, "%6.6llu", a.n[i]); cout << msg; // 6 = BASEXP!
	}
	cout << endl;
}
void invar(Long &a) {
	fill(a.n+a.l, a.n+LMAX, 0);
	while(a.l>1 && !a.n[a.l-1]) a.l--;
}
void lsuma(const Long&a, const Long&b, Long &c) { // c = a + b
	c.l = max(a.l, b.l);
	tipo q = 0;
	forn(i, c.l) q += a.n[i]+b.n[i], c.n[i]=q%BASE, q/=BASE;
	if(q) c.n[c.l++] = q;
	invar(c);
}
Long& operator+= (Long&a, const Long&b) { lsuma(a, b, a); return a; }
Long operator + (const Long&a, const Long&b) { Long c; lsuma(a, b, c); return c;}
bool lresta(const Long&a, const Long&b, Long&c) { // c = a - b
	c.l = max(a.l, b.l);
	tipo q = 0;
	forn(i, c.l) q += a.n[i] - b.n[i], c.n[i]=(q+BASE)%BASE, q=(q+BASE)/BASE-1;
	invar(c);
	return !q;
}
Long& operator-= (Long&a, const Long&b) { lresta(a, b, a); return a;}
Long operator- (const Long&a, const Long&b) {Long c; lresta(a, b, c); return c;}
bool operator< (const Long&a, const Long&b) { Long c; return !lresta(a, b, c); }
bool operator<= (const Long&a, const Long&b) { Long c; return lresta(b, a, c); }
bool operator== (const Long&a, const Long&b) { return a <= b && b <= a; }
void lmul(const Long&a, const Long&b, Long&c) { // c = a * b
	c.l = a.l+b.l;
	fill(c.n, c.n+c.l, 0);
	forn(i, a.l) {
		tipo q = 0;
		forn(j, b.l) q += a.n[i]*b.n[j]+c.n[i+j], c.n[i+j] = q%BASE, q/=BASE;
		c.n[i+b.l] = q;
	}
	invar(c);
}
Long& operator*= (Long&a, const Long&b) { Long c; lmul(a, b, c); return a=c; }
Long operator* (const Long&a, const Long&b) { Long c; lmul(a, b, c); return c; }
void lmul (const Long&a, tipo b, Long&c) { // c = a * b
	tipo q = 0;
	forn(i, a.l) q+= a.n[i]*b, c.n[i] = q%BASE, q/=BASE;
	c.l = a.l;
	while(q) c.n[c.l++] = q%BASE, q/=BASE;
	invar(c);
}
Long& operator*= (Long&a, tipo b) { lmul(a, b, a); return a; }
Long operator* (const Long&a, tipo b) { Long c = a; c*=b; return c; }
void ldiv(const Long& a, tipo b, Long& c, tipo& rm) { // c = a / b; rm = a % b
	rm = 0;
	dforn(i, a.l) {
		rm = rm * BASE + a.n[i];
		c.n[i] = rm / b; rm %= b;
	}
	c.l = a.l;
	invar(c);
}
Long operator/ (const Long&a, tipo b) { Long c; tipo r; ldiv(a, b, c, r); return c;}
Long operator% (const Long&a, tipo b) { Long c; tipo r; ldiv(a, b, c, r); return r;}
void ldiv(const Long& a, const Long& b, Long& c, Long& rm) { // c = a / b; rm = a % b
	rm = 0;
	dforn(i, a.l) {
		if (rm.l == 1 && rm.n[0] == 0) {
			rm.n[0] = a.n[i];
		}
		else {
			dforn(j, rm.l) rm.n[j+1] = rm.n[j];
			rm.n[0] = a.n[i]; rm.l++;
		}
		tipo q = rm.n[b.l] * BASE + rm.n[b.l-1];
		tipo u = q / (b.n[b.l-1] + 1);
		tipo v = q / b.n[b.l-1] + 1;
		while (u < v-1) {
			tipo m = (u+v)/2;
			if (b*m <= rm) u=m; else v = m;
		}
		c.n[i] = u;
		rm -= b*u;
	}
	c.l = a.l;
	invar(c);
}
Long operator/ (const Long&a, const Long& b) { Long c,r; ldiv(a, b, c, r); return c;}
Long operator% (const Long&a, const Long& b) { Long c,r; ldiv(a, b, c, r); return r;}

typedef Long ll;

ll gcd (ll a, ll b) { 
	ll t;
	while (!(b == 0)) {
		t = b;
		b = a % b;
		a = t;
	}
	return a;
}

ll modexp(ll a, ll b, ll n) {
	ll c = 1;
	while (!(b <= 1)) {
		if (b % 2 == 0) {
			a *= a;
			a = a % n;
			b = b / 2;
		}
		else {
			c = c * a;
			c = c % n;
			b = b - 1;
		}
	}
	return (a * c) % n;
}

bool isprime (ll n, int rounds) { //rounds次数
	unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
	mt19937 g1 (seed);
	uniform_int_distribution<tipo> distribution(0, BASE-1);
	vector <ll> bases(rounds);
	for (int c = 0; c < rounds; c++) {
		bases[c].l = n.l;
		forn(i, n.l) {
			bases[c].n[i] = distribution(g1);
		}
		invar(bases[c]);
		if (n <= bases[c]) c--;
	}
	if (n == 2) return true;
	if (n == 1 || n % 2 == 0) return false;
	ll d, x, b;
	tipo k;
	tipo s = 0;
	d = n - 1;
	while (d % 2 == 0) {
		s = s + 1;
		d = d / 2;
	}
	for (int c = 0; c < rounds; c++) {
		b = bases[c];
		if (n <= b) continue;
		if (!(gcd(b,n) == 1)) {
			if (b == n) continue;
			else return false;
		}
		x = modexp(b,d,n);
		if ((x == 1) || (x == n -1)) continue;
		for(k = 1; k < s; k++) {
			x = (x*x) % n;
			if (x == n-1) break;
			if (x == 1) return false;
		}
		if (k == s) return false;
		if (s == 1 && !(x == n - 1)) return false;
	}
	return true;
}

int primes[] = {
         2,    3,    5,    7,   11,   13,   17,   19,
        23,   29,   31,   37,   41,   43,   47,   53,
        59,   61,   67,   71,   73,   79,   83,   89,
        97,  101,  103,  107,  109,  113,  127,  131,
       137,  139,  149,  151,  157,  163,  167,  173,
       179,  181,  191,  193,  197,  199,  211,  223,
       227,  229,  233,  239,  241,  251,  257,  263,
       269,  271,  277,  281,  283,  293,  307,  311,
       313,  317,  331,  337,  347,  349,  353,  359,
       367,  373,  379,  383,  389,  397,  401,  409,
       419,  421,  431,  433,  439,  443,  449,  457,
       461,  463,  467,  479,  487,  491,  499,  503,
       509,  521,  523,  541,  547,  557,  563,  569,
       571,  577,  587,  593,  599,  601,  607,  613,
       617,  619,  631,  641,  643,  647,  653,  659,
       661,  673,  677,  683,  691,  701,  709,  719,
       727,  733,  739,  743,  751,  757,  761,  769,
       773,  787,  797,  809,  811,  821,  823,  827,
       829,  839,  853,  857,  859,  863,  877,  881,
       883,  887,  907,  911,  919,  929,  937,  941,
       947,  953,  967,  971,  977,  983,  991,  997,
      1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
      1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097,
      1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
      1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
      1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283,
      1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321,
      1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
      1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459,
      1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
      1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571,
      1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619,
      1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693,
      1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747,
      1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
      1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877,
      1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949,
      1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003,
      2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069,
      2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
      2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203,
      2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267,
      2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311,
      2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377,
      2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423,
      2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503,
      2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579,
      2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
      2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693,
      2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
      2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801,
      2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861,
      2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939,
      2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011,
      3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079,
      3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167,
      3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221,
      3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301,
      3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347,
      3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
      3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491,
      3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541};

bool easyCheckIsPrime(int n) {
	for(int i = 0; i < sizeof(primes) / sizeof(primes[0]); ++i) {
		if(n % primes[i] == 0) {
			return false;
		}
	}
	return true;
}

// int main() {
// 	int t;
// 	int LOW = 961748941;
// 	int i = LOW;
// 	const int LIMIT = 100000;
// 	string s;
// 	int round = 10;
// 	int cnt = 0;
 
// 	while( i++ < LOW + LIMIT ) {
// 		// if(i % 1000 == 0) cout << i << endl;
// 		if(! easyCheckIsPrime(i)) continue;
// 		s = to_string(i);
// 		ll N(s);
		
// 		if (isprime(N, round)) {
// 			// cout << "YES " << endl;
// 			// out(N);
// 			cnt++;
// 		} else {
// 			// cout << "NO" << endl;
// 		}
// 	}
// 	cout << "cnt: " << cnt << endl;
// 	return 0;
// }



int main() {
	int t;
	int i = 0;
	const int LIMIT = 1000;
	int index = 0;
	string s;
	int round = 10;

	ifstream fin("primelist.txt");  
	while( i++ < LIMIT && getline(fin,s) ) {
		s = s.substr(0, s.length()-1);  //删除换行符
		cout << s << endl;
		ll N(s);
		out(N);
		if (! isprime(N, round)) cout << "NO" << endl;
		else cout << "YES" << endl;
	}

	return 0;
}



// int main() {
// 	int t;
// 	string s;
// 	cin >> t;
// 	forn(i, t) {
// 		cin >> s;
// 		ll N(s);
// 		if (isprime(N, 10)) cout << "YES" << endl; // Modify the '10' parameter to alter the ammount of RM rounds
// 		else cout << "NO" << endl;
// 	}
// 	return 0;
// }
