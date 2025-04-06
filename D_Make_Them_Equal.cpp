// Author : Sarbojit Rana
// LinkTree : https://linktr.ee/sarbojit_rana

#include <bits/stdc++.h>
#include <complex>
#include <queue>
#include <set>
#include <unordered_set>
#include <list>
#include <chrono>
#include <random>
#include <iostream>
#include <algorithm>
#include <cmath>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <stack>
#include <iomanip>
#include <fstream>

using namespace std;

typedef long long ll;
typedef long double ld;
typedef pair<int,int> pii;
typedef pair<ll,ll> pll;
typedef pair<double,double> pdd;
typedef vector<ll> vll;
typedef vector<int> vi;
typedef vector<vector<int>> vvi;
typedef vector<vector<ll>> vvll;
typedef vector<vector<pll>> vvpll;
typedef vector<pll> vpll;
typedef vector<pii> vpii;
typedef map<int, int> mii;
typedef map<ll,ll> mll;

const ll MOD = 998244353;
const double eps = 1e-12;

#define forn(i,e) for(ll i = 0; i < e; i++)
#define forsn(i,s,e) for(ll i = s; i < e; i++)
#define rforn(i,s) for(ll i = s; i >= 0; i--)
#define rforsn(i,s,e) for(ll i = s; i >= e; i--)
#define ln "\n"
#define MEM(a, b) memset(a, (b), sizeof(a))
#define dbg(x) cout<<#x<<" = "<<x<<ln
#define mp make_pair
#define pb push_back
#define fi first
#define se second
#define INF 2e18
#define fast_cin() ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL)
#define all(x) (x).begin(), (x).end()
#define sz(x) ((ll)(x).size())
#define yes cout << "YES\n" ;
#define no cout << "NO\n" ;
#define iv(v,n) vector<ll> v(n); forn(i,n) cin >> v[i] ;

// unique sort :
// sort(all(v));
// v.resize(unique(all(v)) - v.begin());

// Mathematical functions
ll gcd(ll a, ll b){if (b == 0)return a;return gcd(b, a % b);} //__gcd

ll lcm(ll a, ll b){return (a/gcd(a,b)*b);}

ll moduloMultiplication(ll a,ll b,ll mod){
    ll res = 0;
    a %= mod;
    while (b){
        if (b & 1)
            res = (res + a) % mod;
        b >>= 1;
        a = (a + a) % mod;
    }
    return res;
}

ll powermod(ll x, ll y, ll p){
    ll res = 1;
    x = x % p;
    if (x == 0) return 0;
    while (y > 0){
        if (y & 1)
            res = (res*x) % p;
        y = y >> 1;
        x = (x*x) % p;
    }
    return res;
}

ll binexp(ll a, ll b, ll m){
    ll result = 1;
    while(b > 0){
        if(b & 1){
            result = ((result % m) * (a % m)) % m;
        }
        a = ((a % m) * (a % m)) % m;
        b >>= 1;
    }
    return result;
}

int phi(int n) {
    int result = n;
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            while (n % i == 0)
                n /= i;
            result -= result / i;
        }
    }
    if (n > 1)
        result -= result / n;
    return result;
}

void phi_1_to_n(int n) {
    vector<int> phi(n + 1);
    for (int i = 0; i <= n; i++)
        phi[i] = i;

    for (int i = 2; i <= n; i++) {
        if (phi[i] == i) {
            for (int j = i; j <= n; j += i)
                phi[j] -= phi[j] / i;
        }
    }
}

vector<vector<long long>> matrixmultiply(
    const vector<vector<long long>>& matrix1,
    const vector<vector<long long>>& matrix2
) {
    int rows = matrix1.size();
    int cols = matrix2[0].size();
    int common = matrix2.size();
    vector<vector<long long>> result(rows, vector<long long>(cols, 0));

    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            for (int k = 0; k < common; k++) {
                result[i][j] += matrix1[i][k] * matrix2[k][j];
            }
        }
    }
    return result;
}

//Factorial by vector
//vll fact;
//void factorials(ll mod, ll maxi){
//    fact.resize(maxi + 1, 1);
//    for(int i = 2; i <= maxi; i++) fact[i] = (fact[i-1]*i) % mod;
//}
//ll nCr(ll n, ll r, ll mod){
//    if(r > n) return 0;
//    ll x = (fact[r] * fact[n-r]) % mod;
//    ll ans = (fact[n] * (powermod(x, mod-2, mod))) % mod;
//    return ans;
//}

bool isPrime(ll n){
    if(n <= 1) return false;
    if(n <= 3) return true;
    if(n % 2 == 0 || n % 3 == 0) return false;
    for(int i = 5; i * i <= n; i = i + 6)
        if(n % i == 0 || n % (i + 2) == 0) return false;
    return true;
}

bool isPowerOfTwo(int n){
    if(n == 0) return false;
    return (ceil(log2(n)) == floor(log2(n)));
}

bool isPerfectSquare(ll x){
    if (x >= 0) {
        ll sr = sqrt(x);
        return (sr * sr == x);
    }
    return false;
}

vll val(1e4 + 1, INT_MAX) ;

void precompute(ll n){
    val[1] = 0;
    for(ll i =  1; i<= n; i++){
        ll temp = val[i] ;
        for(ll j = 1 ; j<= i ;j++){
            val[i + i/ j] = min( val[i+ i/j], 1 + temp) ;
        }
    }
}


void solve() {
    ll n,k, sum = 0;
    cin >> n >> k;
    vll b(n, 0) , c(n, 0) ;
    forn(i, n){
        cin >> b[i] ;
        sum += val[b[i]] ;
    } 
    forn(i, n) cin >> c[i] ;
    vll v(n, 0);
    forn(i, n) v[i] = val[b[i]] ;

    ll m = min(k , sum) ;
    vll prev(m + 1, 0) ;
    for(ll i = v[0] ; i <= m ; i++){
        prev[i] = c[0] ;
    }
    for(ll i= 1; i < n ; i++){
        vll curr(m + 1, 0) ;
        for(ll j = 0; j<= m ;j++){
            curr[j] = prev[j] ;
            if( j >= v[i] ){
                curr[j] = max(curr[j] , c[i] + prev[j - v[i]]) ;
            }
        }
        prev = curr ;
    }

    cout << prev[m] << endl;
}

int main() {
    fast_cin();
    precompute(1000) ;

    ll t;
    cin >> t;
    for(int it = 1; it <= t; it++) {
        solve();
    }
    return 0;
}