#include <iostream>
#include <cstring>

using namespace std;
typedef long long treetype;
const int MAXN = static_cast<const int> ( 1e6 + 5 );
int n, a[MAXN];
int MOD;

treetype sgt_query(int lft, int rht, int rt, int l, int r);

void sgt_update(int lft, int rht, int mul, int add, int rt, int l, int r);

treetype sgt_get_val(int rt);

struct edge {
    int t, n;
} es[MAXN];


int g[MAXN * 2];
int len;

void addedge(int a, int b) {
    es[++len].t = b;
    es[len].n = g[a];
    g[a] = len;
}


int wt[MAXN], fat[MAXN], dep[MAXN], siz[MAXN], hvy[MAXN], id[MAXN], top[MAXN], cnt;


#define childs_in(root, j) for(int j##_ = g[root], j; j = es[j##_].t, j##_; j##_ = es[j##_].n)

void tcd_dfs1(int x, int f, int depth) {
    dep[x] = depth;
    fat[x] = f;
    siz[x] = 1;
    hvy[x] = 0;
    childs_in (x, s) {
        if (s == fat[x]) continue;
        tcd_dfs1(s, x, depth + 1);
        siz[x] += siz[s];
        if (!hvy[x] || siz[s] > siz[hvy[x]])
            hvy[x] = s;
    }
}


void tcd_dfs2(int x, int top_father) {
    id[x] = ++cnt;
    wt[cnt] = a[x];
    top[x] = top_father;
    if (hvy[x]) {
        tcd_dfs2(hvy[x], top_father);
        childs_in(x, s) {
            if (fat[x] == s || hvy[x] == s) continue;
            tcd_dfs2(s, s);
        }

    }
}


treetype tcd_query_sum(int x, int y) {
    treetype sum = 0;
    while (top[x] != top[y]) {
        if (dep[top[x]] < dep[top[y]])
            swap(x, y);
        (sum += sgt_query(id[top[x]], id[x], 1, 1, n)) %= MOD;
        x = fat[top[x]];
    }
    if (dep[x] > dep[y]) {
        swap(x, y);
    };
    return (sgt_query(id[x], id[y], 1, 1, n) + sum) % MOD;
}

void tcd_update(int x, int y, int mul, int add) {
    while (top[x] != top[y]) {
        if (dep[top[x]] < dep[top[y]])
            swap(x, y);
        sgt_update(id[top[x]], id[x], mul, add, 1, 1, n);
        x = fat[top[x]];
    }
    if (dep[x] > dep[y])
        swap(x, y);

    sgt_update(id[x], id[y], mul, add, 1, 1, n);
}


treetype tcd_query_son(int x) {
    return sgt_query(id[x], id[x] + siz[x] - 1, 1, 1, n);
}

void tcd_update_son(int x, int mul, int add) {
    return sgt_update(id[x], id[x] + siz[x] - 1, mul, add, 1, 1, n);
}


// segment tree part
treetype sum[MAXN * 4], lz_add[MAXN * 4], lz_mul[MAXN * 4];
#define ls rt<<1
#define rs rt<<1|1
#define lson ls,l,mid
#define rson rs,mid+1,r
#define md int mid = (l + r) >> 1;

inline void sgt_init_lazy(int rt) {
    lz_mul[rt] = 1;
}

inline void sgt_set_val(int rt, int x) {
    sum[rt] = wt[x];
}

treetype sgt_get_val(int rt) {
    return sum[rt];
}

inline void sgt_pushup(int rt) {
    sum[rt] = (sum[ls] + sum[rs]) % MOD;
}

inline void sgt_change_node(int rt, int l, int r, treetype add, treetype mul) {
    if (mul != 1) {
        sum[rt] = sum[rt] * mul % MOD;
        lz_mul[rt] = lz_mul[rt] * mul % MOD;
        lz_add[rt] = lz_add[rt] * mul % MOD;
    }
    if (add) {
        sum[rt] = (sum[rt] + add * (r - l + 1)) % MOD;
        lz_add[rt] = (lz_add[rt] + add) % MOD;
    }
}

inline void sgt_pushdown(int rt, int l, int r) {
    if (lz_add[rt] || lz_mul[rt] != 1) {
        md;
        sgt_change_node(lson, lz_add[rt], lz_mul[rt]);
        sgt_change_node(rson, lz_add[rt], lz_mul[rt]);
        lz_add[rt] = 0;
        lz_mul[rt] = 1;
    }
}

void sgt_build(int rt, int l, int r) {
    sgt_init_lazy(rt);
    if (l == r) {
        sgt_set_val(rt, l);
        return;
    }
    md;
    if (l <= mid)
        sgt_build(lson);
    if (r > mid)
        sgt_build(rson);
    sgt_pushup(rt);
}

treetype sgt_query(int lft, int rht, int rt, int l, int r) {
    if (lft <= l && r <= rht) {
        return sgt_get_val(rt);
    }
    sgt_pushdown(rt, l, r);
    treetype sum = 0;
    md;
    if (lft <= mid)
        sum += sgt_query(lft, rht, lson);
    if (rht > mid)
        sum += sgt_query(lft, rht, rson);
    return sum % MOD;
}


// first mul second add
void sgt_update(int lft, int rht, int mul, int add, int rt, int l, int r) {
    if (lft <= l && r <= rht) {
        sgt_change_node(rt, l, r, add, mul);
        return;
    }
    sgt_pushdown(rt, l, r);
    md;
    if (lft <= mid) sgt_update(lft, rht, mul, add, lson);
    if (rht > mid) sgt_update(lft, rht, mul, add, rson);
    sgt_pushup(rt);
}

inline void tcd_init(int r, int n)
{
    tcd_dfs1(r, 0, 1);
    tcd_dfs2(r, r);
    sgt_build(1, 1, n);

}
int main() {
    int m, r;
    cin >> n >> m >> r >> MOD;
    for (int i = 1; i <= n; ++i)
        cin >> a[i];
    for (int i = 0; i < n - 1; ++i) {
        int a, b;
        cin >> a >> b;
        addedge(a, b);
        addedge(b, a);
    }

    tcd_init(r, n);

    for (int i = 0; i < m; ++i) {
        int t, a, b, c;
        cin >> t;
        switch (t) {
            case 1:
                cin >> a >> b >> c;
                tcd_update(a, b, 1, c);
                break;
            case 2:
                cin >> a >> b;
                cout << "<<:" << tcd_query_sum(a, b) << endl;
                break;
            case 3:
                cin >> a >> b;
                tcd_update_son(a, 1, b);
                break;
            case 4:
                cin >> a;
                cout << "<<:" << tcd_query_son(a) << endl;
                break;
            default:
                exit(-1);
        }
    }
    return 0;
}
