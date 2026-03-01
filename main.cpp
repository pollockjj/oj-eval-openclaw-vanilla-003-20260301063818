#pragma GCC optimize("O2,unroll-loops")
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <string>
using namespace std;

// Fast I/O
static char buf_in[1 << 22];
static int buf_in_pos = 0, buf_in_len = 0;
inline char gc() {
    if (buf_in_pos == buf_in_len) {
        buf_in_len = fread(buf_in, 1, sizeof(buf_in), stdin);
        buf_in_pos = 0;
        if (!buf_in_len) return EOF;
    }
    return buf_in[buf_in_pos++];
}
inline void readstr(char* s) {
    char c = gc();
    while (c <= ' ') c = gc();
    int i = 0;
    while (c > ' ') { s[i++] = c; c = gc(); }
    s[i] = 0;
}
inline int readint() {
    char c = gc();
    while (c < '0' || c > '9') c = gc();
    int x = 0;
    while (c >= '0' && c <= '9') { x = x * 10 + c - '0'; c = gc(); }
    return x;
}

static char buf_out[1 << 22];
static int buf_out_pos = 0;
inline void flush_out() { fwrite(buf_out, 1, buf_out_pos, stdout); buf_out_pos = 0; }
inline void pc(char c) {
    if (buf_out_pos == (int)sizeof(buf_out)) flush_out();
    buf_out[buf_out_pos++] = c;
}
inline void ps(const char* s) { while (*s) pc(*s++); }
inline void pint(int x) {
    if (x == 0) { pc('0'); return; }
    char tmp[12]; int len = 0;
    while (x > 0) { tmp[len++] = '0' + x % 10; x /= 10; }
    for (int i = len - 1; i >= 0; i--) pc(tmp[i]);
}

const int MAXN = 10001;
const int MAXM = 26;
const int HASH_SIZE = (1 << 17);
const int HASH_MASK = HASH_SIZE - 1;

int num_teams = 0;
char team_names[MAXN][22];

// Hash map
int hash_next[MAXN];
int hash_heads[HASH_SIZE];
int hash_count = 0;

inline unsigned hashStr(const char* s) {
    unsigned h = 0;
    while (*s) h = h * 131 + *s++;
    return h & HASH_MASK;
}
inline int findTeam(const char* s) {
    for (int i = hash_heads[hashStr(s)]; i != -1; i = hash_next[i])
        if (strcmp(team_names[i], s) == 0) return i;
    return -1;
}
inline void insertTeam(const char* s, int id) {
    unsigned h = hashStr(s);
    hash_next[id] = hash_heads[h];
    hash_heads[h] = id;
}

// Problem status - keep it small
struct ProbStatus {
    short attempts = 0;
    int ac_time = 0;
    bool solved = false;
    bool is_frozen = false;
    short frozen_count = 0;
    short pre_freeze_attempts = 0;
    bool pre_freeze_solved = false;
    bool has_frozen_ac = false;
};

ProbStatus prob[MAXN][MAXM];

// Frozen submissions stored separately
struct FzSub { int time; bool accepted; };
vector<FzSub> frozen_subs[MAXN][MAXM]; // only allocated when needed

struct SubRecord { int problem; int status; int time; };
vector<SubRecord> team_subs[MAXN];
int last_sub[MAXN][28][5];

int scoreboard[MAXN];
int last_flush_rank[MAXN];
int problem_count = 0;

// Sort key with packed fast comparison
struct SortKey {
    unsigned long long fast_key; // (26-solved)<<32 | penalty
    int nsolved;
    int stimes[MAXM];
    int nrank;
    int solved_count, penalty;
} keys[MAXN];

bool key_dirty[MAXN];

inline bool keyLess(int a, int b) {
    if (keys[a].fast_key != keys[b].fast_key) return keys[a].fast_key < keys[b].fast_key;
    int n = keys[a].nsolved;
    for (int i = 0; i < n; i++)
        if (keys[a].stimes[i] != keys[b].stimes[i]) return keys[a].stimes[i] < keys[b].stimes[i];
    return keys[a].nrank < keys[b].nrank;
}

void computeKey(int tid) {
    auto& k = keys[tid];
    int sc = 0, pen = 0;
    for (int j = 0; j < problem_count; j++) {
        auto& p = prob[tid][j];
        if (p.solved && !p.is_frozen) {
            pen += 20 * p.attempts + p.ac_time;
            k.stimes[sc++] = p.ac_time;
        }
    }
    k.nsolved = sc;
    k.solved_count = sc;
    k.penalty = pen;
    k.fast_key = ((unsigned long long)(26 - sc) << 32) | (unsigned)pen;
    if (sc > 1) sort(k.stimes, k.stimes + sc, [](int a, int b){ return a > b; });
    key_dirty[tid] = false;
}

const char* status_strs[] = {"Accepted", "Wrong_Answer", "Runtime_Error", "Time_Limit_Exceed"};
inline int parseStatus(const char* s) {
    if (s[0] == 'A') return 0;
    if (s[0] == 'W') return 1;
    if (s[0] == 'R') return 2;
    return 3;
}

void printTeam(int pos) {
    int tid = scoreboard[pos];
    ps(team_names[tid]); pc(' ');
    pint(pos + 1); pc(' ');
    pint(keys[tid].solved_count); pc(' ');
    pint(keys[tid].penalty);
    for (int j = 0; j < problem_count; j++) {
        pc(' ');
        auto& p = prob[tid][j];
        if (p.is_frozen) {
            if (p.pre_freeze_attempts == 0) {
                pc('0'); pc('/'); pint(p.frozen_count);
            } else {
                pc('-'); pint(p.pre_freeze_attempts);
                pc('/'); pint(p.frozen_count);
            }
        } else if (p.solved) {
            pc('+');
            if (p.attempts > 0) pint(p.attempts);
        } else {
            if (p.attempts == 0) pc('.');
            else { pc('-'); pint(p.attempts); }
        }
    }
    pc('\n');
}

bool unfreezeProb(int tid, int fp) {
    auto& p = prob[tid][fp];
    p.is_frozen = false;
    bool new_solve = false;
    auto& fz = frozen_subs[tid][fp];
    for (auto& fs : fz) {
        if (!p.solved) {
            if (fs.accepted) { p.solved = true; p.ac_time = fs.time; new_solve = true; }
            else p.attempts++;
        }
    }
    p.frozen_count = 0;
    p.has_frozen_ac = false;
    fz.clear();
    return new_solve;
}

int main() {
    memset(last_sub, -1, sizeof(last_sub));
    memset(key_dirty, true, sizeof(key_dirty));
    memset(hash_heads, -1, sizeof(hash_heads));
    
    bool started = false;
    bool frozen_state = false;
    
    char cmd[32], a1[32], a2[32], a3[32], a4[32], a5[32], a6[32];
    
    while (true) {
        readstr(cmd);
        
        if (cmd[0] == 'A' && cmd[1] == 'D') {
            readstr(a1);
            if (started) { ps("[Error]Add failed: competition has started.\n"); }
            else if (findTeam(a1) >= 0) { ps("[Error]Add failed: duplicated team name.\n"); }
            else {
                int id = num_teams++;
                strcpy(team_names[id], a1);
                insertTeam(a1, id);
                ps("[Info]Add successfully.\n");
            }
        } else if (cmd[0] == 'S' && cmd[1] == 'T' && cmd[2] == 'A') {
            readstr(a1); int dur = readint(); (void)dur;
            readstr(a1); int pc_ = readint();
            if (started) { ps("[Error]Start failed: competition has started.\n"); }
            else {
                started = true;
                problem_count = pc_;
                int ids[MAXN];
                for (int i = 0; i < num_teams; i++) ids[i] = i;
                sort(ids, ids + num_teams, [](int a, int b) {
                    return strcmp(team_names[a], team_names[b]) < 0;
                });
                for (int i = 0; i < num_teams; i++) {
                    keys[ids[i]].nrank = i;
                    scoreboard[i] = ids[i];
                    last_flush_rank[ids[i]] = i + 1;
                }
                for (int i = 0; i < num_teams; i++) computeKey(i);
                ps("[Info]Competition starts.\n");
            }
        } else if (cmd[0] == 'S' && cmd[1] == 'U') {
            readstr(a1); int pj = a1[0] - 'A';
            readstr(a2); readstr(a3); readstr(a4); readstr(a5); readstr(a6);
            int time = readint();
            int tid = findTeam(a3);
            int st = parseStatus(a5);
            
            int idx = team_subs[tid].size();
            team_subs[tid].push_back({pj, st, time});
            last_sub[tid][pj + 1][st] = idx;
            last_sub[tid][pj + 1][4] = idx;
            last_sub[tid][0][st] = idx;
            last_sub[tid][0][4] = idx;
            
            auto& ps_ = prob[tid][pj];
            if (ps_.solved) {}
            else if (frozen_state && !ps_.pre_freeze_solved) {
                ps_.is_frozen = true;
                ps_.frozen_count++;
                bool is_ac = (st == 0);
                frozen_subs[tid][pj].push_back({time, is_ac});
                if (is_ac) ps_.has_frozen_ac = true;
            } else {
                if (st == 0) { ps_.solved = true; ps_.ac_time = time; }
                else ps_.attempts++;
                key_dirty[tid] = true;
            }
        } else if (cmd[0] == 'F' && cmd[1] == 'L') {
            ps("[Info]Flush scoreboard.\n");
            for (int i = 0; i < num_teams; i++)
                if (key_dirty[i]) computeKey(i);
            sort(scoreboard, scoreboard + num_teams, keyLess);
            for (int i = 0; i < num_teams; i++)
                last_flush_rank[scoreboard[i]] = i + 1;
        } else if (cmd[0] == 'F' && cmd[1] == 'R') {
            if (frozen_state) { ps("[Error]Freeze failed: scoreboard has been frozen.\n"); }
            else {
                frozen_state = true;
                for (int i = 0; i < num_teams; i++) {
                    for (int j = 0; j < problem_count; j++) {
                        auto& p = prob[i][j];
                        p.pre_freeze_attempts = p.attempts;
                        p.pre_freeze_solved = p.solved;
                        p.is_frozen = false;
                        p.frozen_count = 0;
                        p.has_frozen_ac = false;
                        frozen_subs[i][j].clear();
                    }
                }
                ps("[Info]Freeze scoreboard.\n");
            }
        } else if (cmd[0] == 'S' && cmd[1] == 'C') {
            if (!frozen_state) { ps("[Error]Scroll failed: scoreboard has not been frozen.\n"); }
            else {
                ps("[Info]Scroll scoreboard.\n");
                
                for (int i = 0; i < num_teams; i++)
                    if (key_dirty[i]) computeKey(i);
                sort(scoreboard, scoreboard + num_teams, keyLess);
                for (int i = 0; i < num_teams; i++) printTeam(i);
                
                int cursor = num_teams - 1;
                while (cursor >= 0) {
                    int tid = scoreboard[cursor];
                    int fp = -1;
                    for (int j = 0; j < problem_count; j++)
                        if (prob[tid][j].is_frozen) { fp = j; break; }
                    if (fp == -1) { cursor--; continue; }
                    
                    bool new_solve = unfreezeProb(tid, fp);
                    if (!new_solve) continue;
                    
                    computeKey(tid);
                    
                    int lo = 0, hi = cursor;
                    while (lo < hi) {
                        int mid = (lo + hi) >> 1;
                        if (keyLess(tid, scoreboard[mid])) hi = mid;
                        else lo = mid + 1;
                    }
                    
                    if (lo < cursor) {
                        int dtid = scoreboard[lo];
                        memmove(&scoreboard[lo + 1], &scoreboard[lo],
                                (cursor - lo) * sizeof(int));
                        scoreboard[lo] = tid;
                        ps(team_names[tid]); pc(' ');
                        ps(team_names[dtid]); pc(' ');
                        pint(keys[tid].solved_count); pc(' ');
                        pint(keys[tid].penalty); pc('\n');
                    }
                }
                
                for (int i = 0; i < num_teams; i++) {
                    last_flush_rank[scoreboard[i]] = i + 1;
                    printTeam(i);
                }
                frozen_state = false;
            }
        } else if (cmd[0] == 'Q' && cmd[6] == 'R') {
            readstr(a1);
            int tid = findTeam(a1);
            if (tid < 0) { ps("[Error]Query ranking failed: cannot find the team.\n"); }
            else {
                ps("[Info]Complete query ranking.\n");
                if (frozen_state)
                    ps("[Warning]Scoreboard is frozen. The ranking may be inaccurate until it were scrolled.\n");
                ps(a1); ps(" NOW AT RANKING "); pint(last_flush_rank[tid]); pc('\n');
            }
        } else if (cmd[0] == 'Q' && cmd[6] == 'S') {
            readstr(a1); readstr(a2); readstr(a3); readstr(a4); readstr(a5);
            int qp = (a3[8] == 'A' && a3[9] == 'L') ? 0 : (a3[8] - 'A' + 1);
            int qs = (a5[7] == 'A' && a5[8] == 'L') ? 4 : parseStatus(a5 + 7);
            int tid = findTeam(a1);
            if (tid < 0) { ps("[Error]Query submission failed: cannot find the team.\n"); }
            else {
                ps("[Info]Complete query submission.\n");
                int idx = last_sub[tid][qp][qs];
                if (idx == -1) { ps("Cannot find any submission.\n"); }
                else {
                    auto& sub = team_subs[tid][idx];
                    ps(a1); pc(' '); pc('A' + sub.problem); pc(' ');
                    ps(status_strs[sub.status]); pc(' '); pint(sub.time); pc('\n');
                }
            }
        } else if (cmd[0] == 'E') {
            ps("[Info]Competition ends.\n");
            break;
        }
    }
    flush_out();
    return 0;
}
