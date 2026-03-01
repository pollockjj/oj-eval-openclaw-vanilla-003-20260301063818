#pragma GCC optimize("O2")
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <unordered_map>
#include <string>
using namespace std;

// Fast I/O
static char buf_in[1 << 22];
static int buf_in_pos = 0, buf_in_len = 0;
inline char gc() {
    if (buf_in_pos == buf_in_len) {
        buf_in_len = fread(buf_in, 1, sizeof(buf_in), stdin);
        buf_in_pos = 0;
        if (buf_in_len == 0) return EOF;
    }
    return buf_in[buf_in_pos++];
}
inline void readstr(char* s) {
    char c = gc();
    while (c == ' ' || c == '\n' || c == '\r') c = gc();
    int i = 0;
    while (c != ' ' && c != '\n' && c != '\r' && c != EOF) { s[i++] = c; c = gc(); }
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
    buf_out[buf_out_pos++] = c;
    if (buf_out_pos == (int)sizeof(buf_out)) flush_out();
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

int num_teams = 0;
char team_names[MAXN][22];
unordered_map<string, int> name_map;

struct ProbStatus {
    short attempts = 0;
    int ac_time = 0;
    bool solved = false;
    bool is_frozen = false;
    short frozen_count = 0;
    short pre_freeze_attempts = 0;
    bool pre_freeze_solved = false;
    short frozen_sub_count = 0;
    // Store frozen submissions compactly: bit for accepted, time
    // Max submissions in a freeze period per team-problem: limited
    struct FzSub { int time; bool accepted; };
    vector<FzSub> frozen_subs;
};

ProbStatus prob[MAXN][MAXM];

// Submissions tracking for query
struct SubRecord { int problem; int status; int time; };
// Per team: all submissions in order
vector<SubRecord> team_subs[MAXN];
// last_sub[team][problem+1 where 0=all][status where 4=all]
int last_sub[MAXN][28][5]; // initialized to -1

// Scoreboard
int scoreboard[MAXN];
int last_flush_rank[MAXN];

int problem_count = 0;

// Sort key - packed for fast comparison
struct SortKey {
    int neg_solved;   // negated for ascending sort = descending solved
    int penalty;
    // solve times sorted descending, padded with large value
    int stimes[MAXM];
    int nsolved;
    int name_id;
} keys[MAXN];

inline bool keyLess(int a, int b) {
    const SortKey& ka = keys[a];
    const SortKey& kb = keys[b];
    if (ka.neg_solved != kb.neg_solved) return ka.neg_solved < kb.neg_solved;
    if (ka.penalty != kb.penalty) return ka.penalty < kb.penalty;
    int n = ka.nsolved; // same as kb.nsolved since neg_solved is same
    for (int i = 0; i < n; i++) {
        if (ka.stimes[i] != kb.stimes[i]) return ka.stimes[i] < kb.stimes[i];
    }
    if (ka.nsolved != kb.nsolved) return ka.nsolved > kb.nsolved;
    return strcmp(team_names[a], team_names[b]) < 0;
}

void computeKey(int tid) {
    auto& k = keys[tid];
    k.neg_solved = 0;
    k.penalty = 0;
    k.nsolved = 0;
    k.name_id = tid;
    int sc = 0;
    for (int j = 0; j < problem_count; j++) {
        auto& p = prob[tid][j];
        if (p.solved && !p.is_frozen) {
            k.neg_solved--;
            k.penalty += 20 * p.attempts + p.ac_time;
            k.stimes[sc++] = p.ac_time;
        }
    }
    k.nsolved = sc;
    sort(k.stimes, k.stimes + sc, [](int a, int b){ return a > b; });
    for (int i = sc; i < MAXM; i++) k.stimes[i] = 0x7fffffff;
}

const char* status_strs[] = {"Accepted", "Wrong_Answer", "Runtime_Error", "Time_Limit_Exceed"};
inline int parseStatus(const char* s) {
    switch(s[0]) {
        case 'A': return 0;
        case 'W': return 1;
        case 'R': return 2;
        default: return 3;
    }
}

bool hasFrozen(int tid) {
    for (int j = 0; j < problem_count; j++)
        if (prob[tid][j].is_frozen) return true;
    return false;
}

int smallestFrozenProb(int tid) {
    for (int j = 0; j < problem_count; j++)
        if (prob[tid][j].is_frozen) return j;
    return -1;
}

void printTeam(int pos) {
    int tid = scoreboard[pos];
    ps(team_names[tid]); pc(' ');
    pint(pos + 1); pc(' ');
    pint(-keys[tid].neg_solved); pc(' ');
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

int main() {
    memset(last_sub, -1, sizeof(last_sub));
    
    bool started = false;
    bool frozen_state = false;
    
    char cmd[32], arg1[32], arg2[32], arg3[32], arg4[32], arg5[32], arg6[32];
    
    while (true) {
        readstr(cmd);
        
        if (cmd[0] == 'A' && cmd[1] == 'D') { // ADDTEAM
            readstr(arg1);
            if (started) {
                ps("[Error]Add failed: competition has started.\n");
            } else if (name_map.count(arg1)) {
                ps("[Error]Add failed: duplicated team name.\n");
            } else {
                int id = num_teams++;
                strcpy(team_names[id], arg1);
                name_map[arg1] = id;
                ps("[Info]Add successfully.\n");
            }
        } else if (cmd[0] == 'S' && cmd[1] == 'T' && cmd[2] == 'A') { // START
            readstr(arg1);
            int dur = readint();
            readstr(arg1);
            int pc_ = readint();
            if (started) {
                ps("[Error]Start failed: competition has started.\n");
            } else {
                started = true;
                problem_count = pc_;
                vector<pair<string, int>> sv;
                for (int i = 0; i < num_teams; i++)
                    sv.push_back({team_names[i], i});
                sort(sv.begin(), sv.end());
                for (int i = 0; i < num_teams; i++) {
                    scoreboard[i] = sv[i].second;
                    last_flush_rank[sv[i].second] = i + 1;
                }
                ps("[Info]Competition starts.\n");
            }
        } else if (cmd[0] == 'S' && cmd[1] == 'U') { // SUBMIT
            readstr(arg1); int pj = arg1[0] - 'A';
            readstr(arg2); // BY
            readstr(arg3); // team
            readstr(arg4); // WITH
            readstr(arg5); // status
            readstr(arg6); // AT
            int time = readint();
            
            int tid = name_map[arg3];
            int st = parseStatus(arg5);
            
            int idx = team_subs[tid].size();
            team_subs[tid].push_back({pj, st, time});
            
            last_sub[tid][pj + 1][st] = idx;
            last_sub[tid][pj + 1][4] = idx;
            last_sub[tid][0][st] = idx;   // ALL problem
            last_sub[tid][0][4] = idx;    // ALL/ALL
            
            auto& ps_ = prob[tid][pj];
            if (ps_.solved) {
                // already solved
            } else if (frozen_state && !ps_.pre_freeze_solved) {
                ps_.is_frozen = true;
                ps_.frozen_count++;
                ps_.frozen_subs.push_back({time, st == 0});
                ps_.frozen_sub_count++;
            } else {
                if (st == 0) { ps_.solved = true; ps_.ac_time = time; }
                else ps_.attempts++;
            }
        } else if (cmd[0] == 'F' && cmd[1] == 'L') { // FLUSH
            ps("[Info]Flush scoreboard.\n");
            for (int i = 0; i < num_teams; i++) computeKey(i);
            sort(scoreboard, scoreboard + num_teams, keyLess);
            for (int i = 0; i < num_teams; i++)
                last_flush_rank[scoreboard[i]] = i + 1;
        } else if (cmd[0] == 'F' && cmd[1] == 'R') { // FREEZE
            if (frozen_state) {
                ps("[Error]Freeze failed: scoreboard has been frozen.\n");
            } else {
                frozen_state = true;
                for (int i = 0; i < num_teams; i++) {
                    for (int j = 0; j < problem_count; j++) {
                        auto& p = prob[i][j];
                        p.pre_freeze_attempts = p.attempts;
                        p.pre_freeze_solved = p.solved;
                        p.is_frozen = false;
                        p.frozen_count = 0;
                        p.frozen_sub_count = 0;
                        p.frozen_subs.clear();
                    }
                }
                ps("[Info]Freeze scoreboard.\n");
            }
        } else if (cmd[0] == 'S' && cmd[1] == 'C') { // SCROLL
            if (!frozen_state) {
                ps("[Error]Scroll failed: scoreboard has not been frozen.\n");
            } else {
                ps("[Info]Scroll scoreboard.\n");
                
                // Flush
                for (int i = 0; i < num_teams; i++) computeKey(i);
                sort(scoreboard, scoreboard + num_teams, keyLess);
                
                // Print pre-scroll scoreboard
                for (int i = 0; i < num_teams; i++) printTeam(i);
                
                // Scroll with cursor from bottom
                int cursor = num_teams - 1;
                while (cursor >= 0) {
                    int tid = scoreboard[cursor];
                    int fp = smallestFrozenProb(tid);
                    if (fp == -1) { cursor--; continue; }
                    
                    // Unfreeze problem fp for team tid
                    auto& p = prob[tid][fp];
                    p.is_frozen = false;
                    for (auto& fs : p.frozen_subs) {
                        if (!p.solved) {
                            if (fs.accepted) { p.solved = true; p.ac_time = fs.time; }
                            else p.attempts++;
                        }
                    }
                    p.frozen_count = 0;
                    p.frozen_sub_count = 0;
                    p.frozen_subs.clear();
                    
                    computeKey(tid);
                    
                    // Binary search for new position (positions 0..cursor-1)
                    // We want the leftmost position where tid should go
                    int lo = 0, hi = cursor;
                    while (lo < hi) {
                        int mid = (lo + hi) / 2;
                        if (keyLess(tid, scoreboard[mid])) hi = mid;
                        else lo = mid + 1;
                    }
                    int new_pos = lo;
                    
                    if (new_pos < cursor) {
                        int displaced_tid = scoreboard[new_pos];
                        memmove(&scoreboard[new_pos + 1], &scoreboard[new_pos],
                                (cursor - new_pos) * sizeof(int));
                        scoreboard[new_pos] = tid;
                        
                        ps(team_names[tid]); pc(' ');
                        ps(team_names[displaced_tid]); pc(' ');
                        pint(-keys[tid].neg_solved); pc(' ');
                        pint(keys[tid].penalty); pc('\n');
                    }
                    // Don't decrement cursor - check same position again
                    // (could have more frozen problems, or a new team slid here)
                }
                
                // Print post-scroll scoreboard
                for (int i = 0; i < num_teams; i++) {
                    last_flush_rank[scoreboard[i]] = i + 1;
                    printTeam(i);
                }
                
                frozen_state = false;
            }
        } else if (cmd[0] == 'Q' && cmd[6] == 'R') { // QUERY_RANKING
            readstr(arg1);
            auto it = name_map.find(arg1);
            if (it == name_map.end()) {
                ps("[Error]Query ranking failed: cannot find the team.\n");
            } else {
                ps("[Info]Complete query ranking.\n");
                if (frozen_state)
                    ps("[Warning]Scoreboard is frozen. The ranking may be inaccurate until it were scrolled.\n");
                ps(arg1); ps(" NOW AT RANKING "); pint(last_flush_rank[it->second]); pc('\n');
            }
        } else if (cmd[0] == 'Q' && cmd[6] == 'S') { // QUERY_SUBMISSION
            readstr(arg1); // team
            readstr(arg2); // WHERE
            readstr(arg3); // PROBLEM=X
            readstr(arg4); // AND
            readstr(arg5); // STATUS=X
            
            int qp; // 0=ALL, 1-26=specific
            if (arg3[8] == 'A' && arg3[9] == 'L') qp = 0;
            else qp = arg3[8] - 'A' + 1;
            
            int qs; // 4=ALL, 0-3=specific
            if (arg5[7] == 'A' && arg5[8] == 'L') qs = 4;
            else qs = parseStatus(arg5 + 7);
            
            auto it = name_map.find(arg1);
            if (it == name_map.end()) {
                ps("[Error]Query submission failed: cannot find the team.\n");
            } else {
                ps("[Info]Complete query submission.\n");
                int tid = it->second;
                int idx = last_sub[tid][qp][qs];
                if (idx == -1) {
                    ps("Cannot find any submission.\n");
                } else {
                    auto& sub = team_subs[tid][idx];
                    ps(arg1); pc(' '); pc('A' + sub.problem); pc(' ');
                    ps(status_strs[sub.status]); pc(' '); pint(sub.time); pc('\n');
                }
            }
        } else if (cmd[0] == 'E') { // END
            ps("[Info]Competition ends.\n");
            break;
        }
    }
    
    flush_out();
    return 0;
}
