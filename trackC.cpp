#include<iostream>
#include<cstdio>
#include<sstream>
#include<string>
#include<vector>
#include<list>
#include<map>
#include<set>
#include<queue>
#include<algorithm>
#include<stdlib.h>
#include<utility>
#include<sys/time.h>
#include<atomic>
#include<chrono>
#include<csignal>
#include<unistd.h>
#include<climits>

using namespace std;

// constants
#define DEBUG 0

// data types
#define LL long long

#define F first
#define S second
#define MP make_pair
#define PB push_back

// tuples
#define PI pair<int,int>
#define TPII pair<PI,int>
#define TIPI pair<int,PI>
#define TDPI pair<double,PI>

// 1D arrays
#define VB vector<bool> 
#define VI vector<int>
#define VPI vector<PI>

// 2D arrays
#define VVI vector<VI>
#define VVPI vector<VPI>

int N,M,K; // num of vertices, edges, terminals
set<int> T; // terminals
vector<TPII> E; // list of edges
map<PI,int> edgeWeight; // edge weights
VI parent,sizes;
VB active;
int numActive = 0;
int value = INT_MAX;
VPI tree;

void takeInput()
{
    edgeWeight.clear(); T.clear();
    
	string s1,s2;
    cin>>s1>>s2; // SECTION Graph
    cin>>s1>>N; // Nodes n
    cin>>s1>>M; // Edges m
    
    for(int i=0;i<M;i++){
		int u,v,w;
		cin>>s1>>u>>v>>w; // E u v w
        PI e = MP(min(u,v),max(u,v)); // store edges as e = uv with u < v
        edgeWeight[e] = w;
        E.PB(MP(e,w));
    }
    cin>>s1; // END
    cin>>s1>>s2; // SECTION Terminals
    cin>>s1>>K; // Terminals k
    
    for(int i=0;i<K;i++){
        int t;
        cin>>s1>>t; // T t
        T.insert(t);
    }
    cin>>s1; // END
    cin>>s1; // EOF
}

pair<int,VPI> removeLeafSteinerNodes(int W,VPI tree){
    VI deg(N+1,0);
    for(int i=0,sz=tree.size();i<sz;i++){
        deg[tree[i].F]++;
        deg[tree[i].S]++;
    }

    set<PI> tmpTree(tree.begin(),tree.end());
    set<PI> tmpDeg;
    for(int u=1;u<=N;u++){
        if(T.find(u) == T.end() and deg[u] > 0){
            tmpDeg.insert(MP(deg[u],u));
        }
    }

    while(!tmpDeg.empty()){
        PI cur = *(tmpDeg.begin());
        if(cur.F == 0){
            tmpDeg.erase(cur);
        }
        else if(cur.F == 1){
            int u=0,v=0;
            for(set<PI>::iterator it = tmpTree.begin();it != tmpTree.end();it++){
                if((*it).F == cur.S){
                    u = (*it).F;
                    v = (*it).S;
                    
                    tmpDeg.erase(cur);
                    deg[u]--;

                    if(T.find(v) == T.end()){
                        tmpDeg.erase(MP(deg[v],v));    
                        deg[v]--;
                        tmpDeg.insert(MP(deg[v],v));
                    }
                    else{
                        deg[v]--;
                    }

                    W -= edgeWeight[MP(u,v)];
                    tmpTree.erase(MP(u,v));

                    break;
                }
                else if((*it).S == cur.S){
                    u = (*it).F;
                    v = (*it).S;

                    tmpDeg.erase(cur);
                    deg[v]--;
                    
                    if(T.find(u) == T.end()){
                        tmpDeg.erase(MP(deg[u],u));    
                        deg[u]--;
                        tmpDeg.insert(MP(deg[u],u));
                    }
                    else{
                        deg[u]--;
                    }

                    W -= edgeWeight[MP(u,v)];
                    tmpTree.erase(MP(u,v));
                    break;
                }
                else{
                    continue;
                }
            }
        }
        else{
            break;
        }
    }

    tree.clear();
    tree.resize(tmpTree.size());
    copy(tmpTree.begin(), tmpTree.end(), tree.begin());
    return MP(W,tree);
}

int findParent(int u){
    if(u == parent[u])
        return u;
    else
        return parent[u] = findParent(parent[u]);
}

void merge(int u,int v){
    int pu = findParent(u);
    int pv = findParent(v);

    if(active[pu] and active[pv])
        numActive--;

    if(sizes[pu] > sizes[pv]){
        parent[pv] = pu;
        sizes[pu] += sizes[pv];
        active[pv] = 0;
        active[pu] = 1;
    }
    else{
        parent[pu] = pv;
        sizes[pv] += sizes[pu];
        active[pv] = 1;
        active[pu] = 0;
    }
}

pair<int,VPI> dualAlgorithm(set<int> sNodes){
    VPI forest;
    int W = 0;

    parent.clear();
    sizes.clear();
    active.clear();
    numActive = 0;

    parent.resize(N+1,0);
    sizes.resize(N+1,1);
    active.resize(N+1,false);

    for(int i=1;i<=N;i++)
        parent[i] = i;

    for(set<int>::iterator t=T.begin();t != T.end();t++)
        active[*t] = true;
    
    for(set<int>::iterator node=sNodes.begin();node != sNodes.end();node++)
        active[*node] = true;

    numActive = T.size() + sNodes.size();

    vector<TPII> curEdges = E;

    vector<double> moat(N+1,0.0);
    while(numActive > 1){
        PI minEdge;
        double time = 1e9;
        for(int i=0,sz=curEdges.size();i<sz;i++){
            double rem = curEdges[i].S;
            int u = curEdges[i].F.F;
            int v = curEdges[i].F.S;
            rem -= moat[u];
            rem -= moat[v];
            int pu = findParent(u);
            int pv = findParent(v);
            if(active[pu] or active[pv]){
                double curTime = rem/((int)active[pu]+(int)active[pv]);
                if(curTime < time){
                    minEdge = curEdges[i].F;
                    time = curTime;
                }
            }
        }

        forest.PB(minEdge);
        W += edgeWeight[minEdge];

        merge(minEdge.F,minEdge.S);
        vector<TPII> tmpEdges = curEdges;
        curEdges.clear();

        for(int u=1;u<=N;u++){
            int pu = findParent(u);
            if(active[pu]){
                moat[u] += time;
            }
        }

        for(int i=0,sz=tmpEdges.size();i<sz;i++){
            int u = tmpEdges[i].F.F;
            int v = tmpEdges[i].F.S;
            int pu = findParent(u);
            int pv = findParent(v);
            if(pu != pv)
                curEdges.PB(tmpEdges[i]);
        }
    }
    return removeLeafSteinerNodes(W,forest);
}

void printSoln(){
    printf("VALUE %d\n", value);
    for(int i=0,sz=tree.size();i<sz;i++){
        printf("%d %d\n", tree[i].F, tree[i].S);
    }
}

void handleSignal(int signalNum)
{
    if (signalNum == SIGINT or signalNum == SIGTERM)
    {
        printSoln();
        exit(0);
    }
}

int main(int argc,char **argv)
{
	takeInput();

    // Handle kill signal

    signal(SIGTERM, handleSignal);
    signal(SIGINT, handleSignal);
    
    int opt;
    while((opt = getopt(argc, argv, "s:")) != -1){
        if(opt == 's'){
            srand(unsigned(std::stoul(optarg)));
        }
        else{
            srand(unsigned(1105));
        }
    }

    set<int> SteinerNodes;

    pair<int,VPI> initSoln = dualAlgorithm(SteinerNodes);
    int initValue = INT_MAX;
    VPI initTree;

    if(initValue > initSoln.F){
        initValue = initSoln.F;
        initTree = initSoln.S;

        value = initValue;
        tree = initTree;
    }

    VI nonTerminals;
    for(int u=1;u<=N;u++){
        if(T.find(u) == T.end())
            nonTerminals.PB(u);
    }

    while( true )
    {
        SteinerNodes.clear();
        int tmpValue = initValue;
        VPI tmpTree = initTree;

        while(true)
        {
            VI candidates = nonTerminals;
            random_shuffle(candidates.begin(),candidates.end());
            
            int i = 0;
            for(;i<N-K;i++){
                int u = candidates[i];
                set<int> tmpSteinerNodes = SteinerNodes;
                if(SteinerNodes.find(u) == SteinerNodes.end())
                    tmpSteinerNodes.insert(u);
                else
                    tmpSteinerNodes.erase(u);

                pair<int,VPI> curSoln = dualAlgorithm(tmpSteinerNodes);
                if(tmpValue > curSoln.F)
                {
                    tmpValue = curSoln.F;
                    tmpTree = curSoln.S;
                    SteinerNodes = tmpSteinerNodes;
                    break;
                }
            }

            if(i == N-K)
                break;
        }

        if(tmpValue < value)
        {
            value = tmpValue;
            tree = tmpTree;
        }
    }

    return 0;
}