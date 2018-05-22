#include <iostream>
#include <cstdio>
#include <sstream>
#include <string>
#include <vector>
#include <list>
#include <map>
#include <set>
#include <queue>
#include <algorithm>
#include <stdlib.h>
#include <utility>
#include <sys/time.h>
#include <chrono>
#include <csignal>
#include <unistd.h>
#include <climits>
#include <cmath>
#include <iomanip>
#include <ctime>
using namespace std;

// constants
#define INF (UINT_MAX>>1)
#define DEBUG 0
#define SAVETIME 1

// data types
#define LL long long
#define UI unsigned int

#define F first
#define S second
#define MP make_pair
#define PB push_back

// tuples
#define PUI pair<UI,UI>
#define TUIPUI pair<UI,PUI>

// 1D arrays
#define VB vector<bool> 
#define VUI vector<UI>
#define VPUI vector<PUI>

// 2D arrays
#define VVUI vector<VUI>
#define VVPUI vector<VPUI>

UI N,M,K,Ones; // num of vertices, edges, terminals
VUI Terminals; // orig indices of terminals
VB isTerminal;
VVPUI G; // input graph
map<PUI,UI> EdgeWeight; // edge weights
VVUI states;
clock_t EPOCH,prevTime;
VB badSplit; 
VUI bestTree; // needed for storing opt solns for subproblems
UI approxSolnValue = INF, PRUNINGPARAM;

VUI setBits( UI a )
{
    VUI res;
    UI i = 0;
    while( a )
    {
        if( a & 1 )
            res.PB(i);
        a = a>>1;
        i++;
    }
    return res;
}

void takeInput()
{
    string str1,str2;
    cin >> str1 >> str2; // SECTION Graph
    cin >> str1 >> N; // Nodes n
    cin >> str1 >> M; // Edges m

    G.resize( N+1, VPUI(0) );

    for( UI i = 0; i < M; i++ )
    {
        UI u,v,w;
        cin >> str1 >> u >> v >> w; // E u v w
        G[u].PB( MP(v,w) );
        G[v].PB( MP(u,w) );
        EdgeWeight[ MP(u,v) ] = EdgeWeight[ MP(v,u) ] = w;
    }

    cin >> str1; // END
    cin >> str1 >> str2; // SECTION Terminals
    cin >> str1 >> K; // Terminals k
    
    isTerminal.resize(N+1,false);
    
    for( UI i = 0; i < K; i++ )
    {
    	UI t;
        cin >> str1 >> t; // T t
        Terminals.PB(t);
        isTerminal[t] = true;
    }
    cin >> str1; // END
    cin >> str1; // EOF

    // a few initializations
	Ones = (1<<K)-1;
	PRUNINGPARAM = (K<16) ? 0 : 4; // no need to prune the DP states for smaller K

    if( DEBUG )
    {
        clock_t curTime = clock();
        UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
        UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
        printf( "Input taken N=%u M=%u K=%u [%u,%u]\n", N, M, K, t1, t2 );
        prevTime = curTime;
    }
}

UI cost(set<PUI> & Soln)
{
    UI c = 0;
    VPUI edges( Soln.begin(), Soln.end() );
    for( UI i = 0, sz = edges.size(); i < sz; i++ )
        c += EdgeWeight[edges[i]];
    return c;
}

void Dijkstra( UI source, PUI **D )
{
    D[source][source] = MP(0,source);

    priority_queue<PUI, std::vector<PUI>, std::greater<PUI> > q;
    q.push( MP(0,source) );

    bool *vis = new bool[N+1]();

    while( !q.empty() )
    {
        PUI cur = q.top();
        q.pop();

        UI curNode = cur.S, curDist = cur.F;
        
        if( vis[curNode] )
            continue;
        
        vis[curNode] = true;

        for( UI i = 0, sz = G[curNode].size(); i < sz; i++ )
        {
            UI ngb = G[curNode][i].F;
            UI wgt = G[curNode][i].S;
            if( !vis[ngb] and D[source][ngb].F > curDist + wgt )
            {
                q.push( MP(curDist+wgt,ngb) );
                D[source][ngb] = MP(curDist+wgt,curNode);
            }
        }
    }

    delete[] vis;
}

void computeAllPairsShortestPaths( PUI **D )
{
    for( UI u = 1; u <= N; u++ )
        Dijkstra( u, D );
}

VPUI shortestPath( UI u, UI v, PUI **D )
{
    VPUI path;
    UI cur = v;
    while( cur != u )
    {
        UI prev = D[u][cur].S;
        path.PB( MP(prev,cur) );
        cur = prev;
    }
    return path;
}

void computeDPTable( PUI **T, PUI **D )
{
    UI largestSubsetSize = K/2;

    badSplit.resize( (1<<K), false );
	bestTree.resize( (1<<K), INF ); // needed for storing opt solutions for subproblems

    VUI smallStates; // subsets of terminals of size <= PRUNINGPARAM
    UI badSplitsFound = 0, totalSplits = 0; // not used in the code - just for info
    LL savings = 0, totalEffort = 0; // not used in the code - just for info

    /* some preprocessing of subsets of terminals */
    states.resize(largestSubsetSize+1);

    for( UI s = 1; s <= Ones; s++ ){
        UI numSetBits = __builtin_popcount(s);
        if( numSetBits <= largestSubsetSize ){
            states[numSetBits].PB(s);
            totalSplits++;
            totalEffort += (1<<numSetBits);
        }
    }

    // Handle base case
    for( UI i = 0; i < K; i++ )
    {
        UI s = (1<<i);
        T[s] = new PUI[N+1];
        
        for( UI u = 1; u <= N; u++ ) // for the base case v = u and one of the subproblems is the terminal
            T[s][u] = MP( D[Terminals[i]][u].F, s + (u<<K) );
        
        bestTree[s] = 0;
    }

    VPUI bestSplit(N+1); // for processing each state (s,v) find the best split s = s1 + s2

    for( UI subsetSize = 2; subsetSize <= largestSubsetSize; subsetSize++ )
    {
        if( DEBUG )
        {
            clock_t curTime = clock();
            UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
            UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
            printf( "Processing subsets of size %u [%u,%u]\n", subsetSize, t1, t2 );
            prevTime = curTime;
        }

        for( UI idx = 0, numStates = states[subsetSize].size(); idx < numStates; idx++ )
        {
            UI s = states[subsetSize][idx];
            VUI subTerminals = setBits(s);

            if( badSplit[s] )
                continue;

            if( subsetSize <= PRUNINGPARAM )
                smallStates.PB(s);
            
            for( UI u = 1; u <= N; u++ )
                bestSplit[u] = MP(INF,0);
            
            for( UI j = 1; j < ( 1<<(subsetSize-1) ); j++ ) // proper subsets of s without one particular element
            {
                VUI tmp = setBits(j);
                UI part = 0; // subset defined by j
                for( UI l = 0, z = tmp.size(); l < z; l++ )
                    part = part + ( 1<<subTerminals[tmp[l]] );
                
                UI comp = s - part; // complement of the subset defined by part

                if( badSplit[part] or badSplit[comp] )
                    continue;

                // find the best partition of s for each vertex v 
                for( UI v = 1; v <= N; v++ )
                {
                    UI cur = T[part][v].F + T[comp][v].F;
                    if( bestSplit[v].F > cur )
                        bestSplit[v] = MP(cur,part);
                }
            }

            // Exercise 6.9 from the textbook on Parameterized Algorithms by Cygan et al.
            // Simulate an instance of single source shortest paths by using the bestSplits for each vertex
            // Add a dummy source vertex x with a dummy edge xv of weight bestSplit[v].F
            // Then find shortest paths from x to every vertex 1 <= v <= N.
            // improves running time to $O(3^K K^O(1) (N+M))$.

            VPUI tmpD( N+1, MP(INF,0) ); // distances and prev vertex
            priority_queue<PUI, std::vector<PUI>, std::greater<PUI> > q;
            
            for( UI u = 1; u <= N; u++ )
            {
                tmpD[u] = MP(bestSplit[u].F,u);
                q.push(tmpD[u]);
            }

            VB vis( N+1, false );
            while( !q.empty() )
            {
                PUI cur = q.top();
                q.pop();

                UI curNode = cur.S, curDist = cur.F;
                
                if( vis[curNode] )
                    continue;
                
                vis[curNode] = true;
                tmpD[curNode].S = tmpD[tmpD[curNode].S].S;

                for( UI i = 0, sz = G[curNode].size(); i < sz; i++ )
                {
                    UI ngb = G[curNode][i].F;
                    UI wgt = G[curNode][i].S;

                    if( !vis[ngb] and tmpD[ngb].F > curDist + wgt )
                    {
                        q.push( MP(curDist + wgt,ngb) );
                        tmpD[ngb] = MP(curDist + wgt,curNode);
                    }
                }
            }
            
            T[s] = new PUI[N+1]; // only create the dp table for state s when needed

            for( UI u = 1; u <= N; u++ )
            {
                UI parent = tmpD[u].S;
                UI value = bestSplit[parent].F; // T[part + parent<<K].F + T[comp + parent<<K].F
                UI part = bestSplit[parent].S;

                T[s][u] = MP( value + D[u][parent].F, part + (parent<<K) );
                bestTree[s] = min(bestTree[s],T[s][u].F);
            }
        }
        
        /*
		The below code does some trimming of the solution space. It is easy to construct examples
		where such trimming is not possible (see public instances 125/131).

		We use approx algorithms designed for Track C to compute an approximate solution that will
		be used to discard subproblems in our DP solution that cannot be part of the optimal solution.
		Suppose that the approximate solution is a (1+epsilon) approximation where epsilon is much less
		than 1. Our goal is to compute dp[D][v] for every subset D of the terminals and for every vertex v.
		To compute dp[D][v] we iterate over all bipartitions D = D1 + D2 and vertices u in V to compute 
		min{ D1+D2 = D, u in V } dp[D1][u] + dp[D2][v] + shortest u-v path. Observe that if
		min{ u } dp[D_1][u] + min{ u } dp[D_2][u] > approx soln value, then the optimal solution cannot be
		formed by any bipartition K1 + K2 of K where K1 contains D1 and K2 contains D2. Thus we may choose
		to not compute dp[X][.] for any X such that X contains D1 and is disjoint from D2 OR X contains D2 
		and is disjoint from D1.
        */

        if( subsetSize == PRUNINGPARAM ) // eliminate larger states
        {
            sort(smallStates.begin(),smallStates.end());
            UI numSmallStates = smallStates.size();

            if( DEBUG ){
                clock_t curTime = clock();
                UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
                UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
                printf( "Number of small states %u [%u,%u]\n", numSmallStates, t1, t2 );
                prevTime = curTime;
            }
            
            for( UI i = 0; i < numSmallStates; i++ ){
                UI s1 = smallStates[i];
                
                for( UI j = i+1; j < numSmallStates; j++ ){
                    UI s2 = smallStates[j];
                    if( (s1 & s2) == 0 and bestTree[s1] + bestTree[s2] > approxSolnValue ) // if the states are disjoint
                    {
                        UI sb1 = __builtin_popcount(s1);
                        UI sb2 = __builtin_popcount(s2);

                        for( UI l = 1, rem = largestSubsetSize - min(sb1,sb2); l <= rem; l++ ){
                            for( UI idx = 0, sz = states[l].size(); idx < sz; idx++ ){
                                UI s = states[l][idx];
                                if( (s & s1) == 0 and (s & s2) == 0 ){
                                    if( sb1+l <= largestSubsetSize and !badSplit[ s|s1 ] ){
                                        badSplit[ s|s1 ] = true;
                                        badSplitsFound++;
                                        savings += (1LL<<(sb1+l));
                                    }
                                    if( sb2+l <= largestSubsetSize and !badSplit[ s|s2 ] ){
                                        badSplit[ s|s2 ] = true;
                                        badSplitsFound++;
                                        savings += (1LL<<(sb2+l));
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if( DEBUG ){
                clock_t curTime = clock();
                UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
                UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
                printf( "Bad Splits found = %u vs %u Gain = %.3lf [%u,%u]\n", 
                    badSplitsFound, totalSplits, (double)badSplitsFound/(double)totalSplits, t1, t2 );
                printf( "Savings = %lld vs %lld Gain = %.3lf [%u,%u]\n", 
                    savings, totalEffort, (double)savings/(double)totalEffort, t1, t2 );

                prevTime = curTime;
            }
        }
    }
}

/*  
	the opt steiner tree T for spanning terminals in sub1 + sub2 and
    including the steiner node u consists of a shortest path from u to v, 
    sub-steiner tree T1 that spans sub1 and v, and sub-steiner tree T2 that
    spans sub2 and v. 
*/

void constructSubSolution( set<PUI> & Soln, UI u, UI v, 
        UI sub1, UI sub2, PUI **T, PUI **D )
{
    // add edges in the path from u to v to the solution
    VPUI path = shortestPath( u, v, D );
    for( UI i = 0, sz = path.size(); i < sz; i++ )
    {
        if( path[i].F < path[i].S )
            Soln.insert( path[i] );
        else
            Soln.insert( MP(path[i].S,path[i].F) );
    }

    // handle sub-solutions recursively
    if( sub2 ) // nontrivial case
    { 
        constructSubSolution( Soln, v, (T[sub1][v].S)>>K, (T[sub1][v].S) & Ones, 
                sub1 - (T[sub1][v].S & Ones), T, D );
        constructSubSolution( Soln, v, (T[sub2][v].S)>>K, (T[sub2][v].S) & Ones, 
                sub2 - (T[sub2][v].S & Ones), T, D );
    }
    else // we have hit the base case
    { 
        if( sub1 )
        {
            VUI idx = setBits(sub1);
            constructSubSolution( Soln, Terminals[idx[0]], v, 0, 0, T, D);
        }
    }
}

void constructSolution( set<PUI> & Soln, PUI **T, PUI **D )
{
    Soln.clear();

    UI value = approxSolnValue+1; // some upper bound
    UI vert = 0;
    UI part[3];

    /* In the optimal Steiner tree OPT (spanning all the terminals), there exists a vertex v such that
    deleting v from OPT splits the tree into 3 parts whose sizes are restricted to a smaller range. We 
    can show that the largest part has size in [K/3,K/2], the second largest part has size in [K/4,sz1], 
    and the smallest part has size in [1,sz2]. This observation gives a constant-factor speedup of approx 
    4x-5x since the textbook version of Dreyfus-Wagner algorithm requires you to compute T[D,v] for all
    subsets D of the terminals. Here you only do it for subsets of size at most K/2 which leads to huge
    savings since computing T[D,v] for a subset D of size r requires 2^r computations */

    UI smallestSubsetSize = (K+2)/3; // ceil of K/3
    UI largestSubsetSize = K/2; // floor of K/2

    for( UI subsetSize = smallestSubsetSize; subsetSize <= largestSubsetSize; subsetSize++ )
    {
        for( UI idx = 0, sz = states[subsetSize].size(); idx < sz; idx++ )
        {
            UI s1 = states[subsetSize][idx];
            UI sb1 = subsetSize; // number of set bits in s1 is just the size of the subset
            UI rem = K - sb1; // remaining terminals

            if( badSplit[s1] or sb1 == 0 or rem < 2 )
            	continue;

            VUI tmp(1<<rem,0);
            UI comp = Ones - s1;
            VUI remTerms = setBits(comp);

            for( UI i = 0; i < rem; i++ )
            {
            	UI iter = 1<<i;
            	while( iter < (1<<rem) )
            	{
            		tmp[iter] += (1<<remTerms[i]);
            		iter++;
            		if( (iter & (1<<i)) == 0 )
            			iter += (1<<i);
            	}
            }

            for( UI i = 1; i < (1<<rem) - 1; i++ )
            {
            	UI s2 = tmp[i];
            	UI sb2 = __builtin_popcount(i);

            	UI s3 = comp - s2;
            	UI sb3 = rem - sb2;

            	if( sb2 <= sb1 and sb3 <= sb2 and 1 <= sb3 )
            	{
            		if( badSplit[s2] or badSplit[s3] )
            			continue;

            		if( bestTree[s1] + bestTree[s2] + bestTree[s3] > value )
            			continue;

            		for( UI u = 1; u <= N; u++ )
            		{
            			if( T[s1][u].F + T[s2][u].F + T[s3][u].F < value )
            			{
            				value = T[s1][u].F + T[s2][u].F + T[s3][u].F;
            				vert = u;
            				part[0] = s1;
            				part[1] = s2;
            				part[2] = s3;
            			}
            		}
            	}
            }
		}
    }

    for( UI i = 0; i < 3; i++ )
    {
	    UI branch = (T[part[i]][vert].S)>>K;
	    UI sub1 = (T[part[i]][vert].S) & part[i];
	    UI sub2 = part[i] - sub1;
	    constructSubSolution( Soln, vert, branch, sub1, sub2, T, D );
	}
}

void printSolution( set<PUI> & Soln )
{
    UI value = 0;
    VPUI tree( Soln.begin(), Soln.end() );
    for( UI i = 0, sz = tree.size(); i < sz; i++ )
        value += EdgeWeight[tree[i]];

    printf( "VALUE %u\n", value );
    for( UI i = 0, sz = tree.size(); i < sz; i++ )
        printf( "%u %u\n", tree[i].F, tree[i].S );
}

set<PUI> trimSoln( set<PUI> Tree )
{
    VUI deg( N+1, 0 );
    for( set<PUI>::iterator it = Tree.begin(); it != Tree.end(); it++ )
    {
        deg[it->F]++;
        deg[it->S]++;
    }

    set<PUI> tmpTree = Tree;
    set<PUI> tmpDeg;
    for( UI u = 1; u <= N; u++)
    {
        if( !isTerminal[u] and deg[u] > 0 )
            tmpDeg.insert(MP(deg[u],u));
    }

    while( !tmpDeg.empty() )
    {
        PUI cur = *(tmpDeg.begin());
        if( cur.F == 0 )
            tmpDeg.erase(cur);
        else if( cur.F == 1 )
        {
            UI u = 0, v = 0;
            for( set<PUI>::iterator it = tmpTree.begin(); it != tmpTree.end(); it++ )
            {
                if( it->F == cur.S )
                {
                    u = it->F;
                    v = it->S;
                    
                    tmpDeg.erase(cur);
                    deg[u]--;

                    if( !isTerminal[v] ){
                        tmpDeg.erase(MP(deg[v],v));    
                        deg[v]--;
                        tmpDeg.insert(MP(deg[v],v));
                    }
                    else
                        deg[v]--;

                    tmpTree.erase(MP(u,v));

                    break;
                }
                else if( it->S == cur.S )
                {
                    u = it->F;
                    v = it->S;

                    tmpDeg.erase(cur);
                    deg[v]--;
                    
                    if( !isTerminal[u] )
                    {
                        tmpDeg.erase(MP(deg[u],u));    
                        deg[u]--;
                        tmpDeg.insert(MP(deg[u],u));
                    }
                    else
                        deg[u]--;

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

    return tmpTree;
}

// Finds MST on the metric completion of G induced on Terminals + Steiner Nodes 
set<PUI> MST( PUI **D, set<UI> SteinerNodes )
{
    set<PUI> Tree;

    UI numSteinerNodes = SteinerNodes.size();

    VUI nodes( K + numSteinerNodes );

    for( UI i = 0; i < K; i++ )
        nodes[i] = Terminals[i];

    copy( SteinerNodes.begin(), SteinerNodes.end(), nodes.begin() + K );

    set<UI> visited( nodes.begin(), nodes.begin()+1 );
    set<UI> unvisited( nodes.begin()+1, nodes.end() );

    set<TUIPUI> curEdges;
    for( UI i = 1; i < K + numSteinerNodes; i++ )
        curEdges.insert( MP( D[nodes[0]][nodes[i]].F, MP(nodes[0],nodes[i]) ) );

    while( !unvisited.empty() )
    {
        TUIPUI e;
        while( true )
        {
            e = (*curEdges.begin());
            if( visited.find(e.S.F) != visited.end() and visited.find(e.S.S) != visited.end() )
            {
                curEdges.erase( curEdges.begin() );
                continue;
            }
            else
                break;
        }

        VPUI path = shortestPath( e.S.F, e.S.S, D );
        copy( path.begin(), path.end(), std::inserter( Tree, Tree.end() ) );

        visited.insert(e.S.S);
        unvisited.erase(e.S.S);

        for( set<UI>::iterator it = unvisited.begin(); it != unvisited.end(); it++ )
            curEdges.insert( MP( D[e.S.S][*it].F, MP( e.S.S, *it ) ) );
    }

    return trimSoln(Tree);
}

pair<UI,set<PUI> > ApproximateSoln( PUI **D )
{
    UI value = INF;
    set<PUI> Tree;

    set<UI> SteinerNodes;

    set<PUI> curSoln = MST( D, SteinerNodes );
    UI curValue = cost(curSoln);
    if( value > curValue )
    {
        value = curValue;
        Tree = curSoln;
    }

    VUI nonTerminals;
    for( UI u = 1; u <= N; u++ )
        if( !isTerminal[u] )
            nonTerminals.PB(u);

    while( true )
    {
        VUI candidates = nonTerminals;
        random_shuffle( candidates.begin(), candidates.end() );
        
        UI i = 0;
        for( ; i < N-K; i++ )
        {
            UI u = candidates[i];
            set<UI> tmpSteinerNodes = SteinerNodes;
            if( SteinerNodes.find(u) == SteinerNodes.end() )
                tmpSteinerNodes.insert(u);
            else
                tmpSteinerNodes.erase(u);

            curSoln = MST( D, tmpSteinerNodes );
            curValue = cost(curSoln);

            if( value > curValue )
            {
                value = curValue;
                Tree = curSoln;
                SteinerNodes = tmpSteinerNodes;
                break;
            }
        }
        if( i == N-K )
            break;
    }
    return MP(value,Tree);
}

void DreyfusWagner()
{
    if( SAVETIME and K >= 24 )
        exit(1);

    PUI **D; // shortest path from u to v w/ second last vertex 
    D = new PUI *[N+1];
    for( UI u = 0; u <= N; u++ )
    {
        D[u] = new PUI[N+1];
        for( UI v = 0; v <= N; v++ )
            D[u][v] = MP(INF,0);
    }

    computeAllPairsShortestPaths( D );

    if( DEBUG )
    {
        clock_t curTime = clock();
        UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
        UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
        printf( "Created distance array [%u,%u]\n", t1, t2 );
        prevTime = curTime;
    }
        
    approxSolnValue = ApproximateSoln(D).F;

    if( DEBUG )
    {
        clock_t curTime = clock();
        UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
        UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
        printf( "Approx Soln %u [%u,%u]\n", approxSolnValue, t1, t2 );
        prevTime = curTime;
    }
    
    PUI **T;   // min-weight steiner tree on subproblems 
            // T[s][u] refers to min-cost steiner tree that spans u and the terminals in s
    T = new PUI *[1<<K];
        
    computeDPTable( T, D );

    set<PUI> Soln;
    constructSolution( Soln, T, D );

    if( DEBUG ){
        clock_t curTime = clock();
        UI t1 = (UI)ceil((double)(curTime-prevTime) / CLOCKS_PER_SEC);
        UI t2 = (UI)ceil((double)(curTime-EPOCH) / CLOCKS_PER_SEC);
        printf( "Solution computed [%u,%u]\n", t1, t2 );
        prevTime = curTime;
    }

    printSolution( Soln );
}

int main()
{
    EPOCH = prevTime = clock();
    srand(unsigned(1991));

    takeInput();
    DreyfusWagner();

    return 0;
}