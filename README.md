# PACE2018
Algorithms for computing optimal/approximate Steiner trees

This repository has two files containing submissions for PACE Challenge 2018 in Track A and Track C. See https://pacechallenge.wordpress.com/pace-2018/ for more details about the contest.

trackA.cpp contains code which takes as input an undirected edge-weighted graph and a set of terminals. The code produces as output the optimal Steiner Tree spanning the given terminals. It is an implementation of the dynamic-programming based algorithm due to Dreyfus and Wagner along with a few constant-factor speedups and another hueristic speedup based on additional assumptions about the input data. More details at the end of this file.

trackC.cpp takes the same kind of input as does trackA.cpp. The code produces as output a 2-approximate Steiner Tree spanning the given terminals. It is an implementation of the standard 2-approximation algorithm based on the primal-dual method. The code also runs a hueristic to improve upon the 2-approximate solution by randomly guessing which Steiner nodes can be added to/removed from the given set of terminals without increasing the solution value. 

To run the above codes use the following commands to (1) compile (2) run with the input data.

For track A:
c++ -std=c++11 -O3 -march=native -Wall -Wextra    trackA.cpp   -o trackA
./trackA < ../path-to-input-data-folder/instancexyz.gr 

For track C:
c++ -std=c++11 -O3 -march=native -Wall -Wextra    trackC.cpp   -o trackC
./trackC < ../path-to-input-data-folder/instancexyz.gr 

Note: 

(1) trackC.cpp does not terminate by itself so it requires the user to send a kill signal. After running the code for a few seconds/minutes, send 'kill <process-id>' command from terminal.

(2) There is a bug in trackA.cpp which makes the code produce a wrong answer for exactly one of the secret instances in track A. In the remaining instances (public or secret) it is either Correct/Time Limit Exceeded/Memory Limit Exceeded/Runtime Error.

Additional details about the algorithm for Track A:

(1) A straightforward implementation of the Dreyfus-Wagner algorithm leads to a running time of Omega(3^K * N^2). Using ideas from Exercise 6.9 from the textbook on Parameterized Algorithms by Cygan et al. we can improve the running time to Big-O( 3^K * K *  (N log N + M) )$.

(2) In the optimal Steiner tree OPT (spanning all the terminals), there exists a vertex v such that deleting v from OPT splits the tree into 3 parts whose sizes are constrained. We can show that the largest part has size in the range [K/3,K/2], the second largest part has size in the range [K/4,sz1], and the smallest part has size in the range [1,sz2]. This observation gives a constant-factor speedup since the textbook version of Dreyfus-Wagner algorithm requires you to compute T[D,v] for all subsets D of the terminals. Here, you do it only for subsets of size at most K/2 which leads to huge savings in the running time since computing T[D,v] for a subset D of size r requires 2^r * N computations.

(3) We also trim the search space for our DP by using a hueristic. It is easy to construct examples where such trimming is not possible (see public instances 125 or 131). We use approx algorithms designed for Track C to compute an approximate solution that will be used to discard subproblems in our DP solution that cannot be part of the optimal solution. Suppose that the approximate solution is a (1+epsilon)-approximation where epsilon is much less than 1. Our goal is to compute dp[D][v] for every subset D of the terminals and for every vertex v. To compute dp[D][v] we iterate over all bipartitions D = (D1,D2) and vertices u in V to compute dp[D][v] as 
min_{ D1+D2 = D, u in V } dp[D1][u] + dp[D2][v] + weight of a shortest u-v path.
Observe that if min_{u} dp[D_1][u] + min_{u} dp[D_2][u] > approx-soln-value, then the optimal solution cannot be formed by any bipartition (K1,K2) of K where K1 contains D1 and K2 contains D2. Thus we may choose	to not compute dp[X][] for any X such that X contains D1 and is disjoint from D2 (OR) X contains D2 and is disjoint from D1.
