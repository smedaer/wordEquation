#include <iostream>
#include <cmath>
#include <list>
#include <cstdio>
#include <ctime>
#include "Solver.hpp"
#include "InitWordEq.hpp"
#include "WordEq.hpp"

using namespace std;

int main() {
    
    list<int> newEq;
    InitWordEq n;
    newEq = n.getEqInfo();

    WordEq eq(newEq);
    //begin clock
    std::clock_t start;
    double duration;
    start = std::clock();

    //solving the equation
    eq.solve();

    //output of clock
    duration = ( std::clock() - start ) / (double) CLOCKS_PER_SEC;
    std::cout<<"\n\n------Time for solver: "<< duration <<"\n\n\n";

    
}
