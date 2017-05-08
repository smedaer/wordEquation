#include <iostream>
#include <cmath>
#include <list>
#include "Solver.hpp"
#include "InitWordEq.hpp"
#include "WordEq.hpp"

using namespace std;

int main() {
    
    list<int> newEq;
    InitWordEq n;
    newEq = n.getEqInfo();

    WordEq eq(newEq);
    eq.solve();

    
}
