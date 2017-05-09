#ifndef __WORDEQ_HPP
#define __WORDEQ_HPP 

#include <iostream>
#include <cmath>
#include <list>
#include "Solver.hpp"

using namespace std;

class WordEq {

public:

    WordEq(list<int> newOperations);

    void solve();

    int getN() { return N; }
    void setN(int newN) { N=newN; }
    int getR() { return R; }
    void setR(int newR) { R=newR; }
    int getL() { return L; }
    void setL(int newL) { L=newL; }
    int getP() { return P; }
    void setP(int newP) { P=newP; }
    int getQ() { return Q; }
    void setQ(int newQ) { Q=newQ; }

private:
    //constants
    int N;                  //length of word
    int R;                  //length of Alphabet
    int P;                  //number of left var
    int Q;                  //number of right var
    int L; //min length of member
//    int F = factoriel(L)/factoriel(L-N-1); //number of possibilities for lengthvar

    vec<Lit> lits;

    list<int> operations;

    string result;

    bool printFlag = false;

    //propositions
    int** posLeftLetterProp;
    int** posRightLetterProp;
    int** startLeftVarProp;
    int** startRightVarProp;
    int** endLeftVarProp;
    int** endRightVarProp;
    int*** lengthLeftVarProp;
    int*** lengthRightVarProp;
    
    int minimum(int n1, int n2) { return (n1 < n2) ? n1 : n2 ; }
    //int factorial(int n) { return (n==1 || n==0) ? 1 : factorial(n-1)*n; }

    void parseSolution(const Solver &s);

    void addNewVar(Solver &s);

    //constraints
    void generateStartConstraints(Solver &s);
    void generateEndConstraints(Solver &s);
    void generateUnicityLetterConstraints(Solver &s);
    void generateUnicityStartEndVarConstraints(Solver &s, int member);
    void generateExistenceLetterConstraints(Solver &s);
    void generateExistenceStartEndVarConstraints(Solver &s, int member);
    void generateContinuityConstraints(Solver &s, int member);
    void generateGlobalEqualityConstraints(Solver &s);
    void generateLengthVarConstraints(Solver &s, int member);
    void generateVarMaxLengthConstraints(Solver &s, int member);
    void generateConstEqualityConstraints(Solver &s, int member, int var, int letter);
    void generateVarEqualityConstraints(Solver &s, int member1, int member2, int var1, int var2);
    void generateVarLengthEqualityConstraints(Solver &s, int member1, int member2, int var1, int var2);
};

#endif 
