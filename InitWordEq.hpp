#ifndef __INITWORDEQ_HPP
#define __INITWORDEQ_HPP 

#include <iostream>
#include <list>

using namespace std;

class InitWordEq {
    
public:
    
    list<int> getEqInfo();

private:

    string alphabet;
    string variables;
    string memberLeft;   
    string memberRight;
    int N;          //max size of a word
    list<int> initEq;

    void getDataInput();
    void getInitEq();
    int indexAlphabet(char letter);
    void printResult();

};

#endif
