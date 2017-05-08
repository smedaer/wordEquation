#ifndef __INITWORDEQ_CPP
#define __INITWORDEQ_CPP 

#include <iostream>
#include <list>
#include "InitWordEq.hpp"

void InitWordEq::getDataInput() {
    cout << "\n";
    cout << "Please enter the maximum length of a word: ";
    cin >> N;
    cout << "\n";
    cout << "Please enter the entire alphabet: ";
    cin >> alphabet;
    cout << "\n";
    cout << "Please enter all variables: ";
    cin >> variables;
    cout << "\n";
    cout << "Please enter the left member of the equation: ";
    cin >> memberLeft;
    cout << "\n";
    cout << "Please enter the right member of the equation: ";
    cin >> memberRight;
    cout << "\n";
}

void InitWordEq::getInitEq() {
    int letterPos; //id of alphabet letter
    //global parameters
    initEq.push_back(N);
    initEq.push_back(alphabet.size());
    initEq.push_back(memberLeft.size());
    initEq.push_back(memberRight.size());
    //memberLeft
    for (int i1=0; i1<static_cast<int>(memberLeft.size()); i1++) {
        letterPos = indexAlphabet(memberLeft[i1]);
        cout << "left member" << letterPos << endl;
        if (letterPos!=-1) {
            initEq.push_back(-1);
            initEq.push_back(0);
            initEq.push_back(i1);
            initEq.push_back(letterPos);
        } else {
            for (int i2=(i1+1); i2<static_cast<int>(memberLeft.size()); i2++) {
                if (memberLeft[i1]==memberLeft[i2]) {
                    initEq.push_back(0);
                    initEq.push_back(0);
                    initEq.push_back(i1);
                    initEq.push_back(i2);
                }
            }
            for (int j=0; j<static_cast<int>(memberRight.size()); j++) {
                if (memberLeft[i1]==memberRight[j]) {
                    initEq.push_back(0);
                    initEq.push_back(1);
                    initEq.push_back(i1);
                    initEq.push_back(j);
                }
            }
        }
    }
    //memberRight
    for (int j1=0; j1<static_cast<int>(memberRight.size()); j1++) {
        letterPos = indexAlphabet(memberRight[j1]);
        cout << "right member" << letterPos << endl;
        if (letterPos!=-1) {
            initEq.push_back(-1);
            initEq.push_back(1);
            initEq.push_back(j1);
            initEq.push_back(letterPos);
        } else {
            for (int j2=(j1+1); j2<static_cast<int>(memberRight.size()); j2++) {
                if (memberRight[j1]==memberRight[j2]) {
                    initEq.push_back(1);
                    initEq.push_back(1);
                    initEq.push_back(j1);
                    initEq.push_back(j2);
                }
            }
        }
    }
                
            
    
}

void InitWordEq::printResult() {
    for (list<int>::iterator it = initEq.begin(); it != initEq.end(); it++) {
        cout << *it << ' ';
    }
}

int InitWordEq::indexAlphabet(char letter) {
    int result = -1;
    for (int i=0; i<static_cast<int>(alphabet.size()); i++) {
        if (alphabet[i]==letter) result = i;
        cout << "in alphabet fct  " << alphabet[i] << " " << letter << endl;
    }
    cout << "\n";
    return result;
}

list<int> InitWordEq::getEqInfo() {
    getDataInput();
    getInitEq();
    printResult();
    return initEq;
}

#endif
