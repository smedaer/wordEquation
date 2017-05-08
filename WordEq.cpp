#ifndef __WORDEQ_CPP

#define __WORDEQ_CPP
#include <stdexcept>
#include <string>
#include <stdio.h>
#include <stdlib.h>
#include <list>

#include "WordEq.hpp"
#include "Solver.hpp"

using namespace std;

WordEq::WordEq(list<int> newOperations) { //constructor
    operations = newOperations;
    N = operations.front();
    operations.pop_front();
    R = operations.front();
    operations.pop_front();
    P = operations.front();
    operations.pop_front();
    Q = operations.front();
    operations.pop_front();
    L = minimum(((N*(Q+1))-1),((N*(P+1))-1));
    posLeftLetterProp = new int*[R];
    for (int a=0; a<R; a++) {
        posLeftLetterProp[a] = new int[L];
    }
    posRightLetterProp = new int*[R];
    for (int a=0; a<R; a++) {
        posRightLetterProp[a] = new int[L];
    }
    startLeftVarProp = new int*[P];
    for (int i=0; i<P; i++) {
        startLeftVarProp[i] = new int[L];
    }
    startRightVarProp = new int*[Q];
    for (int j=0; j<Q; j++) {
        startRightVarProp[j] = new int[L];
    }
    endLeftVarProp = new int*[P];
    for (int i=0; i<P; i++) {
        endLeftVarProp[i] = new int[L+1];
    }
    endRightVarProp = new int*[Q];
    for (int j=0; j<Q; j++) {
        endRightVarProp[j] = new int[L+1];
    }
    lengthLeftVarProp = new int**[P];
    for (int i=0; i<P; i++) {
        lengthLeftVarProp[i] = new int*[L];
        for (int k=0; k<L; k++) {
            lengthLeftVarProp[i][k] = new int[L];
        }
    }
    lengthRightVarProp = new int**[Q];
    for (int j=0; j<Q; j++) {
        lengthRightVarProp[j] = new int*[L];
        for (int k=0; k<L; k++) {
            lengthRightVarProp[j][k] = new int[L];
        }
    }
} 
    

void WordEq::addNewVar(Solver &s) {
    //declare new variables in each list containing propositions
    for (int a=0; a<R; a++) {
        for (int k=0; k<L; k++) {
            posLeftLetterProp[a][k] = s.newVar();
            posRightLetterProp[a][k] = s.newVar();
        }
    }

    for (int i=0; i<P; i++) {
        for (int k=0; k<L; k++) {
            startLeftVarProp[i][k] = s.newVar();
            endLeftVarProp[i][k] = s.newVar();
        }
        endLeftVarProp[i][L] = s.newVar();
    }

    for (int j=0; j<Q; j++) {
        for (int k=0; k<L; k++) {
            startRightVarProp[j][k] = s.newVar();
            endRightVarProp[j][k] = s.newVar();
        }
        endRightVarProp[j][L] = s.newVar();
    }

    for (int i=0; i<P; i++) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<L; k2++) {
                lengthLeftVarProp[i][k1][k2] = s.newVar();
            }
        }
    }
    for (int j=0; j<Q; j++) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=0; k2<L; k2++) {
                lengthRightVarProp[j][k1][k2] = s.newVar();
            }
        }
    }
}


void WordEq::generateStartConstraints(Solver &s) {
    //both member start at the first position
    s.addUnit(Lit(posLeftLetterProp[0][0]));
    cout << posLeftLetterProp[0][0] << endl;
    s.addUnit(Lit(posRightLetterProp[0][0]));
    cout << posRightLetterProp[0][0] << endl;
}

void WordEq::generateEndConstraints(Solver &s) {
    //both member got the same end
    for (int k=0; k<L; k++) {
        s.addBinary(~Lit(endLeftVarProp[P-1][k]), Lit(endRightVarProp[Q-1][k]));
        cout << "-" << endLeftVarProp[P-1][k] << " " << endRightVarProp[Q-1][k] << endl;
        s.addBinary(Lit(endLeftVarProp[P-1][k]), ~Lit(endRightVarProp[Q-1][k]));
        cout << endLeftVarProp[P-1][k] << " -" << endRightVarProp[Q-1][k] << endl;
    }
}

void WordEq::generateUnicityLetterConstraints(Solver &s) {
    //a position can be filled only with one letter
    for (int k=0; k<L; k++) {
        for (int a1; a1<R; a1++) {
            for (int a2; a2<R; a2++) {
                if (a1!=a2) {
                    s.addBinary(~Lit(posLeftLetterProp[a1][k]), ~Lit(posLeftLetterProp[a2][k]));
                    cout << "-" << posLeftLetterProp[a1][k] << " -" << posLeftLetterProp[a2][k] << endl;
                    s.addBinary(~Lit(posRightLetterProp[a1][k]), ~Lit(posRightLetterProp[a2][k]));
                    cout << "-" << posRightLetterProp[a1][k] << " -" << posRightLetterProp[a2][k] << endl;
                }
            }
        }
    }
}

void WordEq::generateUnicityStartEndVarConstraints(Solver &s, int member) {
    //each left/right variable get an unique start and an unique end
    if (member) {
        for (int i=0; i<Q; i++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=0; k2<(L+1); k2++) {
                    if (k1!=k2) {
                        if (k1!=L || k2!=L) {
                            s.addBinary(~Lit(startRightVarProp[i][k1]), ~Lit(startRightVarProp[i][k2]));
                            cout << "-" << startRightVarProp[i][k1] << " -" << startRightVarProp[i][k2];
                        }
                        s.addBinary(~Lit(endRightVarProp[i][k1]), ~Lit(endRightVarProp[i][k2]));
                        cout << "-" << endRightVarProp[i][k1] << " -" << endRightVarProp[i][k2];
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=0; k2<(L+1); k2++) {
                    if (k1!=k2) {
                        if (k1!=L || k2!=L) {
                            s.addBinary(~Lit(startLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i][k2]));
                            cout << "-" << startLeftVarProp[i][k1] << " -" << startLeftVarProp[i][k2];
                        }
                        s.addBinary(~Lit(endLeftVarProp[i][k1]), ~Lit(endLeftVarProp[i][k2]));
                        cout << "-" << endLeftVarProp[i][k1] << " -" << endLeftVarProp[i][k2];
                    }
                }
            }
        }
    }
}

void WordEq::generateExistenceLetterConstraints(Solver &s) {
    //each position get a least a letter
    for (int k=0; k<L; k++) {
        lits.clear();
        for (int a=0; a<R; a++) {
            lits.push(Lit(posLeftLetterProp[a][k]));
            cout << posLeftLetterProp[a][k] << " ";
        }
        s.addClause(lits);
        cout << "\n";
    }
}

void WordEq::generateExistenceStartEndVarConstraints(Solver &s, int member) {
    //each left/right variable get a least a start and an end
    if (member) {
        for (int j=1; j<Q; j++) {       //begin at 1 because case 0 is in generateStartConstraints
            lits.clear();
            for (int k=0; k<(L+1); k++) {
                if (k!=L) {
                    lits.push(Lit(startRightVarProp[j][k]));
                    cout << startRightVarProp[j][k] << " ";
                }
                lits.push(Lit(endRightVarProp[j][k]));
                cout << endRightVarProp[j][k] << " ";
            }
            s.addClause(lits);
            cout << "\n";
        }
    } else {
        for (int i=1; i<P; i++) {	    //begin at 1 because case 0 is in generateStartConstraints
            lits.clear();
            for (int k=0; k<(L+1); k++) {
                if (k!=L) {
                    lits.push(Lit(startLeftVarProp[i][k]));
                    cout << startLeftVarProp[i][k] << " ";
                }
                lits.push(Lit(endLeftVarProp[i][k]));
                cout << endLeftVarProp[i][k] << " ";
            }
            s.addClause(lits);
            cout << "\n";
        }
    }
}

void WordEq::generateContinuityConstraints(Solver &s, int member) {
    if (member) {
        for (int j=0; j<Q; j++) {
            //s.addUnit(~Lit(startRightVarProp[j][L]));        //start can't not be after the last position
            //cout << "-" << startRightVarProp[j][L] << endl;
            for (int k1=0; k1<(L+1); k1++) {
                if ((k1==(L-1) || k1==L) && j<(Q-1)) {
                    s.addBinary(~Lit(endRightVarProp[j][k1]), Lit(startRightVarProp[j+1][L-1]));  //if the end of variable is at L or L-1
                    cout << "-" << endRightVarProp[j][k1] << " " << startRightVarProp[j+1][L-1] << endl;
                }
                if (k1!=L && j<(Q-1)) {        //if the variable is empty
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k1]), Lit(endRightVarProp[j][k1]));
                    cout << "-" << lengthRightVarProp[j][k1][k1] << " " << endRightVarProp[j][k1] << endl;
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k1]), Lit(startRightVarProp[j+1][k1]));
                    cout << "-" << lengthRightVarProp[j][k1][k1] << " " << startRightVarProp[j+1][k1] << endl;
                    s.addTernary(Lit(lengthRightVarProp[j][k1][k1]), ~Lit(endRightVarProp[j][k1]), ~Lit(startRightVarProp[j+1][k1]));
                    cout << " " << lengthRightVarProp[j][k1][k1] << " -" << endRightVarProp[j][k1] << " -" << startRightVarProp[j+1][k1] << endl;
                }
                for (int k2=k1; k2<L; k2++) {  
                    if (j<(Q-1) && k1!=k2 && k1<(L-1) && k2!=(L-1)) {     //if the variable is not emply and do not end at L-1 or L
                        s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(endRightVarProp[j][k2]));
                        cout << "-" << lengthRightVarProp[j][k1][k2] << " " << endRightVarProp[j][k2] << endl;
                        s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(startRightVarProp[j+1][k2+1]));
                        cout << "-" << lengthRightVarProp[j][k1][k2] << " " << startRightVarProp[j+1][k2+1] << endl;
                        s.addTernary(Lit(lengthRightVarProp[j][k1][k2]), ~Lit(endRightVarProp[j][k2]), ~Lit(startRightVarProp[j+1][k2+1]));
                        cout << " " << lengthRightVarProp[j][k1][k2] << " -" << endRightVarProp[j][k2] << " -" << startRightVarProp[j+1][k2+1] << endl;
                    }
                    if (k1!=L) {        //for the same variable, the start before the end
                        s.addBinary(~Lit(endRightVarProp[j][k1]), ~Lit(startRightVarProp[j][k2]));
                        cout << "-" << endRightVarProp[j][k1] << " " << startRightVarProp[j][k2] << endl;
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            //s.addUnit(~Lit(startLeftVarProp[i][L]));        //start can't not be after the last position
            //cout << "-" << startLeftVarProp[i][L] << endl;
            for (int k1=0; k1<(L+1); k1++) {
                if ((k1==(L-1) || k1==L) && i<(P-1)) {
                    s.addBinary(~Lit(endLeftVarProp[i][k1]), Lit(startLeftVarProp[i+1][L-1]));  //if the end of variable is at L or L-1
                    cout << "-" << endLeftVarProp[i][k1] << " " << startLeftVarProp[i+1][L-1] << endl;
                }
                if (k1!=L && i<(P-1)) {        //if the variable is empty
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k1]), Lit(endLeftVarProp[i][k1]));
                    cout << "-" << lengthLeftVarProp[i][k1][k1] << " " << endLeftVarProp[i][k1] << endl;
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k1]), Lit(startLeftVarProp[i+1][k1]));
                    cout << "-" << lengthLeftVarProp[i][k1][k1] << " " << startLeftVarProp[i+1][k1] << endl;
                    s.addTernary(Lit(lengthLeftVarProp[i][k1][k1]), ~Lit(endLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i+1][k1]));
                    cout << " " << lengthLeftVarProp[i][k1][k1] << " -" << endLeftVarProp[i][k1] << " -" << startLeftVarProp[i+1][k1] << endl;
                }
                for (int k2=k1; k2<L; k2++) { 
                    if (i<(P-1) && k1!=k2 && k1<(L-1) && k2!=(L-1)) {     //if the variable is not emply and do not end at L-1 or L
                        s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(endLeftVarProp[i][k2]));
                        cout << "-" << lengthLeftVarProp[i][k1][k2] << " " << endLeftVarProp[i][k2] << endl;
                        s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(startLeftVarProp[i+1][k2+1]));
                        cout << "-" << lengthLeftVarProp[i][k1][k2] << " " << startLeftVarProp[i+1][k2+1] << endl;
                        s.addTernary(Lit(lengthLeftVarProp[i][k1][k2]), ~Lit(endLeftVarProp[i][k2]), ~Lit(startLeftVarProp[i+1][k2+1]));
                        cout << " " << lengthLeftVarProp[i][k1][k2] << " -" << endLeftVarProp[i][k2] << " -" << startLeftVarProp[i+1][k2+1] << endl;
                    }
                    if (k1!=L) {        //for the same variable, the start before the end
                        s.addBinary(~Lit(endLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i][k2]));
                        cout << "-" << endLeftVarProp[i][k1] << " " << startLeftVarProp[i][k2] << endl;
                    }
                }
            }
        }
    }                             
}

void WordEq::generateGlobalEqualityConstraints(Solver &s) {
	//equality between the two members of the equation
    for (int k=0; k<L; k++) {
        for (int a=0; a<R; a++) {
            s.addBinary(~Lit(posLeftLetterProp[a][k]), Lit(posRightLetterProp[a][k]));
            cout << "-" << posLeftLetterProp[a][k] << " " << posRightLetterProp[a][k] << endl;
            s.addBinary(Lit(posLeftLetterProp[a][k]), ~Lit(posRightLetterProp[a][k]));
            cout << " " << posLeftLetterProp[a][k] << " -" << posRightLetterProp[a][k] << endl;
		}
	}
}

void WordEq::generateLengthVarConstraints(Solver &s, int member) {
    //define the proposition that describe the length of a variable
    if (member) {
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<(L+1); k2++) {
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(startRightVarProp[j][k1]));
                    cout << "-" << lengthRightVarProp[j][k1][k2] << " " << startRightVarProp[j][k1] << endl;
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(endRightVarProp[j][k2]));
                    cout << "-" << lengthRightVarProp[j][k1][k2] << " " << endRightVarProp[j][k2] << endl;
                    s.addTernary(Lit(lengthRightVarProp[j][k1][k2]), ~Lit(startRightVarProp[j][k1]), ~Lit(endRightVarProp[j][k2]));
                    cout << " " << lengthRightVarProp[j][k1][k2] << " -" << startRightVarProp[j][k1] << " -" << endRightVarProp[j][k2] << endl;
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<(L+1); k2++) {
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(startLeftVarProp[i][k1]));
                    cout << "-" << lengthLeftVarProp[i][k1][k2] << " " << startLeftVarProp[i][k1] << endl;
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(endLeftVarProp[i][k2]));
                    cout << "-" << lengthLeftVarProp[i][k1][k2] << " " << endLeftVarProp[i][k2] << endl;
                    s.addTernary(Lit(lengthLeftVarProp[i][k1][k2]), ~Lit(startLeftVarProp[i][k1]), ~Lit(endLeftVarProp[i][k2]));
                    cout << " " << lengthLeftVarProp[i][k1][k2] << " -" << startLeftVarProp[i][k1] << " -" << endLeftVarProp[i][k2] << endl;
                }
            }
        }
    }               
}


void WordEq::generateVarMaxLengthConstraints(Solver &s, int member) {
    //check is variable don't overpass the maximum word size
    if (member) {
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<L; k2++) {
                    if ((k2-k1)>N) {
                        s.addUnit(~Lit(lengthRightVarProp[j][k1][k2]));
                        cout << "-" << lengthRightVarProp[j][k1][k2] << endl;
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<L; k2++) {
                    if ((k2-k1)>N) {
                        s.addUnit(~Lit(lengthLeftVarProp[i][k1][k2]));
                        cout << "-" << lengthLeftVarProp[i][k1][k2] << endl;
                    }
                }
            }
        }
    }
}

void WordEq::generateConstEqualityConstraints(Solver &s, int member, int var, int letter) {
	//equality between a variable and a constant from the alphabet
    if (member) {
        for (int k=0; k<L; k++) {
            s.addBinary(~Lit(startRightVarProp[var][k]), Lit(endRightVarProp[var][k+1]));
            cout << "-" << startRightVarProp[var][k] << " " << endRightVarProp[var][k+1] << endl;
            s.addBinary(~Lit(startRightVarProp[var][k]), Lit(posRightLetterProp[letter][k]));
            cout << "-" << startRightVarProp[var][k] << " " << posRightLetterProp[letter][k] << endl;
        }
    } else {
        for (int k=0; k<L; k++) {
            s.addBinary(~Lit(startLeftVarProp[var][k]), Lit(endLeftVarProp[var][k+1]));
            cout << "-" << startLeftVarProp[var][k] << " " << endLeftVarProp[var][k+1] << endl;
            s.addBinary(~Lit(startLeftVarProp[var][k]), Lit(posLeftLetterProp[letter][k]));
            cout << "-" << startLeftVarProp[var][k] << " " << posLeftLetterProp[letter][k] << endl;
        }
    }
}

void WordEq::generateVarEqualityConstraints(Solver &s, int member1, int member2, int var1, int var2) {
    //check the equality of two variables
    if (member1 && member2) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            for (int h=0; h<(k2-k1); h++) {
                                for (int a=0; a<R; a++) {
                                    lits.clear();
                                    lits.push(~Lit(lengthRightVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthRightVarProp[var2][l1][l2]));
                                    lits.push(~Lit(posRightLetterProp[a][k1+h]));
                                    lits.push(Lit(posRightLetterProp[a][l1+h]));
                                    cout << " -" << lengthRightVarProp[var1][k1][k2] << " -" << lengthRightVarProp[var2][l1][l2] << " -" << posRightLetterProp[a][k1+h] << " " << posRightLetterProp[a][l1+h] << endl;
                                    s.addClause(lits);
                                    lits.clear();
                                    lits.push(~Lit(lengthRightVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthRightVarProp[var2][l1][l2]));
                                    lits.push(Lit(posRightLetterProp[a][k1+h]));
                                    lits.push(~Lit(posRightLetterProp[a][l1+h]));
                                    cout << " -" << lengthRightVarProp[var1][k1][k2] << " -" << lengthRightVarProp[var2][l1][l2] << " " << posRightLetterProp[a][k1+h] << " -" << posRightLetterProp[a][l1+h] << endl;
                                    s.addClause(lits);
                                }
                            }
                        }
                    }
                }
            }
        }
    } else if (member1 || member2) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            for (int h=0; h<(k2-k1); h++) {
                                for (int a=0; a<R; a++) {
                                    lits.clear();
                                    lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthRightVarProp[var2][l1][l2]));
                                    lits.push(~Lit(posLeftLetterProp[a][k1+h]));
                                    lits.push(Lit(posRightLetterProp[a][l1+h]));
                                    cout << " -" << lengthLeftVarProp[var1][k1][k2] << " -" << lengthRightVarProp[var2][l1][l2] << " -" << posLeftLetterProp[a][k1+h] << " " << posRightLetterProp[a][l1+h] << endl;
                                    s.addClause(lits);
                                    lits.clear();
                                    lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthRightVarProp[var2][l1][l2]));
                                    lits.push(Lit(posLeftLetterProp[a][k1+h]));
                                    lits.push(~Lit(posRightLetterProp[a][l1+h]));
                                    cout << " -" << lengthLeftVarProp[var1][k1][k2] << " -" << lengthRightVarProp[var2][l1][l2] << " " << posLeftLetterProp[a][k1+h] << " -" << posRightLetterProp[a][l1+h] << endl;
                                    s.addClause(lits);
                                }
                            }
                        }
                    }
                }
            }
        }
    } else {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            for (int h=0; h<(k2-k1); h++) {
                                for (int a=0; a<R; a++) {
                                    lits.clear();
                                    lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthLeftVarProp[var2][l1][l2]));
                                    lits.push(~Lit(posLeftLetterProp[a][k1+h]));
                                    lits.push(Lit(posLeftLetterProp[a][l1+h]));
                                    cout << " -" << lengthLeftVarProp[var1][k1][k2] << " -" << lengthRightVarProp[var2][l1][l2] << " -" << posLeftLetterProp[a][k1+h] << " " << posLeftLetterProp[a][l1+h] << endl;
                                    s.addClause(lits);
                                    lits.clear();
                                    lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthLeftVarProp[var2][l1][l2]));
                                    lits.push(Lit(posLeftLetterProp[a][k1+h]));
                                    lits.push(~Lit(posLeftLetterProp[a][l1+h]));
                                    cout << " -" << lengthLeftVarProp[var1][k1][k2] << " -" << lengthRightVarProp[var2][l1][l2] << " " << posLeftLetterProp[a][k1+h] << " -" << posLeftLetterProp[a][l1+h] << endl;
                                    s.addClause(lits);
                                }
                            }
                        }
                    }
                }
            }
        }
    }                                   
}

void WordEq::generateVarLengthEqualityConstraints(Solver &s, int member1, int member2, int var1, int var2) {
    //check the length equality of two variables
    if (member1 && member2) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                lits.clear();
                lits.push(~Lit(lengthRightVarProp[var1][k1][k2]));
                cout << "-" << lengthRightVarProp[var1][k1][k2];
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            lits.push(Lit(lengthRightVarProp[var2][l1][l2]));
                            cout << " " << lengthRightVarProp[var2][l1][l2];
                        }
                    }
                }
                s.addClause(lits);
                cout << "\n";
            }
        }
    } else if (member1 || member2) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                lits.clear();
                lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                cout << "-" << lengthLeftVarProp[var1][k1][k2];
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            lits.push(Lit(lengthRightVarProp[var2][l1][l2]));
                            cout << " " << lengthRightVarProp[var2][l1][l2];
                        }
                    }
                }
                s.addClause(lits);
                cout << "\n";
            }
        }
    } else {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                lits.clear();
                lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                cout << "-" << lengthLeftVarProp[var1][k1][k2];
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            lits.push(Lit(lengthLeftVarProp[var2][l1][l2]));
                            cout << " " << lengthLeftVarProp[var2][l1][l2];
                        }
                    }
                }
                s.addClause(lits);
                cout << "\n";
            }
        }
    }
}


void WordEq::parseSolution(const Solver &s) {
    //get solution and verify
    for (int a=0; a<R; a++) {
        for (int k=0; k<L; k++) {
            if(s.model[posLeftLetterProp[a][k]] == l_True) {
                if (s.model[posRightLetterProp[a][k]] != l_True) {
                            throw logic_error("Error in result");
                }
                cout << " " << a;
            }
        }
    }
}

void WordEq::solve() {
    cout << "on rentre dans solve()" << endl;
    Solver s;

    addNewVar(s);
    generateStartConstraints(s);
    generateEndConstraints(s);
    generateUnicityLetterConstraints(s);
    generateUnicityStartEndVarConstraints(s, 0);
    generateUnicityStartEndVarConstraints(s, 1);
    generateExistenceLetterConstraints(s);
    generateExistenceStartEndVarConstraints(s, 0);    
    generateExistenceStartEndVarConstraints(s, 1);
    cout << "on arrive a la moitie" << endl;
    generateContinuityConstraints(s, 0);
    generateContinuityConstraints(s, 1);
    generateGlobalEqualityConstraints(s);
    generateLengthVarConstraints(s, 0);
    generateLengthVarConstraints(s, 1);
    generateVarMaxLengthConstraints(s, 0);
    generateVarMaxLengthConstraints(s, 1);
    while (operations.size()!=0) {
        if (operations.front()!=-1) {
            int op1 = operations.front();
            operations.pop_front();
            int op2 = operations.front();
            operations.pop_front();
            int op3 = operations.front();
            operations.pop_front();
            int op4 = operations.front();
            operations.pop_front();
            generateVarEqualityConstraints(s, op1, op2, op3, op4);
            generateVarLengthEqualityConstraints(s, op1, op2, op3, op4);
        }   
        else {
            operations.pop_front();
            int op1 = operations.front();
            operations.pop_front();
            int op2 = operations.front();
            operations.pop_front();
            int op3 = operations.front();
            operations.pop_front();
            generateConstEqualityConstraints(s, op1, op2, op3);
        }
    }

    s.solve();
    
    if (!s.okay()) {
        throw logic_error("Unsolvable equation");
    }
    
    parseSolution(s);

}

#endif 
