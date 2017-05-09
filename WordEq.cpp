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
    L = minimum((N*Q),(N*P));
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
            lengthLeftVarProp[i][k] = new int[L+1];
        }
    }
    lengthRightVarProp = new int**[Q];
    for (int j=0; j<Q; j++) {
        lengthRightVarProp[j] = new int*[L];
        for (int k=0; k<L; k++) {
            lengthRightVarProp[j][k] = new int[L+1];
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
            for (int k2=k1; k2<(L+1); k2++) {
                lengthLeftVarProp[i][k1][k2] = s.newVar();
            }
        }
    }
    for (int j=0; j<Q; j++) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=0; k2<(L+1); k2++) {
                lengthRightVarProp[j][k1][k2] = s.newVar();
            }
        }
    }
}


void WordEq::generateStartConstraints(Solver &s) {
    //both member start at the first position
    if (printFlag) {
        cout << "\n\n-----Start Constraints-----" << endl;
    }
    s.addUnit(Lit(startLeftVarProp[0][0]));
    s.addUnit(Lit(startRightVarProp[0][0]));
    if (printFlag) {
        cout << "  " << "D[0][0][0]" << endl;
        cout << "  " << "D[0][0][1]" << endl;
    }
}

void WordEq::generateEndConstraints(Solver &s) {
    //both member got the same end
    if (printFlag) {
        cout << "\n-----Common end constraints-----" << endl;
    }
    for (int k=0; k<(L+1); k++) {
        s.addBinary(~Lit(endLeftVarProp[P-1][k]), Lit(endRightVarProp[Q-1][k]));
        s.addBinary(Lit(endLeftVarProp[P-1][k]), ~Lit(endRightVarProp[Q-1][k]));
        if (printFlag) {
            cout << "(-" << "F[" << P-1 << "][" << k << "][0]" << " \\/ " << "F[" << Q-1 << "][" << k << "][1]" << ") /\\ (" << "F[" << P-1 << "][" << k << "][0]" << " \\/ " << "-" << "F[" << Q-1 << "][" << k << "][1]" << ")" << endl;
        }
    }
}

void WordEq::generateUnicityLetterConstraints(Solver &s) {
    //a position can be filled only with one letter
    if (printFlag) {
        cout << "\n-----Unicity of each position constraint-----" << endl;
    }
    for (int k=0; k<L; k++) {
        for (int a1=0; a1<R; a1++) {
            for (int a2=0; a2<R; a2++) {
                if (a1!=a2) {
                    s.addBinary(~Lit(posLeftLetterProp[a1][k]), ~Lit(posLeftLetterProp[a2][k]));
                    s.addBinary(~Lit(posRightLetterProp[a1][k]), ~Lit(posRightLetterProp[a2][k]));
                    if (printFlag) {
                        cout << " -" << "P[" << a1 << "][" << k << "][0]" << " \\/ " << "-" << "P[" << a2 << "][" << k << "][0]" << endl;
                        cout << " -" << "P[" << a1 << "][" << k << "][1]" << " \\/ " << "-" << "P[" << a2 << "][" << k << "][1]" << endl;
                    }
                }
            }
        }
    }
}

void WordEq::generateUnicityStartEndVarConstraints(Solver &s, int member) {
    //each left/right variable get an unique start and an unique end
    if (printFlag) {
        cout << "\n-----Unicity start and end of variable-----" << endl;
    }
    if (member) {
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=0; k2<(L+1); k2++) {
                    if (k1!=k2) {
                        if (k1!=L && k2!=L) {
                            s.addBinary(~Lit(startRightVarProp[j][k1]), ~Lit(startRightVarProp[j][k2]));
                            if (printFlag) {
                                cout << " -" << "D[" << j << "][" << k1 << "][1]" << " \\/ " << "-" << "D[" << j << "][" << k2 << "][1]" << endl;
                            }
                        }
                        s.addBinary(~Lit(endRightVarProp[j][k1]), ~Lit(endRightVarProp[j][k2]));
                        if (printFlag) {
                            cout << " -" << "F[" << j << "][" << k1 << "][1]" << " \\/ " << "-" << "F[" << j << "][" << k2 << "][1]" << endl;
                        }
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=0; k2<(L+1); k2++) {
                    if (k1!=k2) {
                        if (k1!=L && k2!=L) {
                            s.addBinary(~Lit(startLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i][k2]));
                            if (printFlag) {
                                cout << " -" << "D[" << i << "][" << k1 << "][0]" << " \\/ " << "-" << "D[" << i << "][" << k2 << "][0]" << endl;
                            }
                        }
                        s.addBinary(~Lit(endLeftVarProp[i][k1]), ~Lit(endLeftVarProp[i][k2]));
                        if (printFlag) {
                            cout << " -" << "F[" << i << "][" << k1 << "][0]" << " \\/ " << "-" << "F[" << i << "][" << k2 << "][0]" << endl;
                        }
                    }
                }
            }
        }
    }
}

void WordEq::generateExistenceLetterConstraints(Solver &s) {
    //each position get a least a letter
    if (printFlag) {
        cout << "\n-----A position contains a least a letter constraints-----" << endl;
    }
    for (int k=0; k<L; k++) {
        lits.clear();
        for (int a=0; a<R; a++) {
            lits.push(Lit(posLeftLetterProp[a][k]));
            if (printFlag) {
                cout << "  " << "P[" << a << "][" << k << "][0]";
                if (a!=(R-1)) cout << " \\/ ";
            }
        }
        s.addClause(lits);
	if (printFlag) {
        	cout << "\n";
    	}
    }
    for (int k=0; k<L; k++) {
        lits.clear();
        for (int a=0; a<R; a++) {
            lits.push(Lit(posRightLetterProp[a][k]));
            if (printFlag) {
                cout << "  " << "P[" << a << "][" << k << "][1]";
                if (a!=(R-1)) cout << " \\/ ";
            }
        }
        s.addClause(lits);
        if (printFlag) {
            cout << "\n";
        }
    }
}

void WordEq::generateExistenceStartEndVarConstraints(Solver &s, int member) {
    //each left/right variable get a least a start and an end
    if (printFlag) {
        cout << "\n-----A variable contains at least start and end constraints-----" << endl;
    }
    if (member) {
        for (int j=0; j<Q; j++) {
            lits.clear();
            for (int k=0; k<L; k++) {
                lits.push(Lit(startRightVarProp[j][k]));
                if (printFlag) {
                    cout << "  " << "D[" << j << "][" << k << "][1]";
                    if (k!=(L-1)) cout << " \\/ ";
                }
            }
            s.addClause(lits);
	    if (printFlag) {
            cout << "\n";
        }
        }
        for (int j=0; j<Q; j++) {
            lits.clear();
            for (int k=0; k<(L+1); k++) {
                lits.push(Lit(endRightVarProp[j][k]));
                if (printFlag) {
                    cout << "  " << "F[" << j << "][" << k << "][1]";
                    if (k!=L) cout << " \\/ ";
                }
            }
            s.addClause(lits);
	        if (printFlag) {
                cout << "\n";
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            lits.clear();
            for (int k=0; k<L; k++) {
                lits.push(Lit(startLeftVarProp[i][k]));
                if (printFlag) {
                    cout << "  " << "D[" << i << "][" << k << "][0]";
                    if (k!=(L-1)) cout << " \\/ ";
                }
            }
            s.addClause(lits);
	        if (printFlag) {
                cout << "\n";
            }
        }
        for (int i=0; i<P; i++) {
            lits.clear();
            for (int k=0; k<(L+1); k++) {
                lits.push(Lit(endLeftVarProp[i][k]));
                if (printFlag) {
                    cout << "  " << "F[" << i << "][" << k << "][0]";
                    if (k!=L) cout << " \\/ ";
                }
            }
            s.addClause(lits);
	    if (printFlag) {
            cout << "\n";
        }
        }
    }
}

void WordEq::generateContinuityConstraints(Solver &s, int member) {
    if (printFlag) {
        cout << "\n-----Continuity of variables constraints-----" << endl;
    }
    if (member) {
        for (int j=0; j<(Q-1); j++) {
            for (int k=0; k<L; k++) {
                s.addBinary(~Lit(endRightVarProp[j][k]), Lit(startRightVarProp[j+1][k]));
                if (printFlag) {
                    cout << " -" << "F[" << j << "][" << k << "][1]" << " \\/ " << " " << "D[" << j+1 << "][" << k << "][1]" << endl;
                }
            }
        }
        if (printFlag) {
            cout << "\n";
        }
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=(k1+1); k2<L; k2++) {
                    s.addBinary(~Lit(endRightVarProp[j][k1]), ~Lit(startRightVarProp[j][k2]));
                    if (printFlag) {
                        cout << " -" << "F[" << j << "][" << k1 << "][1]" << " \\/ " << "-" << "D[" << j << "][" << k2 << "][1]" << endl;
                    }
                }
            }
        }
        /*for (int j=0; j<Q; j++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=(k1+1); k2<L; k2++) {
                    s.addUnit(~Lit(lengthRightVarProp[j][k2][k1]));
                    if (printFlag) {
                        cout << " -" << "Z[" << j << "][" << k2 << "][" << k1 << "][1]" << endl;
                    }
                }
            }
        }*/
    } else {
        for (int i=0; i<(P-1); i++) {
            for (int k=0; k<L; k++) {
                s.addBinary(~Lit(endLeftVarProp[i][k]), Lit(startLeftVarProp[i+1][k]));
                if (printFlag) {
                    cout << " -" << "F[" << i << "][" << k << "][0]" << " \\/ " << " " << "D[" << i+1 << "][" << k << "][0]" << endl;
                }
            }
        }
        if (printFlag) {
            cout << "\n";
        }
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=(k1+1); k2<L; k2++) {
                    s.addBinary(~Lit(endLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i][k2]));
                    if (printFlag) {
                        cout << " -" << "F[" << i << "][" << k1 << "][0]" << " \\/ " << "-" << "D[" << i << "][" << k2 << "][0]" << endl;
                    }
                }
            }
        }
        /*for (int i=0; i<P; i++) {
            for (int k1=0; k1<(L+1); k1++) {
                for (int k2=(k1+1); k2<L; k2++) {
                    s.addUnit(~Lit(lengthLeftVarProp[i][k2][k1]));
                    if (printFlag) {
                        cout << " -" << "Z[" << i << "][" << k2 << "][" << k1 << "][0]" << endl;
                    }
                }
            }
        }*/
    }
}

/*void WordEq::generateContinuityConstraints(Solver &s, int member) {
    //set the continuity of variable (one after an other)
    if (printFlag) {
        cout << "\n-----Continuity of variables constraints-----" << endl;
    }
    if (member) {
        for (int j=0; j<Q; j++) {
            //s.addUnit(~Lit(startRightVarProp[j][L]));        //start can't not be after the last position
            //cout << "-" << startRightVarProp[j][L] << endl;
            for (int k1=0; k1<(L+1); k1++) {
                if ((k1==(L-1) || k1==L) && j<(Q-1)) {
                    s.addBinary(~Lit(endRightVarProp[j][k1]), Lit(startRightVarProp[j+1][L-1]));  //if the end of variable is at L or L-1
                    if (printFlag) {
                        cout << " -" << "F[" << j << "][" << k1 << "][1]" << " \\/ " << "-" << "D[" << j+1 << "][" << L-1 << "][1]" << endl;
                    } 
                }
                if (k1!=L && j<(Q-1)) {        //if the variable is empty
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k1]), Lit(endRightVarProp[j][k1]));
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k1]), Lit(startRightVarProp[j+1][k1]));
                    s.addTernary(Lit(lengthRightVarProp[j][k1][k1]), ~Lit(endRightVarProp[j][k1]), ~Lit(startRightVarProp[j+1][k1]));
                    if (printFlag) {
                        cout << "(-" << "Z[" << j << "][" << k1 << "][" << k1 << "][1]" << " \\/ " << " " << "F[" << j << "][" << k1 << "][1]" << ")" << " /\\ " << "(-" << "Z[" << j << "][" << k1 << "][" << k1 << "][1]" << " \\/ " << " " << "D[" << j+1 << "][" << k1 << "][1]" << ")" << " /\\ " << "(" << "Z[" << j << "][" << k1 << "][" << k1 << "][1]" << " \\/ " << "-" << "F[" << j << "][" << k1 << "][1]" << " /\\ " << "-" << "D[" << j+1 << "][" << k1 << "][1]" << ")" << endl;
                    }
                }
                for (int k2=k1; k2<(L+1); k2++) {  
                    if (j<(Q-1) && k1<(L-1) && k2<(L-1)) {     //if the variable is not emply and do not end at L-1 or L
                        s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(endRightVarProp[j][k2]));
                        s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(startRightVarProp[j+1][k2]));
                        s.addTernary(Lit(lengthRightVarProp[j][k1][k2]), ~Lit(endRightVarProp[j][k2]), ~Lit(startRightVarProp[j+1][k2]));
                    if (printFlag) {
                        cout << "(-" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << " " << "F[" << j << "][" << k2 << "][1]" << ")" << " /\\ " << "(-" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << " " << "D[" << j+1 << "][" << k2 << "][1]" << ")" << " /\\ " << "(" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << "-" << "F[" << j << "][" << k2 << "][1]" << " /\\ " << "-" << "D[" << j+1 << "][" << k2 << "][1]" << ")" << endl;
                    }
                    }
                    if (k1!=L) {        //for the same variable, the start before the end
                        s.addBinary(~Lit(endRightVarProp[j][k1]), ~Lit(startRightVarProp[j][k2]));
                        if (printFlag) {
                            cout << " -" << "F[" << j << "][" << k1 << "][1]" << " \\/ " << "-" << "D[" << j << "][" << k2 << "][1]" << endl;
                        }
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
                    if (printFlag) {
                        cout << " -" << "F[" << i << "][" << k1 << "][0]" << " \\/ " << "-" << "D[" << i+1 << "][" << L-1 << "][0]" << endl;
                    } 
                }
                if (k1!=L && i<(P-1)) {        //if the variable is empty
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k1]), Lit(endLeftVarProp[i][k1]));
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k1]), Lit(startLeftVarProp[i+1][k1]));
                    s.addTernary(Lit(lengthLeftVarProp[i][k1][k1]), ~Lit(endLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i+1][k1]));
                    if (printFlag) {
                        cout << "(-" << "Z[" << i << "][" << k1 << "][" << k1 << "][0]" << " \\/ " << " " << "F[" << i << "][" << k1 << "][0]" << ")" << " /\\ " << "(-" << "Z[" << i << "][" << k1 << "][" << k1 << "][0]" << " \\/ " << " " << "D[" << i+1 << "][" << k1 << "][0]" << ")" << " /\\ " << "(" << "Z[" << i << "][" << k1 << "][" << k1 << "][0]" << " \\/ " << "-" << "F[" << i << "][" << k1 << "][0]" << " /\\ " << "-" << "D[" << i+1 << "][" << k1 << "][0]" << ")" << endl;
                    }
                }
                for (int k2=k1; k2<(L+1); k2++) { 
                    if (i<(P-1) && k1<(L-1) && k2<(L-1)) {     //if the variable is not emply and do not end at L-1 or L
                        s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(endLeftVarProp[i][k2]));
                        s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(startLeftVarProp[i+1][k2]));
                        s.addTernary(Lit(lengthLeftVarProp[i][k1][k2]), ~Lit(endLeftVarProp[i][k2]), ~Lit(startLeftVarProp[i+1][k2]));
                    if (printFlag) {
                        cout << "(-" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << " " << "F[" << i << "][" << k2 << "][0]" << ")" << " /\\ " << "(-" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << " " << "D[" << i+1 << "][" << k2 << "][0]" << ")" << " /\\ " << "(" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << "-" << "F[" << i << "][" << k2 << "][0]" << " /\\ " << "-" << "D[" << i+1 << "][" << k2 << "][0]" << ")" << endl;
                    }
                    }
                    if (k1!=L) {        //for the same variable, the start before the end
                        s.addBinary(~Lit(endLeftVarProp[i][k1]), ~Lit(startLeftVarProp[i][k2]));
                        if (printFlag) {
                            cout << " -" << "F[" << i << "][" << k1 << "][0]" << " \\/ " << "-" << "D[" << i << "][" << k2 << "][0]" << endl;
                        }
                            
                    }
                }
            }
        }
    }                             
}*/

void WordEq::generateGlobalEqualityConstraints(Solver &s) {
	//equality between the two members of the equation
    if (printFlag) {
        cout << "\n-----members equality constraints-----" << endl;
    }
    for (int k=0; k<L; k++) {
        for (int a=0; a<R; a++) {
            s.addBinary(~Lit(posLeftLetterProp[a][k]), Lit(posRightLetterProp[a][k]));
            s.addBinary(Lit(posLeftLetterProp[a][k]), ~Lit(posRightLetterProp[a][k]));
            if (printFlag) {
                cout << "(-" << "P[" << a << "][" << k << "][0]" << " \\/ " << " " << "P[" << a << "][" << k << "][1]" << ")" << " /\\ " << "(" << "P[" << a << "][" << k << "][0]" << " \\/ " << "-" << "P[" << a << "][" << k << "][1]" << ")" << endl;
            }
		}
	}
}

void WordEq::generateLengthVarConstraints(Solver &s, int member) {
    //define the proposition that describe the length of a variable
    if (printFlag) {
        cout << "\n-----Defining Z constraints-----" << endl;
    }
    if (member) {
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<(L+1); k2++) {
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(startRightVarProp[j][k1]));
                    s.addBinary(~Lit(lengthRightVarProp[j][k1][k2]), Lit(endRightVarProp[j][k2]));
                    s.addTernary(Lit(lengthRightVarProp[j][k1][k2]), ~Lit(startRightVarProp[j][k1]), ~Lit(endRightVarProp[j][k2]));
                    if (printFlag) {
                        cout << "(-" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << " " << "D[" << j << "][" << k1 << "][1]" << ")" << " /\\ " << "(-" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << " " << "F[" << j << "][" << k2 << "][1]" << ")" << " /\\ " << "(" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << "-" << "D[" << j << "][" << k1 << "][1]" << " \\/ " << "-" << "F[" << j << "][" << k2 << "][1]" << ")" << endl;
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<(L+1); k2++) {
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(startLeftVarProp[i][k1]));
                    s.addBinary(~Lit(lengthLeftVarProp[i][k1][k2]), Lit(endLeftVarProp[i][k2]));
                    s.addTernary(Lit(lengthLeftVarProp[i][k1][k2]), ~Lit(startLeftVarProp[i][k1]), ~Lit(endLeftVarProp[i][k2]));
                    if (printFlag) {
                        cout << "(-" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << " " << "D[" << i << "][" << k1 << "][0]" << ")" << " /\\ " << "(-" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << " " << "F[" << i << "][" << k2 << "][0]" << ")" << " /\\ " << "(" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << "-" << "D[" << i << "][" << k1 << "][0]" << " \\/ " << "-" << "F[" << i << "][" << k2 << "][0]" << ")" << endl;
                    }
                }
            }
        }
    }               
}


void WordEq::generateVarMaxLengthConstraints(Solver &s, int member) {
    //check is variable don't overpass the maximum word size
    if (printFlag) {
        cout << "\n-----Max word size constraints-----" << endl;
    }
    if (member) {
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<(L+1); k2++) {
                    if ((k2-k1)>N) {
                        s.addUnit(~Lit(lengthRightVarProp[j][k1][k2]));
                        if (printFlag) {
                            cout << " -" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << endl;
                        }
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<(L+1); k2++) {
                    if ((k2-k1)>N) {
                        s.addUnit(~Lit(lengthLeftVarProp[i][k1][k2]));
                        if (printFlag) {
                            cout << " -" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << endl;
                        }
                    }
                }
            }
        }
    }
}

/*void WordEq::generateVarMaxLengthConstraints(Solver &s, int member) {
    //check is variable don't overpass the maximum word size
    if (printFlag) {
        cout << "\n-----Max word size constraints-----" << endl;
    }
    if (member) {
        for (int j=0; j<Q; j++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<L; k2++) {
                    if ((k2-k1)>N) {
                        s.addBinary(~Lit(startRightVarProp[j][k1]), ~Lit(endRightVarProp[j][k2]));
                        if (printFlag) {
                            cout << " -" << "Z[" << j << "][" << k1 << "][" << k2 << "][1]" << endl;
                        }
                    }
                }
            }
        }
    } else {
        for (int i=0; i<P; i++) {
            for (int k1=0; k1<L; k1++) {
                for (int k2=k1; k2<L; k2++) {
                    if ((k2-k1)>N) {
                        s.addBinary(~Lit(startLeftVarProp[i][k1]), ~Lit(endLeftVarProp[i][k2]));
                        if (printFlag) {
                            cout << " -" << "Z[" << i << "][" << k1 << "][" << k2 << "][0]" << endl;
                        }
                    }
                }
            }
        }
    }
}*/

void WordEq::generateConstEqualityConstraints(Solver &s, int member, int var, int letter) {
	//equality between a variable and a constant from the alphabet
    if (printFlag) {
        cout << "\n-----equality var const constraints-----" << endl;
    }
    if (member) {
        for (int k=0; k<L; k++) {
            s.addBinary(~Lit(startRightVarProp[var][k]), Lit(endRightVarProp[var][k+1]));
            s.addBinary(~Lit(startRightVarProp[var][k]), Lit(posRightLetterProp[letter][k]));
            if (printFlag) {
                cout << "(-" << "D[" << var << "][" << k << "][1]" << " \\/ " << "F[" << var << "][" << k+1 << "][1]" << ") /\\ (-" << "D[" << var << "][" << k << "][1]" << " \\/ " << "P[" << letter << "][" << k << "][1]" << ")" << endl;
            }
        }
    } else {
        for (int k=0; k<L; k++) {
            s.addBinary(~Lit(startLeftVarProp[var][k]), Lit(endLeftVarProp[var][k+1]));
            s.addBinary(~Lit(startLeftVarProp[var][k]), Lit(posLeftLetterProp[letter][k]));
            if (printFlag) {
                cout << "(-" << "D[" << var << "][" << k << "][0]" << " \\/ " << "F[" << var << "][" << k+1 << "][0]" << ") /\\ (-" << "D[" << var << "][" << k << "][0]" << " \\/ " << "P[" << letter << "][" << k << "][0]" << ")" << endl;
            }
        }
    }
}

void WordEq::generateVarEqualityConstraints(Solver &s, int member1, int member2, int var1, int var2) {
    //check the equality of two variables
    if (printFlag) {
        cout << "\n-----equality of two var constraints-----" << endl;
    }
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
                                    if (printFlag) {
                                        cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][1]" << " \\/ " << "-" << "P[" << a << "][" << k1+h << "][1]" << " \\/ " << " " << "P[" << a << "][" << l1+h << "][1]" << endl;
                                    }
                                    s.addClause(lits);
                                    lits.clear();
                                    lits.push(~Lit(lengthRightVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthRightVarProp[var2][l1][l2]));
                                    lits.push(Lit(posRightLetterProp[a][k1+h]));
                                    lits.push(~Lit(posRightLetterProp[a][l1+h]));
                                    if (printFlag) {
                                        cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][1]" << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][1]" << " \\/ " << " " << "P[" << a << "][" << k1+h << "][1]" << " \\/ " << "-" << "P[" << a << "][" << l1+h << "][1]" << endl;
                                    }
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
                                    if (printFlag) {
                                        cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][1]" << " \\/ " << "-" << "P[" << a << "][" << k1+h << "][0]" << " \\/ " << " " << "P[" << a << "][" << l1+h << "][1]" << endl;
                                    }
                                    s.addClause(lits);
                                    lits.clear();
                                    lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthRightVarProp[var2][l1][l2]));
                                    lits.push(Lit(posLeftLetterProp[a][k1+h]));
                                    lits.push(~Lit(posRightLetterProp[a][l1+h]));
                                    if (printFlag) {
                                        cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][1]" << " \\/ " << " " << "P[" << a << "][" << k1+h << "][0]" << " \\/ " << "-" << "P[" << a << "][" << l1+h << "][1]" << endl;
                                    }
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
                                    if (printFlag) {
                                        cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][0]" << " \\/ " << "-" << "P[" << a << "][" << k1+h << "][0]" << " \\/ " << " " << "P[" << a << "][" << l1+h << "][0]" << endl;
                                    }
                                    s.addClause(lits);
                                    lits.clear();
                                    lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                                    lits.push(~Lit(lengthLeftVarProp[var2][l1][l2]));
                                    lits.push(Lit(posLeftLetterProp[a][k1+h]));
                                    lits.push(~Lit(posLeftLetterProp[a][l1+h]));
                                    if (printFlag) {
                                        cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][0]" << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][0]" << " \\/ " << " " << "P[" << a << "][" << k1+h << "][0]" << " \\/ " << "-" << "P[" << a << "][" << l1+h << "][0]" << endl;
                                    }
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
    if (printFlag) {
        cout << "\n-----var length equality constraints-----" << endl;
    }
    if (member1 && member2) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                lits.clear();
                lits.push(~Lit(lengthRightVarProp[var1][k1][k2]));
                if (printFlag) {
                    cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][1]";
                }
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            lits.push(Lit(lengthRightVarProp[var2][l1][l2]));
                            if (printFlag) {
                                cout << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][1]";
                            }
                        }
                    }
                }
                s.addClause(lits);
                if (printFlag) {
                    cout << "\n";
                }
            }
        }
    } else if (member1 || member2) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                lits.clear();
                lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                if (printFlag) {
                    cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][0]";
                }
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            lits.push(Lit(lengthRightVarProp[var2][l1][l2]));
                            if (printFlag) {
                                cout << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][1]";
                            }
                        }
                    }
                }
                s.addClause(lits);
                if (printFlag) {
                    cout << "\n";
                }
            }
        }
    } else {
        for (int k1=0; k1<L; k1++) {
            for (int k2=k1; k2<(L+1); k2++) {
                lits.clear();
                lits.push(~Lit(lengthLeftVarProp[var1][k1][k2]));
                if (printFlag) {
                    cout << " -" << "Z[" << var1 << "][" << k1 << "][" << k2 << "][0]";
                }
                for (int l1=0; l1<L; l1++) {
                    for (int l2=l1; l2<(L+1); l2++) {
                        if ((l2-l1)==(k2-k1)) {
                            lits.push(Lit(lengthLeftVarProp[var2][l1][l2]));
                            if (printFlag) {
                                cout << " \\/ " << "-" << "Z[" << var2 << "][" << l1 << "][" << l2 << "][0]";
                            }
                        }
                    }
                }
                s.addClause(lits);
                if (printFlag) {
                    cout << "\n";
                }
            }
        }
    }
}


void WordEq::parseSolution(const Solver &s) {
    //get solution and verify
    int indexUnit;
    int indexUnit1;
    for (int k=0; k<L; k++) {
        indexUnit = 0;
        for (int a=0; a<R; a++) {
            if(s.model[posLeftLetterProp[a][k]] == l_True) {
                indexUnit++;
                if (s.model[posRightLetterProp[a][k]] != l_True) {
                            throw logic_error("Error in result");
                }
                cout << " " << a;
            }
        }
        if(indexUnit!=1) {
            throw logic_error("more than one letter for a position");
        }
    }
    cout << "\nleft member" << endl;
    for (int i=0; i<P; i++) {
        indexUnit=0;
        indexUnit1=0;
        for (int k=0; k<(L+1); k++) {
            if (k!=L) {
                if(s.model[startLeftVarProp[i][k]] == l_True) {
                    indexUnit++;
                    cout << "var" << i << "[" << k;
                }
            }
            if(s.model[endLeftVarProp[i][k]] == l_True) {
                indexUnit1++;
                cout << "->" << k << "]" << endl;
            }
        }
        if(indexUnit!=1) {
            throw logic_error("more than one start for a position");
        }
        if(indexUnit1!=1) {
            throw logic_error("more than one end for a position");
        }
    }
    cout << "\nright member" << endl;
    for (int j=0; j<Q; j++) {
        for (int k=0; k<(L+1); k++) {
            if (k!=L) {
                if(s.model[startRightVarProp[j][k]] == l_True) {
                    cout << "var" << j << "[" << k;
                }
            }
            if(s.model[endRightVarProp[j][k]] == l_True) {
                cout << "->" << k << "]" << endl;
            }
        }
    }
    //cout << "membre gauche Z " << endl;
    for (int i =0; i<P; i++) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=0; k2<(L+1); k2++) {
                if(s.model[lengthLeftVarProp[i][k1][k2]] == l_True) {
                    //cout << "Zg" << i << "[" << k1 << "][" << k2 << "]" << endl;

                }
            }
        }
    }
    //cout << "membre droite Z " << endl;
    for (int i =0; i<Q; i++) {
        for (int k1=0; k1<L; k1++) {
            for (int k2=0; k2<(L+1); k2++) {
                if(s.model[lengthRightVarProp[i][k1][k2]] == l_True) {
                    //cout << "Zd" << i << "[" << k1 << "][" << k2 << "]" << endl;

                }
            }
        }
    }
}


void WordEq::solve() {
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
            //cout << "constant equality " << "op1(membre) " << op1 << "    op2(var) " << op2 << "   op3(lettre) " << op3 << "    op4  " << endl; 
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
            //cout << "constant equality " << "op1(membre) " << op1 << "    op2(var) " << op2 << "   op3(lettre) " << op3 << endl;
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
