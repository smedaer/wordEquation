G++ = g++ -Wall  -g -std=c++11

wordeqsat: Main.o InitWordEq.o WordEq.o Solver.o
	$(G++) *.o -o wordeqsat

Solver.o: Solver.cpp Solver.hpp SolverTypes.hpp Global.hpp Heap.hpp
	$(G++) -c Solver.cpp 

Main.o: Main.cpp WordEq.hpp WordEq.cpp InitWordEq.hpp InitWordEq.cpp Solver.hpp 
	$(G++) -c Main.cpp

WordEq.o: WordEq.hpp WordEq.cpp
	$(G++) -c WordEq.cpp

InitWordEq.o: InitWordEq.hpp InitWordEq.cpp
	$(G++) -c InitWordEq.cpp

clean:
	$(RM) *.o wordeqsat
