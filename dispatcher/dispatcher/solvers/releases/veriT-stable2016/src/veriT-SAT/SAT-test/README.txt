To compile:
  gcc -g -c veriT-SAT.c -o veriT-SAT.o
  gcc -g -c SAT-test.c -o SAT-test.o
  gcc -g SAT-test.o veriT-SAT.o -o SAT-test
  gcc -g -c SAT-test2.c -o SAT-test2.o
  gcc SAT-test2.o veriT-SAT.o -o SAT-test2
  ./SAT-test 
  ./SAT-test2 

My notes (for checking memory)
  gcc -g -c veriT-SAT.c -o veriT-SAT.o
  gcc -g -c SAT-test.c -o SAT-test.o
  gcc -g SAT-test.o veriT-SAT.o -o SAT-test
  ./SAT-test 
  valgrind ./SAT-test 2>&1 | more

Clean
  rm -f *~ *.o SAT-test

