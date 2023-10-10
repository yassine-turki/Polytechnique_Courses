/**
  * CSE201 - TD 6
  *
  * Work on your implementation in the td6.cpp file.
  *
  * You should not change any other file, with the exception of main.cpp
  * if you wish to debug your code.
  *
  * The main function in main.cpp runs the automatic grader by default (this is
  * what you need to run while writing your solutions).
  *
  * The value of the macro GRADING defines what code is executed in the main function.
  * If the value is 1 the program runs the automatic grading of the assignment.
  *
  * If the value is 0 (or more precisely, different from 1) the program runs the
  * code in the custom code section below (between the #if GRADING != 1 and
  * #else directives).
  *
  * You can always run the automatic grader just changing the definition of
  * GRADING to 0.
  */

#include <iostream>
#include "grading/grading.hpp"

#include "td6.hpp"

using namespace std;

#define GRADING 1

int main(int argc, char* argv[])
{
#if GRADING != 1
    // START OF THE CUSTOM CODE SECTION
    // This code will be executed only if you set GRADING to a value different from 1

    // END OF THE CUSTOM CODE SECTION
#else
    // RUN THE AUTOMATIC GRADER
    {
      int test_number = 0; // run all the tests

      if (argc == 2) {
        test_number = stoi(argv[1]);
      }

      {
        int result = tdgrading::grading(std::cerr, test_number);

#if EXERCISE_1 != 1
        if (test_number == 0 || test_number == 1)
          std::cerr << "WARNING: The test for exercise 1 did not run" << std::endl
                    << "         Change EXERCISE_1 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif
#if EXERCISE_2 != 1
        if (test_number == 0 || test_number == 2)
          std::cerr << "WARNING: The test for exercise 2 did not run" << std::endl
                    << "         Change EXERCISE_2 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif
#if EXERCISE_3 != 1
        if (test_number == 0 || test_number == 3)
          std::cerr << "WARNING: The test for exercise 3 did not run" << std::endl
                    << "         Change EXERCISE_3 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif
#if EXERCISE_4 != 1
        if (test_number == 0 || test_number == 4)
          std::cerr << "WARNING: The test for exercise 4 did not run" << std::endl
                    << "         Change EXERCISE_4 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif
#if EXERCISE_5 != 1
        if (test_number == 0 || test_number == 5)
          std::cerr << "WARNING: The test for exercise 5 did not run" << std::endl
                    << "         Change EXERCISE_5 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif
#if EXERCISE_6 != 1
        if (test_number == 0 || test_number == 6)
          std::cerr << "WARNING: The test for exercise 6 did not run" << std::endl
                    << "         Change EXERCISE_6 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif
#if EXERCISE_7 != 1
        if (test_number == 0 || test_number == 7)
          std::cerr << "WARNING: The test for exercise 7 did not run" << std::endl
                    << "         Change EXERCISE_7 to 1 in td6.hpp when you are ready to test it" << std::endl;
#endif


        return result;
      }

      // END OF THE AUTOMATIC GRADER
    }
#endif
}
