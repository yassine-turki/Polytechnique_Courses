#include <iostream>
#include "math.h"

#include "common.hpp"
#include "td6.hpp"


// Exercise 1: define the functions Target::get_status and Target::set_status

void Target::toggle_status() {
  // Exercise 1: implement the toggle_status function
}

#if EXERCISE_2 == 1
// Exercise 2: fix the implementation of halve_distance
Coordinate halve_distance(const Coordinate &c1, const Coordinate &c2) {
  c1.set_x((c1.get_x() + c2.get_x()) / 2);
  c1.set_y((c1.get_y() + c2.get_y()) / 2);

  return c1;
}
#endif



// Exercise 4: reduce the number of Coordinate instances
int count_half_segments(Coordinate start, Coordinate end, double min_distance) {
  // Exercise 3: count the half segments
}
