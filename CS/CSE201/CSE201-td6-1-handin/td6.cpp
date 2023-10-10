#include <iostream>
#include "math.h"

#include "common.hpp"
#include "td6.hpp"


// Exercise 1: define the functions Target::get_status and Target::set_status
TargetStatus Target::get_status(){
    return status;
}
void Target::set_status(TargetStatus s){
    status=s;
}

void Target::toggle_status() {
  // Exercise 1: implement the toggle_status function
    if (status==destroyable){
        status=unbreakable;
    }
    else if (status==unbreakable){
        status=hidden;
    }
    else{
        status=destroyable;
    }
}

#if EXERCISE_2 == 1
// Exercise 2: fix the implementation of halve_distance
Coordinate halve_distance(const Coordinate &c1, const Coordinate &c2) {
    Coordinate c=Coordinate(((c1.get_x() + c2.get_x()) / 2),((c1.get_y() + c2.get_y()) / 2));
    return c;
}
#endif



// Exercise 4: reduce the number of Coordinate instances
int count_half_segments(Coordinate &start, Coordinate &end, double min_distance) {
  // Exercise 3: count the half segments
    Coordinate m=halve_distance(start,end);
    if (start.get_distance(m)>=min_distance){
        return 1+count_half_segments(start,m, min_distance)+count_half_segments(m,end, min_distance);
    }
    else{
        return 0;
    }
}
