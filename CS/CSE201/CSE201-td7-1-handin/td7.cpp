#include <iostream>
#include <algorithm>
#include "td7.hpp"
#include <set>




std::vector<int> reverse_even(std::vector<int> input_vector) {
   std::vector<int> a;
   std::vector<int> b;
  for (int i=0;i<input_vector.size();i++){
      if(input_vector[i]%2==0){
          a.push_back(input_vector[i]);
      }
  }
  for (int i=a.size()-1;i>=0;i--){
      b.push_back(a[i]);
  }
  return b;
}

std::vector<Coordinate> same_coordinates(std::vector<double> list_of_x,
                                          std::vector<double> list_of_y)
{
  std::vector<Coordinate> res;
  for(int i=0; i<list_of_x.size();i++){
      for(int j=0; j<list_of_y.size();j++){
      if(list_of_x[i]==list_of_y[j]){
          Coordinate c=Coordinate(list_of_x[i],list_of_y[j]);
          res.push_back(c);
      }
  }
}
  return res;
}

std::vector<int> filter_max(std::vector<int> max_vector,
                            std::vector<int> other_vector) {
    std::vector<int> res;
    std::set<int> s;
    for(int j=0; j<other_vector.size();j++){

        bool in=0;
      for (int i=0; i<max_vector.size();i++){
          if(max_vector[i]==other_vector[j]){
              in=1;
          }
  }
      if (in==0){
          s.insert(other_vector[j]);
      }
}
    for (const int &number : s){
        res.push_back(number);
    }
    return res;

}
