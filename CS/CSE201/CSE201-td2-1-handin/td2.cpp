#include <iostream>     // std::cout, std::fixed
#include <iomanip>      // std::setprecision
#include <math.h>       // sin, cos
#include <limits>       // numeric_limits
#include <stdlib.h>     // include rand
#include <cstdlib>
#include "td2.hpp"

void read_point(std::istream &in, // DO NOT CHANGE
                double &x,         // YOU CAN CHANGE THIS LINE
                double &y) {       // YOU CAN CHANGE THIS LINE
    in >> x; // DO NOT CHANGE
    in >> y; // DO NOT CHANGE
}

double compute_distance(double x1,   // YOU CAN CHANGE THIS LINE
                        double y1,   // YOU CAN CHANGE THIS LINE
                        double x2,   // YOU CAN CHANGE THIS LINE
                        double y2) { // YOU CAN CHANGE THIS LINE
  x1 = (x1 - x2);  // DO NOT CHANGE
  x1 = x1 * x1;    // DO NOT CHANGE
  y1 = (y1 - y2);  // DO NOT CHANGE
  y1 = y1 * y1;    // DO NOT CHANGE
  return sqrt(x1 + y1);  // DO NOT CHANGE
}


double td2_max(double first,  // YOU CAN CHANGE THIS LINE (apart from the function name td2_max)
            double second) {  // YOU CAN CHANGE THIS LINE
    if (first > second) {
        return first;
    } else {
        return second;
    }
}

void generate_target(double &x1, double &y1) {
  x1= (double) rand()/ (double) RAND_MAX*100;
  y1= (double) rand()/ (double) RAND_MAX*100;
}

void generate_obstacle(int &i, int &j) {
  i=rand()%10;
  j=rand()%10;
}

void generate_targets(double *targets, const int num_targets) {
    for (int i=0;i<num_targets;i++){
        generate_target(targets[2*i],targets[2*i+1]);
    }
}

void generate_obstacles(int *obstacles, const int num_obstacles) {
    for (int i=0;i<num_obstacles;i++){
        generate_obstacle(obstacles[2*i],obstacles[2*i+1]);
    }
}

void sort(double *targets, const int num_targets) {
    for (int i=0;i<num_targets*2-2;i++){
        for (int j=0;j<num_targets*2-2-i;j+=2){
            if (targets[j]>targets[(j+2)]){
                std::swap(targets[j],targets[j+2]);
                std::swap(targets[j+1],targets[j+3]);

        }
        }
    }
}

void sort(int *obstacles, const int num_obstacles) {
  for (int i=0;i<num_obstacles*2-2;i++){
      for (int j=0;j<num_obstacles*2-2-i;j+=2){
          if (obstacles[j]>obstacles[j+2]){
              std::swap(obstacles[j+2],obstacles[j]);
              std::swap(obstacles[j+3],obstacles[j+1]);

      }
      }
  }
}

double* find_collision(const double x, const double y,
                       double *targets, const int num_targets) {
  for (int i=0;i<num_targets;i++){
       if (compute_distance(targets[i*2],targets[(i*2)+1],x,y)<=1){
           return targets+i*2;
       }
  }

  return nullptr;
}

bool intersect_obstacle(double x1, double y1,
                        const int i, const int j) {

  if (x1>=i*GRID_SIZE && x1<=(i+1)*GRID_SIZE && y1>=j*GRID_SIZE && y1<=(j+1)*GRID_SIZE){
      return 1;
  }
  return 0;
}


int* find_collision(const double x, const double y,
                    int *obstacles, const int num_obstacles) {
    for (int i=0;i<num_obstacles;i++){
        if (intersect_obstacle(x,y,obstacles[i*2],obstacles[(i*2)+1])){
            return obstacles+i*2;
        }
    }

  return nullptr;
}

void remove_target(double* targets, int &tot_targets, double* target_to_remove) {
  for (double *t=target_to_remove;t!=targets+((tot_targets-1)*2);t+=2){
      *t=*(t+2);
      *(t+1)=*(t+3);
  }
  tot_targets-=1;
}
bool simulate_projectile(const double magnitude, const double angle,
                         const double simulation_interval,
                         double *targets, int &tot_targets,
                         int *obstacles, int tot_obstacles) {
    bool hit_t=0;
    bool hit_o=0;
    double PI = 3.14159265; // use these variables for PI and g
    double g = 9.8;
    double t=0;
    double vi_x=cos(angle*(PI/180))*magnitude;
    double vi_y=sin(angle*(PI/180))*magnitude;
    double x_t=0;
    double y_t=0;
    while (y_t>= 0 && hit_t==0 && hit_o==0){
        double *coordinates= find_collision(x_t, y_t, targets, tot_targets);
        if(coordinates!=NULL){
            remove_target(targets, tot_targets,coordinates);
            hit_t = 1;
        }
        else if (find_collision(x_t, y_t, obstacles, tot_obstacles) != NULL) {
            hit_o = 1;
        }
        else{

        t=t+simulation_interval;
        y_t=vi_y*t-0.5*g*pow(t,2);
        if (y_t>=0){
            x_t=vi_x*t;
        }
        }
    }
    return hit_t;
}

// The following function implement the main loop of the game --- nothing to do here
void game_loop(std::ostream &out, std::istream &in,
               const int max_projectiles,
               int *obstacles, const int num_obstacles,
               double *targets, const int num_targets) {
  int remaining_projectiles = max_projectiles;
  int remaining_targets = num_targets;

  while (remaining_projectiles > 0 && remaining_targets > 0) {
    double magnitude, angle;

    out << "Insert the magnitude and angle for the projectile: ";
    read_point(in, magnitude, angle);

    if (simulate_projectile(magnitude, angle, 0.01,
                            targets, remaining_targets,
                            obstacles, num_obstacles)) {
      out << "You hit one target!" << std::endl;
    } else {
      out << "You missed the target..." << std::endl;
    }

    remaining_projectiles--;
  }

  if (remaining_targets == 0) {
    out << "You won!" << std::endl;
  } else {
    out << "You lost!" << std::endl;
  }
}

void run_game(std::ostream &out, std::istream &in) {
  int tot_projectiles = 5;
  int num_obstacles = 3;
  int num_targets = 2;
  int obstacles[num_obstacles * 2];
  double targets[num_targets * 2];

  // Generate random targets
  generate_targets(targets, num_targets);
  sort(obstacles, num_targets);

  // Generate random obstacles
  generate_obstacles(obstacles, num_obstacles);
  sort(obstacles, num_obstacles);

  out << "List of obstacles:";
  for (int i = 0; i < num_obstacles; i++)
    out << " (" << obstacles[2*i]
        << "," << obstacles[2*i+1] << ")";
  out << std::endl;

  out << "List of targets:";
  for (int i = 0; i < num_targets; i++)
    out << " (" << targets[2*i]
        << "," << targets[2*i+1] << ")";
  out << std::endl;

  // Game loop
  game_loop(out,in,
            tot_projectiles,
            obstacles,
            num_obstacles,
            targets, num_targets);
}
