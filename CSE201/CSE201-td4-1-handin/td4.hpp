#ifndef TD4_HPP
#define TD4_HPP

#include <iostream>

#define EXERCISE_1 1
#define EXERCISE_2 1
#define EXERCISE_3 1
#define EXERCISE_4 1
#define EXERCISE_5 1
#define EXERCISE_6 1
#define EXERCISE_7 1


#endif // TD4_HPP

class Coordinate {
public:
    Coordinate();
    Coordinate(double, double);
    double get_x();
    double get_y();
    double get_distance(Coordinate);
private:
    double x;
    double y;
};

class Target {
public:
  Target(Coordinate, double);
  Target();
  Coordinate get_position();
  double get_radius();
  void randomize();
private:
  Coordinate C;
  double r;
};

class Projectile {
public:
  Projectile(Coordinate, double, double);
  Projectile();
  Coordinate get_position();
  double get_velocity_x();
  double get_velocity_y();
  void simulate_step(double);
  bool intersect(Target);
private:
  Coordinate C;
  double vx;
  double vy;
};

class Telemetry {

public:
  Telemetry();
  ~Telemetry();
  int get_tot_points();
  void add_point(double, double, double);
  void get_point(int, double&, double&, double&);
private:
  double* tel;
  int msize;
  int csize;
};

class Game {
public:

  Game(Projectile projectile_other, Target target) : projectile(projectile_other),target(target) {
    time = 0;
  };
  Game(Projectile projectile_other) : Game(projectile_other, Target()) {  target.randomize(); };
  void run(double simulation_interval);
  ~Game() {}
  Telemetry telemetry;

private:
  Projectile projectile;
  Target target;
  double time;
};
