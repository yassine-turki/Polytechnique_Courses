#include <iostream>     // std::cout, std::fixed
#include <iomanip>      // std::setprecision
#include <math.h>       // sin, cos
#include <limits>       // numeric_limits
using namespace std;

/**
 * @brief Computes the maximum between two numbers
 * @param first
 * @param second
 * @return the maximum between first and second
 */
double max(double first, double second) {
    // IMPLEMENT YOUR CODE HERE
    if (first > second){
        return first;
    }
    else{
        return second;
    }
}

/**
 * @brief Reads two numbers and output the maximum
 * @param cout Output stream to print the maximum
 * @param cin Input stream to read the input numbers
 * @return 0 if there are no errors
 */
void max_io(std::ostream &out, std::istream &in) {
    // IMPLEMENT YOUR CODE HERE

    // WARNING -- remember to output
    // "The maximum number is: " followed by the maximum number

    double n1;
    in>>n1;
    double n2;
    in>>n2;
    double number;
    number=max(n1,n2);
    out<< "The maximum number is:"<<number;

}


/**
 * @brief read_doubles Read and prints a list of 5 numbers
 * @param cout Stream to print the numbers
 * @param cin Stream to read the numbers from
 * @return 0 if there are no errors
 */
void read_doubles(std::ostream &out, std::istream &in) {
    // IMPLEMENT YOUR CODE HERE

    // WARNING -- remember to output
    // the list of numbers you read from in
    double numbers[5];
    for (int i = 0; i < 5; i++) {
        in>>numbers[i];
    }
    for (int i = 0; i < 5; i++) {
        out<<numbers[i]<<" ";
    }
}

/**
 * @brief Computes the trajectory of a projectile
 * @param magnitude of the initial velocity vector of the projectile
 * @param angle of the initial velocity vector of the projectile
 * @param simulation_interval time interval used to simulate the projectile's
 * trajectory
 * @return the final position of the projectile before hitting the ground
 */
double simulate_projectile(const double magnitude,
                           const double angle,
                           const double simulation_interval) {
    double PI = 3.14159265; // use these variables for PI and g
    double g = 9.8;
    double t=0;
    double vi_x=cos(angle*(PI/180))*magnitude;
    double vi_y=sin(angle*(PI/180))*magnitude;
    double x_t=0;
    double y_t=0;
    while (y_t>= 0){
        t=t+simulation_interval;
        y_t=vi_y*t-0.5*g*pow(t,2);
        if (y_t>=0){
            x_t=vi_x*t;
        }
    }

    return x_t;
}


/**
 * @brief Computes the minimum distance between the projectile trajectory
 * and a target
 * @param magnitude of the initial velocity vector of the projectile
 * @param angle of the initial velocity vector of the projectile
 * @param simulation_interval time interval used to simulate the projectile's
 * trajectory
 * @param x_target is the x coordinate of the target
 * @param y_target is the y coordinate of the target
 * @return the minimum distance from the projectile to the target
 */
double compute_min_distance(const double magnitude,
                            const double angle,
                            const double simulation_interval,
                            const double x_target,
                            const double y_target) {
    // IMPLEMENT YOUR CODE HERE
    double PI = 3.14159265;
    double g = 9.8;
    double vi_x=cos(angle*(PI/180))*magnitude;
    double vi_y=sin(angle*(PI/180))*magnitude;
    double d;
    double x_t=0;
    double y_t=0;
    double t=0;
    double minimum_d=sqrt(( x_target) * ( x_target) + ( y_target) * ( y_target));
    while(y_t>=0){
        d=sqrt((x_t - x_target) * (x_t - x_target) + (y_t - y_target) * (y_t - y_target));
        if (d<minimum_d){
            minimum_d=d;
        }
        t=t+simulation_interval;
        y_t=vi_y*t-0.5*g*pow(t,2);
        if (y_t>=0){
            x_t=vi_x*t;
        }


    }

    return minimum_d;
}


/**
 * @brief Computes the minimum distance between several projectile
 * trajectories and a  target
 * @param proj_magitude magnitudes of the projectiles
 * @param proj_angle angles of the projectiles
 * @param simulation_interval time interval used to simulate the projectile's
 * trajectory
 * @param x_target is the x coordinate of the target
 * @param y_target is the y coordinate of the target
 * @return the minimum distance
 */
double simulate_multiple_projectiles(const double proj_magnitude[],
                                     const double proj_angle[],
                                     const int total_projectile,
                                     const double simulation_interval,
                                     const double x_target,
                                     const double y_target) {
    // IMPLEMENT YOUR CODE HERE
    double minimum_d = compute_min_distance(proj_magnitude[0],proj_angle[0],simulation_interval,x_target,y_target);
    for (int i = 1; i < total_projectile; i++) {
        double d = compute_min_distance(proj_magnitude[i],proj_angle[i],simulation_interval,x_target, y_target);
        if (d<minimum_d){
            minimum_d=d;
        }
    }

    return minimum_d;
}


/**
 * @brief Shooting game
 * @param out is the output stream to print the game's output
 * @param in is the input stream to read the game's input
 * @return 0 if the function terminates correctly
 */
void play_game(std::ostream &out, std::istream &in) {
    double simulation_interval = 0.05;

    // IMPLEMENT YOUR CODE HERE
    double x_target;
    out<<"Insert x_target:";
    in>>x_target;
    out<<"Insert y_target:";
    double y_target;
    in>>y_target;
    double magnitudes[5];
    double angles[5];
    for (int i=0;i<5;i++){
        out<<"Insert the magnitude for the "<<i+1<<"th projectile";
        in>>magnitudes[i];
        out<<"Insert the magnitude for the "<<i+1<<"th projectile";
        in>>angles[i];
    }
double minimum_d = simulate_multiple_projectiles(magnitudes, angles, 5,simulation_interval, x_target, y_target);
if (minimum_d <= 1)
      out << "You hit the target!" << endl;
    else
      out << "You did not hit the target." <<endl
          << "Minimum distance: " << minimum_d << endl;

    // WARNING -- remember to output
    // "You hit the target" if a projectile hit target
    // "You did not hit the target" if it didn't
}
