#include <iostream>
#include <math.h>
#include <stdlib.h>     // include rand

#include "td4.hpp"

double PI = 3.14159265;
const double G_CONSTANT = 9.8;

// Class Coordinate

Coordinate::Coordinate(){
    x=0;
    y=0;
}
Coordinate::Coordinate(double px, double py){
    x=px;
    y=py;
}
double Coordinate::get_x(){
    return x;
}
double Coordinate::get_y(){
    return y;
}
double Coordinate::get_distance(Coordinate C){
    return sqrt(pow(C.x-x,2)+pow(C.y-y,2));
}

// Class Target

Target::Target(){
    C=Coordinate();
    r=1;
}
Target::Target(Coordinate c,double rad){
    C=c;
    r=rad;
}
Coordinate Target::get_position(){
    return C;
}

double Target::get_radius(){
    return r;
}
void Target::randomize(){
    C=Coordinate(rand()%101,rand()%101);
}

// Class Projectile

Projectile::Projectile(){
    C=Coordinate();
    double mag=1;
    double angle=45;
    vx=mag*cos(angle*PI/180);
    vy=mag*sin(angle*PI/180);
}

Projectile::Projectile(Coordinate c, double magnitude, double a){
    C=c;
    vx=magnitude*cos(a*PI/180);
    vy=magnitude*sin(a*PI/180);
}
double Projectile::get_velocity_x(){
    return vx;
}
double Projectile::get_velocity_y(){
    return vy;
}
Coordinate Projectile::get_position(){
    return C;
}
void Projectile::simulate_step(double i){
    C=Coordinate(C.get_x()+vx*i,C.get_y()+vy*i-0.5*G_CONSTANT*pow(i,2));
    vy=vy-G_CONSTANT*i;
}
bool Projectile::intersect(Target t){
    if(C.get_distance(t.get_position())<=t.get_radius()){
        return 1;
    }
    else{
        return 0;
    }
}

// Class Telemetry

Telemetry::Telemetry(){
    tel = new double[15];
    msize=15;
    csize=0;
}
Telemetry::~Telemetry(){
    delete[] tel;
}
int Telemetry:: get_tot_points(){
   return csize/3;
}
void Telemetry::add_point(double t, double x, double y){
    if (csize==msize){
        double* narray= new double[msize+15];
        for(int i=0;i<msize;i++){
            narray[i]=tel[i];
        }
        delete[] tel;
        tel=narray;
        msize+=15;
    }
   tel[csize]=t;
   tel[csize+1]=x;
   tel[csize+2]=y;
   csize+=3;
}

void Telemetry::get_point(int i, double &time, double &x, double &y){
    time=tel[i*3];
    x=tel[i*3+1];
    y=tel[i*3+2];
}

// Class Game

void Game::run(double simulation_interval){
    while(projectile.get_position().get_y()>=0 && !projectile.intersect(target)){
        telemetry.add_point(time,projectile.get_position().get_x(),projectile.get_position().get_y());
        projectile.simulate_step(simulation_interval);
        time+=simulation_interval;
    }
}

