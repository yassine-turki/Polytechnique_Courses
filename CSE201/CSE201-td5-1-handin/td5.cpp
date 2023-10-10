#include <iostream>
#include <math.h>

#include "td5.hpp"
double PI = 3.14159265;
const double G_CONSTANT = 9.8;

// -----------------------------------------------------------------------------
// Exercise 1
// -----------------------------------------------------------------------------

// Define the arithmetic operators
Coordinate Coordinate::operator+(Coordinate& other) {
    return (Coordinate(x+other.get_x(),y+other.get_y()));
}
Coordinate Coordinate::operator-() {
    return (Coordinate(-x,-y));
}
Coordinate Coordinate::operator-(Coordinate& other) {
    return (Coordinate(x-other.get_x(),y-other.get_y()));
}
// -----------------------------------------------------------------------------
// Exercise 2
// -----------------------------------------------------------------------------

// Define the comparison operators
bool Coordinate::operator==(Coordinate& other) {
    if(x==other.get_x() && y==other.get_y()){
        return 1;
    }
    else{
        return 0;
    }
}

bool Coordinate::operator!=(Coordinate& other) {
    if(x!=other.get_x() || y!=other.get_y()){
        return 1;
    }
    else{
        return 0;
    }
}
bool Coordinate::operator>(Coordinate& other) {
    if(x>other.get_x() && y>other.get_y()){
        return 1;
    }
    else{
        return 0;
    }
}
bool Coordinate::operator<(Coordinate& other) {
    if(x<other.get_x() && y<other.get_y()){
        return 1;
    }
    else{
        return 0;
    }
}
double Coordinate::x_max=0;
double Coordinate::y_max=0;

// -----------------------------------------------------------------------------
// Exercise 3
// -----------------------------------------------------------------------------

void Coordinate::reset_max(){
    x_max=0;
    y_max=0;
}
double Coordinate::get_x_max(){
    return x_max;
}

double Coordinate:: get_y_max(){
    return y_max;
}


#if EXERCISE_4 == 1
// -----------------------------------------------------------------------------
// Exercise 4
// -----------------------------------------------------------------------------

DroppingProjectile::DroppingProjectile(Coordinate position_other,
                                       double magnitude,
                                       double angle) {
    position=position_other;
    velocity_x=magnitude*cos(angle*PI/180);
    velocity_y=magnitude*sin(angle*PI/180);
}

DroppingProjectile::DroppingProjectile() {
  position=Coordinate();
  double mag=1;
  double angle=45;
  velocity_x=mag*cos(angle*PI/180);
  velocity_y=mag*sin(angle*PI/180);

}

DroppingProjectile::~DroppingProjectile() {
  // IMPLEMENT YOUR CODE HERE
}

void DroppingProjectile::simulate_step(double time_interval) {
    if (velocity_y>0){
    position=Coordinate(position.get_x()+velocity_x*time_interval,position.get_y()+velocity_y*time_interval-0.5*G_CONSTANT*pow(time_interval,2));
    velocity_y=velocity_y-G_CONSTANT*time_interval;
}
    else{
        position=Coordinate(position.get_x(),position.get_y()+velocity_y*time_interval-0.5*G_CONSTANT*pow(time_interval,2));
        velocity_y=velocity_y-G_CONSTANT*time_interval;
        velocity_x=0;
    }
}
#endif

// -----------------------------------------------------------------------------
// Exercise 6
// -----------------------------------------------------------------------------

ListNode::ListNode(Projectile projectile) {
  element=projectile;
}

Projectile ListNode::get_projectile() {
  // IMPLEMENT YOUR CODE HERE
  return element; // you can change this line, we added it to avoid a compilation warning
}

void ListNode::set_next(ListNode* next) {
  this->next=next;
}

ListNode* ListNode::get_next() {
  // IMPLEMENT YOUR CODE HERE
  return next; // you can change this line, we added it to avoid a compilation warning
}


// -----------------------------------------------------------------------------
// Exercise 7
// -----------------------------------------------------------------------------

List::List() {
  // IMPLEMENT YOUR CODE HERE
    head=nullptr;
    tail=nullptr;
}

List::~List() {
  // IMPLEMENT YOUR CODE HERE
   while(head!=tail && head!=nullptr){
       ListNode* tmp=head;
       head=head->get_next();
       delete tmp;
   }
}

bool List::is_empty() {
  // IMPLEMENT YOUR CODE HERE
    if (head==nullptr && tail==nullptr){
        return 1;
    }
    else{
        return 0; // you can change this line, we added it to avoid a compilation warning
    }
}

void List::append(Projectile projectile) {
  // IMPLEMENT YOUR CODE HERE
    ListNode* node = new ListNode(projectile);
    if (head==nullptr&& tail==nullptr){
      head=node;
      tail=node;
    }
    else{
        tail->set_next(node);
        tail=node;
        node->set_next(nullptr);

}
}

Projectile List::remove_from_top() {
  // IMPLEMENT YOUR CODE HERE
  if(head!=tail){
  ListNode* tmp=head;
  head=head->get_next();
  Projectile p= tmp->get_projectile();
  delete tmp;
  return p;// you can change this line, we added it to avoid a compilation warning
}
  else{
      ListNode* tmp=head;
      Projectile p= tmp->get_projectile();
      head=nullptr;
      tail=nullptr;
      delete tmp;
      return p;
  }
}


// -----------------------------------------------------------------------------
// Exercise 8
// -----------------------------------------------------------------------------

PtrListNode::PtrListNode(Projectile *projectile) {
  // IMPLEMENT YOUR CODE HERE
    element=projectile;
}

Projectile* PtrListNode::get_projectile() {
  // IMPLEMENT YOUR CODE HERE
  return element; // you can change this line, we added it to avoid a compilation warning
}

void PtrListNode::set_next(PtrListNode* next) {
  // IMPLEMENT YOUR CODE HERE
   this->next=next;
}


PtrListNode* PtrListNode::get_next() {
  // IMPLEMENT YOUR CODE HERE
  return next; // you can change this line, we added it to avoid a compilation warning
}

PtrList::PtrList() {
  // IMPLEMENT YOUR CODE HERE
    head=nullptr;
    tail=nullptr;
}

PtrList::~PtrList() {
  // IMPLEMENT YOUR CODE HERE
    while(head!=tail && head!=nullptr){
        PtrListNode* tmp=head;
        head=head->get_next();
        delete tmp;
    }
}

bool PtrList::is_empty() {
  // IMPLEMENT YOUR CODE HERE
    if (head==nullptr && tail==nullptr){
        return 1;
    }
    else{
        return 0; // you can change this line, we added it to avoid a compilation warning
    } // you can change this line, we added it to avoid a compilation warning
}

void PtrList::append(Projectile *projectile) {
  // IMPLEMENT YOUR CODE HERE
    PtrListNode* node = new PtrListNode(projectile);
    if (head==nullptr&& tail==nullptr){
      head=node;
      tail=node;
    }
    else{
        tail->set_next(node);
        tail=node;
        node->set_next(nullptr);
}
}

Projectile* PtrList::remove_from_top() {
  // IMPLEMENT YOUR CODE HERE
    if(head!=tail){
    PtrListNode* tmp=head;
    head=head->get_next();
    Projectile *p= tmp->get_projectile();
    delete tmp;
    return p;// you can change this line, we added it to avoid a compilation warning
  }
    else{
        PtrListNode* tmp=head;
        Projectile *p= tmp->get_projectile();
        head=nullptr;
        tail=nullptr;
        delete tmp;
        return p; // you can change this line, we added it to avoid a compilation warning
}
}

// -----------------------------------------------------------------------------
// DO NOT MODIFY THE FOLLOWING CODE
// -----------------------------------------------------------------------------

double Coordinate::get_distance(Coordinate other) {
  return hypot(x - other.get_x(), y - other.get_y());
}

Projectile::Projectile(Coordinate position_other,
                       double magnitude,
                       double angle) {
  double PI = 3.14159265;

  position = position_other;
  velocity_x = magnitude * cos(angle * PI / 180);
  velocity_y = magnitude * sin(angle * PI / 180);
}

Projectile::Projectile() : Projectile(Coordinate(),1,45){

}

Projectile::~Projectile() {};

Coordinate Projectile::get_position() {
  return position;
}

double Projectile::get_velocity_x() {
  return velocity_x;
}

double Projectile::get_velocity_y() {
  return velocity_y;
}

void Projectile::simulate_step(double time_interval) {
  const double g = 9.8;

  position = Coordinate(position.get_x() + velocity_x * time_interval,
                        position.get_y() + velocity_y * time_interval +
                        0.5 * (-g) * time_interval * time_interval);
  velocity_y = velocity_y - g * time_interval;
}

bool Projectile::operator==(const Projectile& other) {
  return (position.get_x() == other.position.get_x() &&
          position.get_y() == other.position.get_y() &&
          velocity_x == other.velocity_x &&
          velocity_y == other.velocity_y);
}

void simulate_full_trajectory(std::ostream &out, double simulation_interval,
                              Projectile *projectile_ptr) {
  while (projectile_ptr->get_position().get_y() >= 0)
    projectile_ptr->simulate_step(simulation_interval);
}

#if EXERCISE_4 == 1
void simulate_full_trajectory(std::ostream &out, double simulation_interval,
                              DroppingProjectile &projectile) {
  while (projectile.get_position().get_y() >= 0)
    projectile.simulate_step(simulation_interval);
}

#endif
