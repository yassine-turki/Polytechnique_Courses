# -*- coding: utf-8 -*-
"""
Created on Fri Nov  5 15:48:28 2021

@author: USER
"""

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Nov  4 08:30:34 2021

@author: yassine.turki
"""

class Trobble:
    """Trobbles: simplified digital pets.

    Data Attributes:
    name -- the Trobble's name.
    sex -- 'male' or 'female'.
    age -- a non-negative integer
    health -- an integer between 0 (dead) and 10 (full health) inclusive
    hunger -- a non-negative integer (0 is not hungry)
    """
    def __init__(self,name,sex):
            self.name = name
            self.sex = sex
            self.age = 0
            self.health = 10
            self.hunger = 0
            
    def __str__(self):
        return f'{self.name}: {self.sex}, health {self.health}, hunger {self.hunger}, age {self.age}'
    
    def next_turn(self):
        """End the turn for the instance and recompute the attribute values
        for the next turn.
        """
        if self.health > 0:
            self.age += 1
            self.hunger += self.age
            self.health= self.health- (self.hunger//20)
        if self.health<0:
            self.health = 0
            
    def feed(self):
        """Feed the Trobble instance to decrease the hunger by 25
        with a minimum value of 0.
        """
        if self.hunger>25:
            self.hunger-=25
        else:
            self.hunger-= self.hunger
            
    def cure(self):
        """Increase the health of the instance by 5 up to the maximum of 10.
        """
        for i in range(5):
            if self.health<10:
                self.health+=1
        
    def have_fun(self):
        """Increase the health of the instance by 2 up to the maximum of 10 
    and increase the hunger by 4.
        """
        if self.health <= 8:
            self.health+=2
            self.hunger+=4
        if self.health==9:
            self.health+=2
            self.hunger+=4
            
    
    def is_alive(self):
        """Return True if the health of the instance is positive,
        otherwise False.
        """
        if self.health > 0:
            return True
        else:
            return False
        
def mate(trobble1, trobble2, name_offspring):
    """Check if the given Trobbles can procreate and if so give back a new
    Trobble that has the sex of trobble1 and the name 'name_offspring'.
    Otherwise, return None.
    """
    if trobble1.age >= 4 and trobble2.age >= 4 and trobble1.sex != trobble2.sex and trobble1.is_alive()== True and trobble2.is_alive()==True:
        o= Trobble(name_offspring, trobble1.sex)
        return o
    else:
        return None
        
        
        

def get_name():
    return input('Please give your new Trobble a name: ')

def get_sex():
    sex = None
    while sex is None:
        prompt = 'Is your new Trobble male or female? Type "m" or "f" to choose: '
        choice = input(prompt)
        if choice == 'm':
            sex = 'male'
        elif choice == 'f':
            sex = 'female'
    return sex

def get_action(actions):
    while True:
        prompt = f"Type one of {', '.join(actions.keys())} to perform the action: "
        action_string = input(prompt)
        if action_string not in actions:
            print('Unknown action!')
        else:
            return actions[action_string]
        
def play():
    name = get_name()
    sex = get_sex()
    trobble = Trobble(name, sex)
    actions = {'feed': trobble.feed, 'cure': trobble.cure}
    while trobble.is_alive():
        print('You have one Trobble named ' + str(trobble))
        action = get_action(actions)
        action()
        trobble.next_turn()
    print(f'Unfortunately, your Trobble {trobble.name} has died at the age of {trobble.age}')
        