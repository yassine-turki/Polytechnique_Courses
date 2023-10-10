import math
class Fraction:
    """ a class of rational numbers"""
    
    def __init__(self, numerator, denominator):
        self.__numerator= numerator
        if denominator==0:
            self.__denominator= denominator
        else:
            self.__denominator= denominator
    @property        
    def numerator(self):
        return self.__numerator
    @property 
    def denominator(self):
        return self.__denominator
            
            
    def reduce(self):
        """reduces the fraction, i.e. puts the fraction in the form where numerator and denominator are coprime and denominator is non-negative."""
        g=math.gcd(self.__numerator,self.__denominator)
        if g !=1:
            self.__denominator=self.__denominator//g
            self.__numerator=self.__numerator//g
        if self.__denominator<0:
            self.__numerator*=-1
            self.__denominator*=-1
            
    def __repr__(self):
        return f'Fraction{(self.numerator,self.denominator)}'
    def __str__(self):
        self.reduce()
        return f'{self.numerator}/{self.denominator}'
    def __eq__(self, o):
        self.reduce()
        o.reduce()
        return (self.denominator == o.denominator) and (self.numerator== o.numerator)
    def __ne__(self, o):
        return not ((self.denominator == o.denominator) and (self.numerator== o.numerator))
    
    def __add__(self,o):
        an=self.numerator
        on=o.numerator
        ad=self.denominator
        od=o.denominator
        if ad==od:
            return Fraction(an+on,ad)
        else:
            l=[an,ad,on,od]
            ad*=l[3]
            od*=l[1]
            an*=l[3]
            on*=l[1]
            num=an+on
            return Fraction(num,ad)
            
    def __sub__(self,o):
        an=self.numerator
        on=o.numerator
        ad=self.denominator
        od=o.denominator
        if ad==od:
            return Fraction(an-on,ad)
        else:
            l=[an,ad,on,od]
            ad*=l[3]
            od*=l[1]
            an*=l[3]
            on*=l[1]
            num=an-on
            return Fraction(num,ad)
            
    def __mul__(self, o):
        an=self.numerator
        on=o.numerator
        ad=self.denominator
        od=o.denominator
        return Fraction(an*on,ad*od)
    
    def __truediv__(self, o):
        an=self.numerator
        on=o.numerator
        ad=self.denominator
        od=o.denominator
        return Fraction(an*od,ad*on)
    def __neg__(self):
        an=self.numerator
        ad=self.denominator
        return Fraction(-an,ad)
        
        
            
        
         
        