# -*- coding: utf-8 -*-
"""
Spyder Editor

This is a temporary script file.
"""

def print_recipe(recipe):
    """Pretty print recipe, which is a dictionary whose keys are
    ingredients and whose values are their corresponding amounts.
    """
    for k,v in recipe.items():
        print(f'{k}: {v}')
        

def read_recipe(recipe_file_name):
    """Read recipe file 'recipe_file_name', and return ingredients as a
    dictionary whose keys are ingredients and whose values are the
    corresponding amounts.
    """
    d=dict()
    with open(recipe_file_name,'r') as infile:
        lines=infile.readlines()
        for line in lines:
            if ',' in line:
                t=line.strip()
                data=line.split(',')
                d[data[0].strip()]=int(data[1].strip())
            else: 
                continue
    return d
        

def write_recipe(recipe, recipe_file_name):
    """Write recipe to a file named recipe_file_name."""
    with open(recipe_file_name,'w') as out:
        for k, v in recipe.items():
            out.write(k)
            out.write(',')
            out.write(str(v))
            out.write('\n')
            
def read_fridge(fridge_file_name):
    """Read fridge file 'fridge_file_name', and return the ingredients
    held in the given fridge as an ingredient=amount dictionary.
    """
    d=dict()
    with open(fridge_file_name,'r') as infile:
        lines=infile.readlines()
        for line in lines:
            if ',' in line:
                t=line.strip()
                data=line.split(',')
                if data[0].strip() in d:
                    d[data[0].strip()]+=int(data[1].strip())
                else:
                    d[data[0].strip()]=int(data[1].strip())
    return d
    

def is_cookable(recipe_file_name, fridge_file_name):
    """Return True if the contents of the fridge named fridge_file_name
    are sufficient to cook the recipe named recipe_file_name.
    """
    a=read_recipe(recipe_file_name)
    b=read_fridge(fridge_file_name)
    for ingredient,amount in a.items():
        if ingredient not in b.keys():
            return False
        else:
            if a[ingredient]>b[ingredient]:
                return False
            
    return True
    

def add_recipes(recipes):
    """Return a dictionary representing the sum of all of
    the recipe dictionaries in recipes.
    """
    d={}
    for i in range(len(recipes)):
        for key,value in recipes[i].items():
            if key in d:
                d[key]+=recipes[i][key]  
            else:
                d[key]=recipes[i][key]
    return d


def create_shopping_list(recipe_file_names, fridge_file_name):
    """Return the shopping list (a dictionary of ingredients and
    amounts) needed to cook the recipes named in recipe_file_names,
    after the ingredients already present in the fridge named
    fridge_file_name have been used.
    """
    l=[]
    d={}
    for i in recipe_file_names:
        b=read_recipe(i)
        l.append(b)
    r=add_recipes(l)
    f=read_fridge(fridge_file_name)
    for k,v in r.items():
        if k not in f:
            d[k]=v
        else:
            if f[k]<v:
                d[k]=(v-f[k])
            else:
                continue
    return d

def total_price(shopping_list, market_file_name):
    """Return the total price in millicents of the given shopping_list
    at the market named market_file_name.
    """
    m=read_recipe(market_file_name)
    price=0
    for k,v in m.items():
        if k in shopping_list:
            price+=v*shopping_list[k]
    return price

def find_cheapest(shopping_list, market_file_names):
    """Return the name of the market in market_file_names
    offering the lowest total price for the given shopping_list,
    together with the total price.
    """
    l=[]
    for i in range(len(market_file_names)):
        l.append(total_price(shopping_list, market_file_names[i]))
    m=l.index(min(l))
    return (market_file_names[m],min(l))

def update_fridge(fridge_file_name, recipe_file_names, market_file_names, new_fridge_file_name):
    """Compute the shopping list for the given recipes after the
    ingredients in fridge fridge_file_name have been used; find the cheapest
    market; and write the new fridge contents to new_fridge_file_name.
    Print the shopping list, the cheapest market name, and the total
    amount to be spent at that market.
    """
    s=create_shopping_list(recipe_file_names,fridge_file_name)
    print('Shopping list:')
    for k,v in s.items():
        print(f'{k}: {v}')
    print(f'Market: {find_cheapest(s, market_file_names)[0]}')
    print(f'Total cost: {find_cheapest(s, market_file_names)[1]}')   
    l=[s,read_fridge(fridge_file_name)]
    f=add_recipes(l)
    write_recipe(f,new_fridge_file_name)
        
            

    
    
    
    