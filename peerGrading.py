# Advanced Topics in Computational Social Choice 2021
# Peer Grading
# On the basis of Holzman, Moulin - Impartial Nominations for a Prize

# Multi-ballots: every agent submits a ranking over their top m agents
# Multi-winner: up to k agents will be selected

from pylgl import solve, itersolve
from math import factorial,comb
from itertools import combinations,permutations,product
import scipy.special


# Basics: Voters, Profiles

n = 3
m = 1 # must be < n
k = 2 # must be < n+1


def allVoters():
    return range(n)

def allProfiles(): #((n-1)!/(n-m-1)!)^n many profiles
    return range((comb(n-1,m)*factorial(m)) ** n)

# Restricting the Range of Quantification

def voters(condition):
    return [i for i in allVoters() if condition(i)]

def profiles(condition):
    return [r for r in allProfiles() if condition(r)]
    
# Extracting preferences

def preference(i, r):
    base = comb(n-1,m)*factorial(m)
    return ( r % (base ** (i+1)) ) // (base ** i)
    
def preflist(i, r):
    """
    First calculate all subsets of size m of N\{i} and then for each subset all permutations (i.e. all orders on it)
    """
    preflists = [item for sublist in [list(permutations(selection)) for selection in list(combinations(voters(lambda j : j != i),m))] for item in sublist]
    return preflists[preference(i,r)]
    
def prefers(i, x, y, r):
    mylist =  preflist(i, r) 
    return mylist.index(x) < mylist.index(y)

def top(i, x, r):
    return preflist(i, r)[0] == x

# Literals
# (((n-1)!/(n-m-1)!)^n) * n many literals
def posLiteral(r, x):
    return r * n + x + 1

def negLiteral(r,x):
    return (-1) * posLiteral(r, x)

# Modelling Nomination Rules

# Size of Outcome Set

def cnfAtLeastOne():
    cnf = []
    for r in allProfiles():
        cnf.append([posLiteral(r,x) for x in allVoters()])
    return cnf    
    
def cnfAtMostK():
    """
    At most k agents will be selected
    """
    cnf = []
    for r in allProfiles():
        for c in list(combinations(allVoters(),k)):
            for y in voters(lambda j: j not in c):
                ll = [negLiteral(r,x) for x in c if x is not None]
                ll.append(negLiteral(r,y))
                cnf.append(ll)
    return cnf     
    
def cnfAtLeastK():
    """
    At least k agents will be selected
    """
    cnf = []
    for r in allProfiles():
        for c in list(combinations(allVoters(),n-k)):
            for y in voters(lambda j: j not in c):
                ll = [posLiteral(r,x) for x in c if x is not None]
                ll.append(posLiteral(r,y))
                cnf.append(ll)
    return cnf     

# Impartiality

def iVariants(i, r1, r2):
    return all(preference(j,r1) == preference(j,r2) for j in voters(lambda j : j!=i))
    
def cnfImpartial():
    cnf = []
    for i in allVoters():
        for r1 in allProfiles():
            for r2 in profiles(lambda r : iVariants(i,r1,r)):
                cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)],[posLiteral(r1,i),negLiteral(r2,i)]])
    return cnf
    
# Unanimity

def cnfNegUnanimous():
    """
    If no one lists i among their top m candidates, i won't be selected (only makes sense if k,m < n
    """
    cnf = []
    for i in allVoters():
        for r in profiles(lambda r : all(i not in preflist(j, r) for j in voters(lambda j : j != i))):
            cnf.append([negLiteral(r,i)])
    return cnf
    
def cnfPosUnanimous():
    """
    If everyone besides i has i as their top candidate, i will be selected
    """
    cnf = []
    for i in allVoters():
        for r in profiles(lambda r : all(top(j,i,r) for j in voters(lambda j : j != i))):
            cnf.append([posLiteral(r,i)])
    return cnf
    
# Monotonicity

def cnfMonotonous():
    """
    If agent i is selected and only agent i either gets ranked higher by an agent or newly gets into the top m of an agent, agent i is still selected
    """
    cnf = []
    for i in allVoters():
        for r1 in allProfiles():
            for j in voters(lambda x : i in preflist(x,r1) and not top(x,i,r1)):
                #single out the profile in which agent j ranks i one spot higher and everything else stays the same
                #r is a j-variant of r1, the top m of r and r1 are the same, i advances one spot in the ranking, the ranking stays fixed except for the swap
                for r2 in [r for r in profiles(lambda r : iVariants(j,r1,r) and sorted(preflist(j,r)) == sorted(preflist(j,r1))) if\
                (preflist(j,r).index(i) == preflist(j,r1).index(i)-1) and\
                all(preflist(j,r)[x] == preflist(j,r1)[x] for x in range(m) if x not in [preflist(j,r).index(i),preflist(j,r).index(i)+1])]:         
                    cnf.append([negLiteral(r1,i), posLiteral(r2,i)])
                    
                #profiles(lambda r : iVariants(j,r1,r) and sorted(preflist(j,r)) == sorted(preflist(j,r1)) and\
                #(preflist(j,r).index(i) == preflist(j,r1).index(i)-1) ):and\
                #all(preflist(j,r)[x] == preflist(j,r1)[x] for x in range(m) if x not in [preflist(j,r).index(i),preflist(j,r).index(i)+1]):
                #preflist(j,r)[:preflist(j,r).index(i)-1] == preflist(j,r1)[:preflist(j,r).index(i)-1] and\
                #preflist(j,r)[preflist(j,r).index(i)+1:] == preflist(j,r1)[preflist(j,r).index(i)+1:]:

    for i in allVoters():
        for r1 in allProfiles():
            for j in voters(lambda x : i not in preflist(x,r1)):
                #single out the profile in which agent j ranks i last among top m and everything else stays the same
                #r is a j-variant of r1, the top m-1 of r and r1 are the same, the m-th preference in r is agent i
                for r2 in profiles(lambda r : iVariants(j,r1,r) and preflist(j,r)[:m-2] == preflist(j,r1)[:m-2] and\
                preflist(j,r)[m-1] == i): 
                    cnf.append([negLiteral(r1,i), posLiteral(r2,i)])
    return cnf

# Surjectivity/Non-imposition

def cnfNoExclusion():
    """
    Every voter gets selected in some profile
    """
    cnf = []
    for i in allVoters():
        cnf.append([posLiteral(r,i) for r in allProfiles()])
    return cnf
  

def cnfSurjective():
    """
    Every group of size k is the outcome under some profile
    """
    cnf = []
    profilesList = allProfiles()
    for c in list(combinations(allVoters(),k)):
        for comb in list(product([x for x in c if x is not None],repeat=len(profilesList))):
            cnf.append([posLiteral(profilesList[k],comb[k]) for k in range(len(profilesList))])
    return cnf


"""
For any set of winners (of size at most k) there is a profile in which one of the voters in this set does not win. 
"""

def cnfNonConstant():
    
    cnf = []
    for j in range(1,k+1):
        for c in list(combinations(allVoters(),j)):
            clause = [negLiteral(r,v) for r in allProfiles() for v in c]
            cnf.append(clause)
    return cnf

# Export CNF
    
def saveCNF(cnf, filename):
    nvars = max([abs(lit) for clause in cnf for lit in clause])
    nclauses = len(cnf)
    file = open(filename, 'w')
    file.write('p cnf ' + str(nvars) + ' ' + str(nclauses) + '\n')
    for clause in cnf:
        file.write(' '.join([str(lit) for lit in clause]) + ' 0\n')
    file.close()

# Interpret Outcome

def interpret(variable):
    r = (variable - 1) // n
    x = (variable - 1) % n
    profilesList = [preflist(i,r) for i in allVoters()]
    print(str(profilesList) + ' --> ' + str(x))  

def extractRule(model):
    rule = []
    j=0
    for r in allProfiles():
        profilesList = [preflist(i,r) for i in allVoters()]
        rule.append(str(profilesList) + ' --> ' + str([(abs(i)-1) % n for i in model[n*j:n*(j+1)] if i>0]))
        j+=1
    for R in rule:
        print(R)
    return rule

# SAT-solving

#print('impartial + neg unan + pos unan together are satisfiable: ' + str(isinstance(solve(cnfAtLeastOne() + cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous()),list)))
#print('impartial + neg unan + noexcl + monotonous together are satisfiable: ' + str(isinstance(solve(cnfAtLeastOne() + cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfNoExclusion() + cnfMonotonous()),list)))
