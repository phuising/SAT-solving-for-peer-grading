# Advanced Topics in Computational Social Choice 2021
# Peer Grading
# On the basis of Holzman, Moulin - Impartial Nominations for a Prize

# Multi-ballots: every agent submits a ranking over their top m agents
# Multi-winner: up to k agents will be selected

from pylgl import solve, itersolve
from math import factorial,comb
from itertools import combinations,permutations,product


# Basics: Voters, Profiles

n = 3
m = 2 # must be < n
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

def posLiteral(r, x):# (((n-1)!/(n-m-1)!)^n) * n many literals
    return r * n + x + 1

def negLiteral(r,x):
    return (-1) * posLiteral(r, x)
    
def posQLiteral(r, c):
    return (((comb(n-1,m)*factorial(m)) ** n) * n) + 1 + r * comb(n,k) + list(combinations(allVoters(),k)).index(c)

def negQLiteral(r,c):
    return (-1) * posQLiteral(r, c)

def posDLiteral(r1, r2, x):
    prof = list(allProfiles())
    return (((comb(n-1,m)*factorial(m)) ** n) * n) + 1 + (len(prof))*comb(n,k) + \
     x * (len(prof)**2) + list(product(prof, prof)).index((r1,r2))

def negDLiteral(r1, r2, x):
    return (-1) * posDLiteral(r1, r2, x)

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
    """
    Impartiality assures that a voter cannot influence them being elected or not,
    i.e. if she is elected with her truthful preferences then in any i-variant she must also be elected)
    """
    cnf = []
    for i in allVoters():
        for r1 in allProfiles():
            for r2 in profiles(lambda r : iVariants(i,r1,r)):
                cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)]])
    return cnf
    
# Unanimity

def cnfNegUnanimous():
    """
    For m == n-1: If everyone besides i has i as their lowest candidate, i will not be selected
    For m != n-1: If no one lists i among their top m candidates, if i is selected, so are all other candidates with nonempty support
    """
    cnf = []
    if m==n-1:
        for i in allVoters():
            for r in profiles(lambda r : all(i == preflist(j, r)[m-1] for j in voters(lambda j : j != i))):
                cnf.append([negLiteral(r,i)])
    else:
        for i in allVoters():
            for r in profiles(lambda r : all(i not in preflist(j, r) for j in voters(lambda j : j != i))):
                for j in voters(lambda x : any(x in preflist(y,r) for y in allVoters())):
                    cnf.append([negLiteral(r,i),posLiteral(r,j)])
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
    for c in list(combinations(allVoters(),k)):
        cnf.append([posQLiteral(r,c) for r in allProfiles()])
    
    for r in allProfiles():
        for c in list(combinations(allVoters(),k)): 
            for x in c:
                cnf.append([negQLiteral(r,c),posLiteral(r,x)])
            clause=[negLiteral(r,x) for x in c]
            clause.append(posQLiteral(r,c))
            cnf.append(clause)   
    return cnf

def cnfNonConstant():
    """
    For any set of winners (of size k) there is a profile in which one of the voters in this set does not win. 
    """
    
    cnf = []
    for c in list(combinations(allVoters(),k)):
        clause = [negLiteral(r,v) for r in allProfiles() for v in c]
        cnf.append(clause)
    return cnf

# Anonymity

def vPermutation(r1, r2):
    return sorted([preflist(i,r1) for i in allVoters()]) == sorted([preflist(j,r2) for j in allVoters()])

def cnfAnonymous():
    cnf = []
    for r1 in allProfiles():
        for r2 in profiles(lambda r : vPermutation(r,r1)):
            for x in allVoters():
                cnf.extend([[negLiteral(r1,x),posLiteral(r2,x)],[posLiteral(r1,x),negLiteral(r2,x)]])
    return cnf
    
# Non-dictatorship

def cnfNondictatorial():
    """
    Call i an dictator if the outcome set consists always of the top k-1 voters in i's ballots and i herself
    """
    cnf = []
    for i in allVoters():
        clause = []
        for r in allProfiles():
            for j in voters(lambda x : x in preflist(i,r)[:k-1] or x == i):
                clause.append(negLiteral(r,j))
        cnf.append(clause)
    return cnf 


#No dummy 

"""
For every voter there there is a profile such that there is a voter j such that j wins in this profile 
and j does not win in one of its i-Variants. 
For any voter we add a disjunction of D-variables indexed with  a profile r1 its i-Variant and a voter j 
which means that j wins in r1 but not in r2. 
"""

def cnfNoDummy():
    cnf = []
    for i in allVoters():
        clause = []
        for r1 in allProfiles():
            for r2 in profiles(lambda r : iVariants(i,r1,r)):
                for j in allVoters():
                    clause.append(posDLiteral(r1,r2,j))
                    cnf.append([negDLiteral(r1,r2,j), posLiteral(r1,j)])
                    cnf.append([negDLiteral(r1,r2,j), negLiteral(r2,j)])
                    cnf.append([posDLiteral(r1,r2,j), negLiteral(r1,j), posLiteral(r2,j)])
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
