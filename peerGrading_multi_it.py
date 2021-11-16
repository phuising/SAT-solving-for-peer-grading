# Advanced Topics in Computational Social Choice 2021
# Peer Grading
# On the basis of Holzman, Moulin - Impartial Nominations for a Prize

# Multi-ballots: every agent submits a ranking over their top m agents
# Multi-winner: up to k agents will be selected

# TO DO: IMPLEMENT ANONYMITY, SURJECTIVITY, COMMITEE MONOTONICITY
# DO THESE AXIOMS REDUCE TO THE STD AXIOMS FOR M=K=1?


from pylgl import solve, itersolve
from math import factorial,comb
from itertools import combinations,permutations,product,chain

def axCombinations(axList):
    return list(chain.from_iterable(combinations(axList, r) for r in range(2,len(axList)+1)))


def main(n, m, k):

    # Basics: Voters, Profiles
    
    def allVoters():
        return range(n)

    def allProfiles():
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

    def posLiteral(r, x):
        return r * n + x + 1

    def negLiteral(r,x):
        return (-1) * posLiteral(r, x)

    # Modelling Nomination Rules

    def cnfAtLeastOne():
        cnf = []
        for r in allProfiles():
            cnf.append([posLiteral(r,x) for x in allVoters()])
        return cnf    

    def cnfOutcomeSize():
        """
        At most k agents will be selected; SHOULD IT BE EXACTLY K?
        """
        cnf = []
        for r in allProfiles():
            for c in list(combinations(allVoters(),k)):
                for y in voters(lambda j: j not in c):
                    ll = [negLiteral(r,x) for x in c if x is not None]
                    ll.append(negLiteral(r,y))
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

    # SAT-solving
    
    results = []
    strComb = axCombinations(["I","NU","PU","M","NE","S"])
    cnfComb = axCombinations([cnfImpartial(),cnfNegUnanimous(),cnfPosUnanimous(),cnfMonotonous(),cnfNoExclusion(),cnfSurjective()])
    for A in range(len(strComb)):
        cnfList = cnfComb[A]
        cnf = [item for sublist in cnfList for item in sublist] + cnfAtLeastOne() + cnfOutcomeSize()
        results.append(str(strComb[A])+': '+ str(isinstance(solve(cnf),list)))
    return results
    
    

for n in range(3,5):
    for k in range(1,n):
        for m in range(1,n):     
            file = open('pg_nmk_ax.txt', 'a')
            file.write(str(n)+','+str(m)+','+str(k)+':\n')   
            print(str(n)+','+str(m)+','+str(k)+': ')
            
            for r in main(n,m,k):
                file.write(r +'\n') 
                print(r)
                
            file.write('\n')
            print('-------------------------------------')
            file.close()
            #print(str(n)+','+str(m)+','+str(k)+': '+str(main(n,m,k)))
