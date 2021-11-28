# Advanced Topics in Computational Social Choice 2021
# Peer Grading
# On the basis of Holzman, Moulin - Impartial Nominations for a Prize


from pylgl import solve, itersolve
from math import factorial,comb
from itertools import combinations,permutations,product,chain


def main(n,m,k,ax,axLabels,outSize,outSizeLabels):

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

    """
    Impartiality assures that a voter cannot influent them being elected or not. Positive impartiality assures that 
    a voter cannot, by voting untruthfully, make herself elected (i.e. if she is not elected with her truthful preferences then
    in any i-variant she cannot be elected). Neative impartiality assures that she cannot, by voting untruthfully, make herself
    not elected i.e. if she is elected with her truthful preferences then in any i-variant she must also be elected)
    """

    def iVariants(i, r1, r2):
        return all(preference(j,r1) == preference(j,r2) for j in voters(lambda j : j!=i))
        
    def cnfNegImpartial():
        cnf = []
        for i in allVoters():
            for r1 in allProfiles():
                for r2 in profiles(lambda r : iVariants(i,r1,r)):
                    cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)]])
        return cnf


    def cnfPosImpartial():
        cnf = []
        for i in allVoters():
            for r1 in allProfiles():
                for r2 in profiles(lambda r : iVariants(i,r1,r)):
                    cnf.extend([[posLiteral(r1,i),negLiteral(r2,i)]])
        return cnf

    def cnfImpartial():
        cnf = cnfNegImpartial() + cnfPosImpartial()
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

    def cnfNonConstant():
        """
        For any set of winners (of size at most k) there is a profile in which one of the voters in this set does not win. 
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
    

    # SAT-solving
    
    if outSize == False:
        outSize = [cnfAtLeastOne()+cnfAtMostK(),cnfAtMostK(),cnfAtLeastK()+cnfAtMostK()]
    else: 
        sizes = outSize
        outSize = []
        for x in sizes:
            outSize.append(eval(x))
    if outSizeLabels == False:
        outSizeLabels = ["0< <=K","<=K","=K"]
    axioms = ax
    ax = []
    for x in axioms:
        ax.append(eval(x))
    
    results = []
    for i in range(len(axLabels)):
        for j in range(len(outSizeLabels)):
            cnf = ax[i] + outSize[j]
            results.append(str(axLabels[i])+' '+str(outSizeLabels[j])+': '+ str(isinstance(solve(cnf),list)))
    return results
    
def iterate(nRange,ax,axLabels,mRange=False,kRange=False,outSize=False,outSizeLabels=False,filename="./test_results/peerGrading.txt"):
    """
    Iterate the peer grading SAT solving for multiple values of n, m, k, different combinations of axioms 
    and different allowed sizes of the outcome set.
    
    Keyword arguments:
    nRange -- list of values for n
    mRange -- list of values for m, {1,..max(nRange)-1} is default
    kRange -- list of values for k, {1,..max(nRange)-1} is default
    ax -- list of strings, each containing python code to generate CNF which should go into SAT-solver
    axLabels -- list of labels identifying the CNFs in ax
    outSize -- list of strings, each containing python code to generate CNF which specify the size of the outcome set
    outSizeLabels -- list of labels identifying the CNFs in outSize
    filename -- string containing file name to write results into
    """
    if mRange == False:
        mRange = range(1,max(nRange))
    if kRange == False:
        kRange = range(1,max(nRange))
    
    count = 0
    
    for n in nRange:
        for k in (x for x in kRange if x < n):
            for m in (x for x in mRange if x < n):   
                if count != 0:
                    file = open(filename, 'a')
                else: 
                    file = open(filename, 'w')
                file.write(str(n)+','+str(m)+','+str(k)+':\n')   
                print(str(n)+','+str(m)+','+str(k)+': ')
                
                for r in main(n,m,k,ax,axLabels,outSize,outSizeLabels):
                    file.write(r +'\n') 
                    print(r)
                    
                file.write('\n')
                print('-------------------------------------')
                file.close()
                
                count += 1
                
def giveCombinations(cList):
    """
    Return all possible subsets of size at least 2 of a list
    """
    return list(chain.from_iterable(combinations(cList, r) for r in range(2,len(cList)+1)))     
     
if __name__ == "__main__":
    # all combinations for all sizes
    axDesc = giveCombinations(["I","NU","PU","M","NE","S"])
    axComb = giveCombinations(["cnfImpartial()","cnfNegUnanimous()","cnfPosUnanimous()","cnfMonotonous()","cnfNoExclusion()","cnfSurjective()"])
    axCnf = ["+".join(combination) for combination in axComb]
    iterate(nRange=range(3,5),ax=axCnf,axLabels=axDesc)
    
    # all combinations which include impartiality for size =k
    axDesc = [tuple("I") + axioms  for axioms in giveCombinations(["NU","PU","M","NE","S"])]
    axComb = giveCombinations(["cnfNegUnanimous()","cnfPosUnanimous()","cnfMonotonous()","cnfNoExclusion()","cnfSurjective()"])
    axCnf = ["cnfImpartial()+"+"+".join(combination) for combination in axComb]
    iterate(nRange=range(3,5),ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"])
    
    # holzman  for size =k
    axDesc = ["I,NU,PU","I,A,NE"]
    cnfComb = ["cnfNegUnanimous()+cnfPosUnanimous()+cnfImpartial()","cnfAnonymous()+cnfNoExclusion()+cnfImpartial()"]
    iterate(nRange=range(3,5),ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"])
    
    # single instance
    axDesc = ["I,NU,M"]
    cnfComb = ["cnfNegUnanimous()+cnfPosUnanimous()+cnfMonotonousl()"]
    iterate(nRange=[3],mRange=[2],kRange=[2],ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastOne()+cnfAtMostK()"],outSizeLabels=["0< =K"])
