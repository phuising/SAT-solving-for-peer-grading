# Advanced Topics in Computational Social Choice 2021
# Peer Grading
# On the basis of Holzman, Moulin - Impartial Nominations for a Prize


from pylgl import solve, itersolve
from math import factorial,comb
from itertools import combinations,permutations,product,chain,compress
import multiprocessing
import time

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



    # SAT-solving
    def worker_solve(queue,cnf):
        queue.put(isinstance(solve(cnf),list))
        
    def worker_calcCNF(queue,x,localVars): #first calculate all cnfs, then solve
        local = locals()
        queue.put(eval(x+"()",{**local, **localVars}))
    
    if outSize == False:
        outSize = [cnfAtLeastOne()+cnfAtMostK(),cnfAtMostK(),cnfAtLeastK()+cnfAtMostK()]
    else: 
        sizes = outSize
        outSize = []
        for x in sizes:
            outSize.append(eval(x))
    if outSizeLabels == False:
        outSizeLabels = ["0< <=K","<=K","=K"]
    
    # calculate all CNFs occurring in ax first
    axioms = ax
    axiomsSet = set([s.strip().replace("()","") for x in axioms for s in x.split("+")])
    axiomsDict = {}
    
    for x in axiomsSet:
        queue = multiprocessing.Queue()
        local = locals()
        localVars = {key: local.get(key) for key in ['cnfAnonymous','cnfImpartial','cnfMonotonous','cnfNegUnanimous','cnfNoDummy','cnfNoExclusion','cnfNonConstant','cnfNondictatorial','cnfPosUnanimous','cnfSurjective']}
        p = multiprocessing.Process(target=worker_calcCNF, name="calculate CNF", args=(queue,x,localVars))
        p.start()
        p.join(18000) #time to wait for CNF construction (for a single CNF)
        if p.is_alive():
            p.terminate()
            p.join()
            log = open("log.txt", 'a')
            log.write(time.strftime("%d-%m-%Y-%H:%M:%S", time.localtime())+" - killed n="+str(n)+", m="+str(m)+", k="+str(k)+" - calc CNF for "+x+'\n')
            log.close()
            continue
        axiomsDict[x] = queue.get()
        
    # filter ax for those entries which only make use of CNFs which we were able to compute
    axList = [[axiomsDict.get(s.strip().replace("()",""),0) for s in x.split("+")] for x in axioms]
    ax = [[c for y in x for c in y] for x in axList if 0 not in x]
    axLabels = list(compress(axLabels, [0 not in x for x in axList]))
    
    results = []
    for i in range(len(axLabels)):
        for j in range(len(outSizeLabels)):
            cnf = ax[i] + outSize[j]
            if not (i==0 and j==0) and (any(set(tuple([s.replace("'","") for s in r[r.find('(')+1:r.find(')')].split(', ')])).issubset(axLabels[i]) and 'False' in r for r in results) or any(set(tuple([s.replace("'","") for s in r[r.find('(')+1:r.find(')')].split(', ')]))==set(axLabels[i]) for r in results)):
                continue
                
            queue = multiprocessing.Queue()
            p = multiprocessing.Process(target=worker_solve, name="SAT solve", args=(queue,cnf))
            p.start()
            p.join(600) #time to wait for SAT solving (one instance)
            if p.is_alive():
                p.terminate()
                p.join()
                log = open("log.txt", 'a')
                log.write(time.strftime("%d-%m-%Y-%H:%M:%S", time.localtime())+" - killed n="+str(n)+", m="+str(m)+", k="+str(k)+" - SAT solving "+str(axLabels[i])+' '+str(outSizeLabels[j])+'\n')
                log.close()
                continue
            results.append(str(axLabels[i])+' '+str(outSizeLabels[j])+': '+ str(queue.get()))
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
    return list(chain.from_iterable(combinations(cList, r) for r in range(1,len(cList)+1)))     
     
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
