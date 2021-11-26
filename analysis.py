from iteratePeerGrading import *
from peerGrading import *
# need to adjust n,m,k in peerGrading.py before using it in this script

# check Holzman results for =K
axDesc = ["I,NU,PU"]
cnfComb = ["cnfNegUnanimous()+cnfPosUnanimous()+cnfImpartial()"]
iterate(nRange=range(3,5),ax=cnfComb,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="holzman.txt")

# check axiom combinations with impartiality and =K for single instance
axDesc = [tuple("I") + axioms  for axioms in giveCombinations(["NU","PU","M","NE","S"])]
axComb = giveCombinations(["cnfNegUnanimous()","cnfPosUnanimous()","cnfMonotonous()","cnfNoExclusion()","cnfSurjective()"])
axCnf = ["cnfImpartial()+"+"+".join(combination) for combination in axComb]
iterate(nRange=[4],mRange=[2],kRange=[2],ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="pg_422.txt")

# check axiom combinations which include I,NU,PU (holzman) for =K for single instance
axDesc = [tuple(["I","NU","PU"]) + axioms  for axioms in giveCombinations(["M","NE","S"])]
axComb = giveCombinations(["cnfMonotonous()","cnfNoExclusion()","cnfSurjective()"])
axCnf = ["cnfImpartial()+cnfNegUnanimous()+cnfPosUnanimous()+"+"+".join(combination) for combination in axComb]
iterate(nRange=[4],mRange=[2],kRange=[2],ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="pg_422.txt")

# extract holzman rule for =K and single instance
rule = extractRule(solve(cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous()))
file = open("pg_422.txt", 'a')
file.write('4,2,2 - I,NU,PU,=K:\n-----------------------------------------------\n')
for r in rule:
    file.write(r+'\n')   
file.close()

# extract well-behaved holzman rule for =K and single instance
rule = extractRule(solve(cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous() + cnfMonotonous() + cnfNoExclusion()))
file = open("pg_322.txt", 'a')
file.write('3,2,2 - I,NU,PU,M,NE,=K:\n-----------------------------------------------\n')
for r in rule:
    file.write(r+'\n')   
file.close()

# extract number of (holzman) rules for single instance
file = open("pg_422.txt", 'a')
file.write("total number of =K rules: "+str(len(list(itersolve(cnfAtLeastK() + cnfAtMostK()))))+'\n')   
file.write("number of I,NU,PU,=K rules: "+str(len(list(itersolve(cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous()))))+'\n')
#file.write("number of I,NU,PU,M,NE,=K rules: "+str(len(list(itersolve(cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous()+cnfMonotonous() + cnfNoExclusion()))))+'\n')  
file.close()

# extract all possible holzman rules for single instance
file = open("pg_322.txt", 'a')
file.write('3,2,2 - I,NU,PU,=K:\n-----------------------------------------------\n')
for R in list(itersolve(cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous())):
    rule = extractRule(R)  
    for r in rule:
        file.write(r+'\n')   
    file.write('-----------------------------------------------\n')
file.close()




rule = extractRule(solve(cnfAtLeastK() + cnfAtMostK() + cnfImpartial() + cnfNegUnanimous() + cnfPosUnanimous()))
file = open("pg_422.txt", 'a')
file.write('4,2,2 - I,NU,PU,=K:\n-----------------------------------------------\n')
for r in rule:
    file.write(r+'\n')   
file.close()

