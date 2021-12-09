from iteratePeerGrading import *

# check holzman thm3 and thm4
axDesc = [tuple(["I","NU","PU"]),tuple(["I","A","NC"])]
axCnf = ["cnfImpartial()+cnfNegUnanimous()+cnfPosUnanimous()","cnfImpartial()+cnfAnonymous()+cnfNonConstant()"] 
iterate(nRange=range(3,8),ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="holzman_thm3_thm4.txt",save=True)

# check axiom combinations which include I,NU,PU (holzman thm 4) for =K
axDesc = [tuple(["I","NU","PU"])] + [tuple(["I","NU","PU"]) + axioms  for axioms in giveCombinations(["M","NE","ND","A","S"])]
axComb = giveCombinations(["cnfMonotonous()","cnfNoExclusion()","cnfNondictatorial()","cnfAnonymous()","cnfSurjective()"])
axCnf = ["cnfImpartial()+cnfNegUnanimous()+cnfPosUnanimous()"] + ["cnfImpartial()+cnfNegUnanimous()+cnfPosUnanimous()+"+"+".join(combination) for combination in axComb] 
#iterate(nRange=range(3,8),ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="holzman_thm4_extensions.txt")


# check axiom combinations which include I,A,NC (holzman thm 3) for =K
axDesc = [tuple(["I","A","NC"])] + [tuple(["I","A","NC"]) + axioms  for axioms in giveCombinations(["M","NE","ND","PU","NU","S"])]
axComb = giveCombinations(["cnfMonotonous()","cnfNoExclusion()","cnfNondictatorial()","cnfPosUnanimous()","cnfNegUnanimous()","cnfSurjective()"])
axCnf = ["cnfImpartial()+cnfAnonymous()+cnfNonConstant()"] + ["cnfImpartial()+cnfAnonymous()+cnfNonConstant()+"+"+".join(combination) for combination in axComb] 
#iterate(nRange=range(3,8),ax=cnfCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="holzman_thm3_extensions.txt")

# combined
axDesc = [tuple(["I","NU","PU"])] + [tuple(["I","NU","PU"]) + axioms  for axioms in giveCombinations(["M","NE","ND","A","S"])]
axDesc = axDesc + [tuple(["I","A","NC"])] + [tuple(["I","A","NC"]) + axioms  for axioms in giveCombinations(["M","NE","ND","PU","NU","S"])]
axComb = giveCombinations(["cnfMonotonous()","cnfNoExclusion()","cnfNondictatorial()","cnfAnonymous()","cnfSurjective()"])
axCnf = ["cnfImpartial()+cnfNegUnanimous()+cnfPosUnanimous()"] + ["cnfImpartial()+cnfNegUnanimous()+cnfPosUnanimous()+"+"+".join(combination) for combination in axComb] 
axComb = giveCombinations(["cnfMonotonous()","cnfNoExclusion()","cnfNondictatorial()","cnfPosUnanimous()","cnfNegUnanimous()","cnfSurjective()"])
axCnf = axCnf + ["cnfImpartial()+cnfAnonymous()+cnfNonConstant()"] + ["cnfImpartial()+cnfAnonymous()+cnfNonConstant()+"+"+".join(combination) for combination in axComb] 
#iterate(nRange=range(3,8),ax=axCnf,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"],filename="holzman_thms_extensions.txt",save=True)
