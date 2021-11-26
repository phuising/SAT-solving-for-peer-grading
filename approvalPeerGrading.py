########################################
## Peer Grading With Approval Ballots ##
########################################

"""We are concerned with a setting in which the agents submit approval ballots that are subsets of the set of voters/alternatives.
The only restriction is that they cannot approve of themselves.""" # QUESTION: does this restriction make sense in this context? 

from pylgl import solve, itersolve
from math import factorial, comb
from itertools import chain, combinations

# Initiate values.
n = 3 # number of voters
m = 1 # number of agents that can maximally be approved of
k = 1 # number of agents selected

## BASICS ############################################################################################################################

# Voters and profiles.

def allVoters():
    return range(n)

def numPossibleBallots():
    # Check for each permissible size of subset how many combinations of n-1 (voters can't approve of themselves)
    # there are with that size. Sum to find total amount of permissible ballots per voter.
    num_possible_ballots = 0
    for size in range(m+1):
        num_possible_ballots += comb(n-1,size)
    return num_possible_ballots

def allApprovalProfiles():
    return range(numPossibleBallots()**n)

# Restricting quantification

def voters(condition):
    return [i for i in allVoters() if condition(i)]

def approvalProfiles(condition):
    return [r for r in allApprovalProfiles() if condition(r)]

# Extracting approval sets.
def approvalIndex(i,r):
    """Each voter has numPossibleBallots() possible ballots. Think of profiles as number with n digits in base
    numPossibleBallots(), where the nth digit from the back represents the approval set of voter n in that profile."""
    return ( r % (numPossibleBallots() ** (i+1)) ) // (numPossibleBallots() ** i)

def approvalSet(i,r):
    """Return the approval ballot submitted by voter i in profile r."""
    possible_ballots = []
    for size in range(m+1):
        for approval_set in [list(x) for x in list(combinations(voters(lambda j: j != i),size))]:
            possible_ballots.append(approval_set)
    return possible_ballots[approvalIndex(i,r)]

def approves(i,j,r):
    """Returns True if i approves of j in profile r and False otherwise."""
    return j in approval_set(i,r)

# Literals representing a voter (not) being elected in some profile.

def posLiteral(r, x):
    """Voter x is elected in profile r."""
    return r * n + x + 1

def negLiteral(r,x):
    """Voter x is not elected in profile r."""
    return (-1) * posLiteral(r, x)

## AXIOMS ############################################################################################################################

# Size of Outcome Set

def cnfAtLeastOne():
    """The outcome contains at least one voter."""
    cnf = []
    for r in allApprovalProfiles():
        cnf.append([posLiteral(r,x) for x in allVoters()])
    return cnf    
    
def cnfAtMostK():
    """At most k agents will be selected."""
    cnf = []
    # If k=n then the requirement is always satisfied.
    if k == n:
        cnf.append([True]) # DOES THIS WORK?
    # If k<n then in any combination of k+1 voters, there must be at least one loser.
    else:
        for r in allApprovalProfiles():
            for combo in list(combinations(allVoters(),k+1)):
                cnf.append([negLiteral(r,i) for i in combo])
    return cnf

print(len(cnfAtMostK()))

# def cnfAtLeastK():
#     """
#     At least k agents will be selected
#     """
#     cnf = []
#     for r in allProfiles():
#         for c in list(combinations(allVoters(),n-k)):
#             for y in voters(lambda j: j not in c):
#                 ll = [posLiteral(r,x) for x in c if x is not None]
#                 ll.append(posLiteral(r,y))
#                 cnf.append(ll)
#     return cnf     

# # Impartiality

# def iVariants(i, r1, r2):
#     return all(preference(j,r1) == preference(j,r2) for j in voters(lambda j : j!=i))
    
# def cnfImpartial():
#     cnf = []
#     for i in allVoters():
#         for r1 in allProfiles():
#             for r2 in profiles(lambda r : iVariants(i,r1,r)):
#                 cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)],[posLiteral(r1,i),negLiteral(r2,i)]])
#     return cnf

## TESTING #########################################################
