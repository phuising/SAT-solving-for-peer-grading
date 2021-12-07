########################################
## Peer Grading With Approval Ballots ##
########################################

"""We are concerned with a setting in which the agents submit approval ballots that are subsets of the set of voters/alternatives.
The only restriction is that they cannot approve of themselves.""" 

from pylgl import solve, itersolve
from math import factorial, comb
from itertools import chain, combinations

# Initiate values.
n = 3 # number of voters
m = 2 # number of agents that can maximally be approved of
k = 1 # number of agents selected

## BASICS ############################################################################################################################

# Voters and profiles.

def allVoters():
    return range(n)

def numPossibleBallots():
    """Returns the number of possible ballots that a voter can submit given the limit of m approvals. 
    Note that a voter may submit an empty ballot."""
    # Check for each permissible size of subset how many combinations of n-1 voters
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

# Extracting approval sets and related information.
def approvalIndex(i,r):
    """Each voter has numPossibleBallots() possible ballots. Think of profiles as numbers with n digits in base
    numPossibleBallots(), where the nth digit from the back represents the approval set of voter n in that profile."""
    return ( r % (numPossibleBallots() ** (i+1)) ) // (numPossibleBallots() ** i)

def approvalSet(i,r):
    """Return the approval ballot submitted by voter i in profile r."""
    # Construct list of all possible ballots.
    possible_ballots = []
    for set_size in range(m+1):
        # Add each combination of set_size voters as a list to possible_ballots.
        for approval_set in [list(x) for x in list(combinations(voters(lambda j: j != i),set_size))]:
            possible_ballots.append(approval_set)
    # Return the ballot corresponding to the approval index i has in r.
    return possible_ballots[approvalIndex(i,r)]

def approves(i,j,r):
    """Returns True if i approves of j in profile r and False otherwise."""
    return j in approvalSet(i,r)

def approvalScore(r,i):
    """Returns the number of people that have voted for i."""
    return len([i for i in voters(lambda j: approves(j,i,r))])

def completeApproval(r,i):
    """Returns True if in r every voter other than i approves of i."""
    return approvalScore(r,i)==n-1

def positiveApproval(r,i):
    """Returns True if at least one voter in r approves of i."""
    return approvalScore(r,i)>0

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
    """At most k agents will be selected. 
    It must be the case that k<n, else the cnf will be empty and unsatisfiable."""
    cnf = []
    # For each profile, in any selection of k+1 agents, at least one must be a loser.
    for r in allApprovalProfiles():
        for combo in list(combinations(allVoters(),k+1)):
            cnf.append([negLiteral(r,i) for i in combo])
    return cnf

def cnfAtLeastK():
    """At least k agents will be selected."""
    cnf = []
    # For any profile, there can never be n-k+1 (or more) losers (for then there would be at most k-1 winners)
    # i.e., any set of n-k+1 voters, there has to be at least one winnner
    for r in allApprovalProfiles():
        for combo in list(combinations(allVoters(),n-k+1)):
            cnf.append([posLiteral(r,i) for i in combo])
    return cnf

# Impartiality

def iVariants(i, r1, r2):
    """r1 and r2 are i variants if they agree on all voters except i."""
    return all(approvalSet(j,r1) == approvalSet(j,r2) for j in voters(lambda j : j!=i))
    
def cnfImpartial():
    """No voter can make the difference between themselves being elected or not. I.e.,
    i variants must agree on whether or not i gets elected."""
    cnf = []
    for i in allVoters():
        for r1 in allApprovalProfiles():
            # List comprehension generates list of all i variants of r1 that are *larger than r1* for symmetry breaking.
            for r2 in [prof for prof in approvalProfiles(lambda r: iVariants(i,r1,r)) if prof > r1]:
                # If i wins in r1, then i wins in r2 and same for losing. (This implies that if i wins/loses in r2 she also
                # does so in r1.)
                cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)],[posLiteral(r1,i),negLiteral(r2,i)]])
    return cnf

# Unanimity

def cnfCondPosUnanimous():
    """No one with incomplete support is elected while someone with complete support is not.
    In other words for any two agents i and j, where the former has complete support and the latter does not,
    if i is not elected, then neither is j."""
    cnf = []
    for r in allApprovalProfiles():
        for i in voters(lambda v: completeApproval(r,v)):
            for j in voters(lambda v: not completeApproval(r,v)):
                cnf.append([posLiteral(r,i),negLiteral(r,j)])
    return cnf

def cnfCondNegUnanimous():
    """If some agent with no support is elected, then everyone with at least one vote is elected as well."""
    cnf = []
    for r in allApprovalProfiles():
        for i in voters(lambda v: positiveApproval(r,v)):
            for j in voters(lambda v: not positiveApproval(r,v)):
                cnf.append([posLiteral(r,i),negLiteral(r,j)])
    return cnf

def cnfNewUnanimity():
    """The agents with maximal approval scores are elected. There is no one who is elected while there is an agent with a higher approval
    score who is not elected. I.e., for any agent i, and agent j with a lower approval score, 
    if the former is not elected, nor is the latter"""
    cnf = []
    for r in allApprovalProfiles():
        for i in allVoters():
            for j in voters(lambda k: approvalScore(r,i) > approvalScore(r,k)):
                cnf.append([posLiteral(r,i),negLiteral(r,j)])
    return cnf

# Monotonicity
    
def cnfMonotonicity():
    """For any voter i, if i is elected in r1 and r1 and r2 are j-variants, then if j does not approve of i in r1,
    and j approves of i in r2 besides or instead of some of the approved voters in r1,
    then i should be among the winners in r2."""
    cnf = []
    for i in allVoters():
        for r1 in allApprovalProfiles():
            # Consider only those voters that don't approve of i in r1
            for j in voters(lambda l: l != i and not approves(l,i,r1)):
                # Consider only those j-variants of r1 in which j votes for i besides/instead of some of the agents approved of in r1
                for r2 in approvalProfiles(lambda r: iVariants(j,r1,r) and approves(j,i,r) and all(elem in approvalSet(j,r1) for elem in approvalSet(j,r) if elem != i)):
                    # If i wins in r1, i should win in r2
                    cnf.append([negLiteral(r1,i),posLiteral(r2,i)])
    return cnf

# Anonymity

def cnfAnonymity():
    """If two profiles agree on the approval scores of all agents, then they should yield they same outcome."""
    cnf = []
    for r1 in allApprovalProfiles():
        # Consider only 'larger' profiles for symmetry breaking.
        for r2 in approvalProfiles(lambda r: all(approvalScore(r1,i)==approvalScore(r,i) for i in allVoters()) and r>r1):
            for i in allVoters():
                cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)],[posLiteral(r1,i),negLiteral(r2,i)]])
    return cnf
