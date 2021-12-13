# Advanced Topics in Computational Social Choice 2021
# Peer Grading
# On the basis of Holzman, Moulin - Impartial Nominations for a Prize

"""File for running sat instances over multiple combinations of parameters in one go."""


from pylgl import solve, itersolve
from math import factorial,comb
from itertools import combinations,permutations,product,chain

def main(n,m,k,ax,axLabels,outSize,outSizeLabels):

    ## BASICS ######################################################

    # Voters and profiles.

    def allVoters():
        return range(n)

    def numPossibleBallots():
        """Returns the number of possible ballots that a voter can submit given the limit of m approvals. 
        Note that a voter may *not* submit an empty ballot.."""
        # Check for each permissible size of subset how many combinations of n-1 voters
        # there are with that size. Sum to find total amount of permissible ballots per voter.
        num_possible_ballots = 0
        for size in range(1, m+1):
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
        # Construct list of all possible ballots (excluding empty ballots).
        possible_ballots = []
        for set_size in range(1, m+1):
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

    ## AXIOMS ####################################################################################

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
        """If some agent with no support is elected, then everyone with at least one vote is elected as well.
        I.e., if any voter with positive support is not elected then every agent with no support is not elected."""
        cnf = []
        for r in allApprovalProfiles():
            for i in voters(lambda v: positiveApproval(r,v)):
                for j in voters(lambda v: not positiveApproval(r,v)):
                    cnf.append([posLiteral(r,i),negLiteral(r,j)])
        return cnf

    def cnfNewUnanimity():
        """The agents with maximal approval scores are elected. There is no one who is elected while there is an agent with a higher approval
        score who is not elected. I.e., for any agent i, and agent j with a lower approval score, 
        if the former is not elected, neither is the latter"""
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
                    # Consider only those j-variants of r1 in which j adds an extra approval of i or approves of i instead of some other agent.
                    for r2 in approvalProfiles(lambda r: iVariants(j,r1,r) and approves(j,i,r) and len(approvalSet(j,r))>=len(approvalSet(j,r1)) and all(elem in approvalSet(j,r1) for elem in approvalSet(j,r) if elem != i)):
                        # If i wins in r1, i should win in r2
                        cnf.append([negLiteral(r1,i),posLiteral(r2,i)])
        return cnf

    # Surjectivity/non-imposition

    def cnfNoExclusion():
        """Every voter gets selected in some profile."""
        cnf = []
        for i in allVoters():
            cnf.append([posLiteral(r,i) for r in allApprovalProfiles()])
        return cnf

    # Non-constantness

    def cnfNonConstant():
        """For any set of k agents, there is a profile in which this set is not elected, i.e., 
        there is a profile in which one of these agents loses.
        Note: saying that each agent should lose in some profile is a stronger requirement, for it is possible that the same 
        agent gets elected in every profile even though not all profiles have an identical outcome. 
        Also: only applicable when outcome is of size exactly k."""
        cnf = []
        for c in list(combinations(allVoters(),k)):
            cnf.append([negLiteral(r,v) for r in allApprovalProfiles() for v in c])
        return cnf

    # Anonymity

    def cnfApprovalScoreAnonymity():
        """If two profiles agree on the approval scores of all agents, then they should yield they same outcome."""
        cnf = []
        for r1 in allApprovalProfiles():
            # Consider only 'larger' profiles for symmetry breaking.
            for r2 in approvalProfiles(lambda r: all(approvalScore(r1,i)==approvalScore(r,i) for i in allVoters()) and r>r1):
                for i in allVoters():
                    cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)],[posLiteral(r1,i),negLiteral(r2,i)]])
        return cnf

    def vPermutation(r1, r2):
        """Return True if r1 and r2 contain exactly the same approval ballots."""
        return sorted([approvalSet(i,r1) for i in allVoters()]) == sorted([approvalSet(j,r2) for j in allVoters()])

    def cnfAnonymity():
        """If the same ballots are submitted in two profiles (but by different voters), then the outcome should be the same."""
        cnf = []
        for r1 in allApprovalProfiles():
            # Consider all the vPermutations of r1 (that are larger than r1 for symmetry breaking).
            for r2 in approvalProfiles(lambda r : vPermutation(r,r1) and r>r1):
                for i in allVoters():
                    cnf.extend([[negLiteral(r1,i),posLiteral(r2,i)],[posLiteral(r1,i),negLiteral(r2,i)]])
        return cnf

    ## SAT-solving #################################################################################
    
    # # SAT-solving for general framework (less efficient for only Holzamn impossibilities)
    # # If outSize isn't specified, then consider 3 options for outcome sizes.
    # if outSize == False:
    #     outSize = [cnfAtLeastOne()+cnfAtMostK(),cnfAtMostK(),cnfAtLeastK()+cnfAtMostK()]
    # else:
    #     sizes = outSize
    #     # create new list in which the functions represented in strings are executed, i.e.,
    #     # create list with CNF corresponding to axioms represented as strings in ouSize
    #     outSize = []
    #     for x in sizes:
    #         outSize.append(eval(x))
    # # If not outSize labels are provided, then provide the 3 options.
    # if outSizeLabels == False:
    #     outSizeLabels = ["0< <=K","<=K","=K"]
    # # Create list with CNFs corresponding to the axioms represented as strings in ax.
    # axioms = ax
    # ax = []
    # for x in axioms:
    #     ax.append(eval(x))
    # # Output results
    # results = []
    # # Consider each combination of axioms and outcome sizes.
    # for i in range(len(axLabels)):
    #     for j in range(len(outSizeLabels)):
    #         # create cnf for particular combination of axioms and outcome size
    #         cnf = ax[i] + outSize[j]
    #         # add to list of results strings specifying the axioms, outsize constraints and 'True' if combination is satisfiable
    #         # and 'False' if it is not 
    #         results.append(str(axLabels[i])+' '+str(outSizeLabels[j])+': '+ str(isinstance(solve(cnf),list)))

    # # SAT-solving specifically for Holzman instances.
    # cnf_exactly_k = cnfAtLeastK()+cnfAtMostK()
    # cnf_impartial = cnfImpartial()
    # cnf_non_constant = cnfNonConstant()
    # results = []
    # # Holzman 1:
    # results.append('I, A, NC: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnfAnonymity()+cnf_non_constant),list)))
    # # Holzman 1, with stronger anonymity.
    # results.append('I, strong-A, NC: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnfApprovalScoreAnonymity()+cnf_non_constant),list)))
    # # Holzman 2:
    # results.append('I, CNU, CPU: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnfCondNegUnanimous()+cnfCondPosUnanimous()),list)))

    # SAT-solving for subsets of axioms for th. 3 with approval score anonymity and th. 4 -- i.e. search for stronger impossibilities.
    # Generate all cnfs.
    cnf_exactly_k = cnfAtLeastK()+cnfAtMostK()
    cnf_impartial = cnfImpartial()
    cnf_strong_anonymous = cnfApprovalScoreAnonymity()
    cnf_non_constant = cnfNonConstant()
    cnf_condnegunanimous = cnfCondNegUnanimous()
    cnf_condposunanimous = cnfCondPosUnanimous()
    # Initialize list of results
    results = []
    # Check that all axioms are satisfiable.
    results.append('INDIVIDUAL AXIOMS\n\tI: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial),list)))
    results.append('\tstrong-A: ' + str(isinstance(solve(cnf_exactly_k+cnf_strong_anonymous),list)))
    results.append('\tNC: ' + str(isinstance(solve(cnf_exactly_k+cnf_non_constant),list)))
    results.append('\tCNU: ' + str(isinstance(solve(cnf_exactly_k+cnf_condnegunanimous),list)))
    results.append('\tCPU: ' + str(isinstance(solve(cnf_exactly_k+cnf_condposunanimous),list)))
    # Check subsets of theorem 3
    results.append('THEOREM 3\n\tI, strong-A: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnf_strong_anonymous),list)))
    results.append('\tI, NC: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnf_non_constant),list)))
    results.append('\tstrong-A, NC: ' + str(isinstance(solve(cnf_exactly_k+cnf_strong_anonymous+cnf_non_constant),list)))
    # Check subsets of theorem 4
    results.append('THEOREM 4\n\tI, CNU: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnf_condnegunanimous),list)))
    results.append('\tI, CPU: ' + str(isinstance(solve(cnf_exactly_k+cnf_impartial+cnf_condposunanimous),list)))
    results.append('\tCNU, CPU: ' + str(isinstance(solve(cnf_exactly_k+cnf_condnegunanimous+cnf_condposunanimous),list)))

    return results

def iterate(nRange,ax,axLabels,mRange=False,kRange=False,outSize=False,outSizeLabels=False,filename="approval_results_no_empty_ballots.txt"):
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
    # default ranges for m and k
    if mRange == False:
        mRange = range(1,max(nRange))
    if kRange == False:
        kRange = range(1,max(nRange))
    
    count = 0
    
    # Consider all combinations of parameters n, k, and m (but consider only values for k and m that are smaller than n)
    for n in nRange:
        for k in (x for x in kRange if x < n):
            for m in (x for x in mRange if x < n):   
                # ensure that we only append results without wiping previous results 
                if count != 0:
                    file = open(filename, 'a')
                # wipe previous results the when you start entirely over
                else: 
                    file = open(filename, 'a')
                # write what parameters are being considered
                file.write(str(n)+','+str(m)+','+str(k)+':\n')   
                print(str(n)+','+str(m)+','+str(k)+': ')                
                # write each result in the list to the specified file
                for r in main(n,m,k,ax,axLabels,outSize,outSizeLabels):
                    file.write(r +'\n') 
                    print(r)    
                file.write('\n')
                print('-------------------------------------')
                file.close()
                
                # register that after this the first iteration has been done so we know not to erase the contents of the file
                # when considering the next set of parameters
                count += 1


# Execution of code
# if __name__ == "__main__" guarantees that we're using the function defined in this file and not from some other imported module
if __name__ == "__main__":
    # Both Holzman-Moulin impossibilities for size =k
    iterate(nRange=range(3,6),ax=[],axLabels=[])
    
    # # single instance
    # axDesc = ["I,A,NC","I,strong-A,NC"]
    # axComb = ["cnfImpartial()+cnfAnonymity()+cnfNonConstant()","cnfImpartial()+cnfApprovalScoreAnonymity()+cnfNonConstant()"]
    # iterate(nRange=range(3,6),ax=axComb,axLabels=axDesc,outSize=["cnfAtLeastK()+cnfAtMostK()"],outSizeLabels=["=K"])