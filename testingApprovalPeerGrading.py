"""File to mess around with approvalPeerGrading.py"""
from approvalPeerGrading import *


def prettyProfile(r):
    """Return a string that shows for which agents each voter voted in profile r."""
    pretty = f"Profile {r}:"
    for i in allVoters():
        pretty += f"\n\tVoter {i}: {list(approvalSet(i,r))}"
    return pretty

# # Check that completeSupport works.
# for r in allApprovalProfiles():
#     comp_support = []
#     pos_support = []
#     print(prettyProfile(r))
#     for i in allVoters():
# #         if positiveSupport(r,i):
# #             pos_support.append(i)
# #             if completeSupport(r,i):
# #                 comp_support.append(i)
#         print(f"\tVoter {i}'s approval score: {approvalScore(r,i)}" )
#     # print(prettyProfile(r) + f"\n\tThe following agents have positive support: {list(pos_support)}.\n\tThe following agents have full support: {list(comp_support)}.")

print(len(cnfCondPosUnanimous()))
print(len(cnfCondNegUnanimous()))
print(len(cnfNewUnanimity()))
print(len(cnfAnonymity()))
print(len(cnfMonotonicity()))
print(len(cnfNonConstant()))

clause_counter = 1
for clause in cnfNonConstant():
    print(f"Clause {clause_counter} has {len(clause)} disjuncts.")
    clause_counter += 1