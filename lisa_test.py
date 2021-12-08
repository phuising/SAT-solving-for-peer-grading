from pylgl import solve

cnf = [[1],[-1]]

if solve(cnf) == "UNSAT":
    print("Not satisfiable.")
