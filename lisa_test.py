from pylgl import solve

cnf = [[1],[-1]]
solver = solve(cnf)
with open ("data.txt", 'w') as file:
    if solver == 'UNSAT':
        file.write('UNSAT')
    else:
        file.write('SAT')
        
        
