from pylgl import solve
import.csv

cnf = [[1],[-1]]
solver = solve(cnf)
with open ("data.csv", 'w') as file:
    writer = csv.DictWriter(file, fieldnames = ['Satisfiability'])
    if solver == 'UNSAT':
        writer.writerow({'Satisfiability':'UNSAT' })
    else:
        writer.writerow({'Satisfiability':'SAT'})
        
        
