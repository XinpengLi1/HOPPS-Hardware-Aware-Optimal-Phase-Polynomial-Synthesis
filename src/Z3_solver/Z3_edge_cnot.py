from z3 import Solver, Bool, Or, And, Sum, Not, Xor, set_param, Implies, AtLeast, AtMost, sat, Optimize, simplify
from functools import reduce
from qiskit import QuantumCircuit
from qiskit.circuit import Parameter
import numpy as np
import time

class z3_edge_cnot:
    def __init__(self, num_qubit, layout=False, terms=[], G=False, I=False, rep = False):
        """
        Initializes the CNOT gate with bit-width for qubits.
        Args:
            num_qubit (int): the number of qubits of QAOA
            F (List): a list of term need to perform
            layout (List): a list of layout edges
            permutation (Boolean): if we need permutation
            G (list): a square matrix to control finial parity matrix
            I (list): a square matrix to control initial parity matrix
        """
        if G==False and  I==False:
            raise("Incomplete, Information, should initial input parity or output parity")
        self.bit_width = num_qubit
        self.finial_matrix = G
        self.initial_matrix = I
        self.terms = terms
        self.mixed_layer_identity = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        self.layout = layout
        self.rep = rep

        # self.mix_layer_matrix = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        
        set_param("parallel.enable", True)
        # set_param("parallel.threads.max", 4)
        self.solver = Solver()

        self.cnot = []
        self.matrix_A = []

        self.F = []

    def initialize_variables(self, K):
        """
        Initialize control qubit(q), target qubit(t), parity matrix(A), and intermediate expressions(h)
        """
        for k in range(K):
            self.cnot.append([Bool(f"cnot_{k}_{i}") for i in range(len(self.layout))])
        for k in range(K+1):
            self.matrix_A.append([[Bool(f'matrix_A_{k+1}_{row_idx}_{col_idx}') for col_idx in range(self.bit_width)]
                for row_idx in range(self.bit_width)])
    
    def constant_initial_clauses(self):
        if self.initial_matrix:
            for i in range(self.bit_width):
                for j in range(self.bit_width):
                    if self.initial_matrix[i][j] == True:  # Constant is True
                        self.solver.add(self.matrix_A[0][i][j])  # Single positive literal
                    elif self.initial_matrix[i][j] == False:  # Constant is False
                        self.solver.add(Not(self.matrix_A[0][i][j]))  # Single negated literal
    
    def constant_finial_clauses(self, K):
        """
        Defines the final state clauses for all result qubits based on the CNOT operation.
        :param k: Number of CNOT gates.
        """
        if self.finial_matrix:
            for i in range(self.bit_width):
                for j in range(self.bit_width):
                    if self.finial_matrix[i][j] ==  True:  # Constant is True
                        self.solver.add(self.matrix_A[K][i][j])  # Single positive literal
                    elif self.finial_matrix[i][j] ==  False:  # Constant is False
                        self.solver.add(Not(self.matrix_A[K][i][j]))  # Single negated literal 
    
    def depend_finial_clauses(self, K, rep):
        """
        Defines the final state clauses for all result qubits based on the CNOT operation.
        :param k: Number of CNOT gates.
        """
        for block in rep:
            rows = block['rows']
            for i in rows:
                subcolumns = block['columns_relate']
                for p , r in zip(block['columns'],  block['relate']):
                    xor_entry = []
                    for j, rr in zip(subcolumns, r):
                        if rr == 1:
                            xor_entry.append(self.matrix_A[K][i][j])
                    if xor_entry:
                        self.solver.add(self.matrix_A[K][i][p] == reduce(Xor,xor_entry))
                
    
    def term_check_clauses(self, K):
        for t in self.terms:
                self.solver.add(Or(
                [ 
                    And([
                        self.matrix_A[k][i][j] == t[j]
                        for j in range(self.bit_width)
                        ])               
                    for k in range(0, K+1) for i in range(self.bit_width)
                ]
                ))

    def validity_clauses(self, K):
        """
        Making sure each cnot is valid
        """
        for i in range(K): 
            self.solver.add(AtMost(*self.cnot[i],1))
            self.solver.add(AtLeast(*self.cnot[i],1))

    def dependency_clauses(self, K):
        """
        Encodes dependencies between the results of consecutive CNOT gates.
        :param k: Number of CNOT gates.
        """
        for k in range(K):
            for e , (i,j) in  enumerate(self.layout):
                for r in range(self.bit_width):
                    self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][j][r] != self.matrix_A[k+1][j][r] ))
                    self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][j][r] == self.matrix_A[k+1][j][r] ))
            for q in range(self.bit_width):
                connected_cnot = []
                for i, (m,n) in enumerate(self.layout):
                    if n == q:
                        connected_cnot.append(self.cnot[k][i])  
                for r in range(self.bit_width):
                    self.solver.add(Implies(Not(Or(connected_cnot)), self.matrix_A[k][q][r] == self.matrix_A[k+1][q][r]))

        # for k in range(K):
        #     for e , (i,j) in  enumerate(self.layout):
        #         for p in range(self.bit_width):
        #             if p == j:
        #                 for r in range(self.bit_width):
        #                     self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][j][r] != self.matrix_A[k+1][j][r] ))
        #                     self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][j][r] == self.matrix_A[k+1][j][r] ))
        #             else:
        #                 for r in range(self.bit_width):
        #                     self.solver.add(Implies(self.cnot[k][e], self.matrix_A[k][p][r] == self.matrix_A[k+1][p][r]))
    
    def qubit_depth_assumption(self, D, K):
        
        assumptions = []
        self.depth_group = []
        for k in range(K):
            self.depth_group.append([Bool(f"depth_group_{k}_{d}") for d in range(D)])

        for k in range(K):
            assumptions.append(AtMost(*self.depth_group[k], 1))
            assumptions.append(AtLeast(*self.depth_group[k], 1))
        
        self.depth_vector = []
        for d in range(D):
            self.depth_vector.append([Bool(f"depth_vector_{d}_{i}") for i, (m,n) in enumerate(self.layout)])
            for i, (m,n) in enumerate(self.layout):
                assumptions.append(AtMost(*[And(self.cnot[k][i], self.depth_group[k][d]) for k in range(K)], 1))
                assumptions.append(self.depth_vector[d][i] == Or([And(self.cnot[k][i], self.depth_group[k][d]) for k in range(K)]))
            for q in range(self.bit_width):
                connected_cnot = []
                for i, (m,n) in enumerate(self.layout):
                    if m == q or n == q:
                        connected_cnot.append(self.depth_vector[d][i])
                assumptions.append(AtMost(*connected_cnot,1))
            
            for k in range(K-1):
                assumptions.append(Implies(
                    self.depth_group[k][d], Or(self.depth_group[k+1][d], And([Not(self.depth_group[kk][d]) for kk in range(k+1, K)]))
                    ))
                
                assumptions.append(Implies(
                    self.depth_group[k][d], And([Not(self.depth_group[kk][dd]) for dd in range(d-1) for kk in range(k+1, K)])
                    ))           
                
        return assumptions

    def solve(self, k, display=True):
        self.initialize_variables(k)
        self.constant_finial_clauses(k)
        self.constant_initial_clauses()
        if self.terms:
            self.term_check_clauses(k)
        self.validity_clauses(k)
        self.dependency_clauses(k)
        if self.rep is not False:
            self.depend_finial_clauses(k, self.rep)
        
        start_time = time.time()
        sat_or = str(self.solver.check()) 
        end_time = time.time() 
        
        elapsed_time = end_time - start_time

        if display:
            print(f"Elapsed time: {elapsed_time:.6f} seconds")

        if sat_or == "sat":
            if display:
                print("solution found for " + str(k)+ "current depth: "+str(k))
            self.model = self.solver.model()
            count_depth = k
            if count_depth<=1:
                self.model = self.solver.model()
                return True, k, elapsed_time, self.model
            for i in range(count_depth, 0, -1):
                sat_or_cnot = str(self.solver.check(self.qubit_depth_assumption(i,k))) 
                if sat_or_cnot != "sat":
                    if display:
                        print("Try " +str(i)+ " depth, fail")
                    self.solver.check(self.qubit_depth_assumption(i+1, k))
                    self.model = self.solver.model()
                    return True, k, elapsed_time, self.model
                else:
                    self.model = self.solver.model()
                    if display:
                       print("Try " +str(i)+ " depth, success")
            print('input circuit is idenity unitary')
            # self.solver.check(self.qubit_depth_assumption(4, k))
            # self.model = self.solver.model()
            return False, k, elapsed_time, None
        else:
            if display:
                print("No solution found for " + str(k))
            return False, k, elapsed_time, None
        
    def perfer_k_cnot_clauses(self, k, qubits):
        for i, (n,m) in enumerate(self.layout):
            if (n not in qubits) or (m not in qubits):
                self.solver.add(Not(self.cnot[k][i]))
        
    def output_perfer_solving(self, K, qubits):
        for k in range(K-1, 0, -1):
            self.solver.push()
            self.perfer_k_cnot_clauses(k, qubits)
            sat_or = str(self.solver.check()) 
            if sat_or == "sat":
                print( str(k) + "th cnot perferred")
            else:
                self.solver.pop()
                self.solver.check()
                return k+1

    def input_perfer_solving(self, K, qubits):
        for k in range(K):
            self.solver.push()
            self.perfer_k_cnot_clauses(k, qubits)
            sat_or = str(self.solver.check()) 
            if sat_or == "sat":
                print( str(k) + "th cnot perferred")
            else:
                self.solver.pop()
                self.solver.check()
                return k
    
    def extract_parity_matrix_at_time(self, m):
        A0 = np.zeros([self.bit_width,self.bit_width])
        for i in range(self.bit_width):
            for j in range(self.bit_width):
                if str(self.solver.model()[self.matrix_A[m][i][j]]) == 'True':
                    A0[i][j] = 1
        return [list(map(bool, a)) for a in A0]
    
    def extract_boolean_term(self, m):
        A0 = np.zeros(self.bit_width)
        for i in range(self.bit_width):
            if str(self.solver.model()[self.boolean_terms[m][i]]) == 'True':
                A0[i] = 1
        return [bool(a) for a in A0]
    
    def extract_quantum_circuit_from_model(self, K, theta):
        qc = QuantumCircuit(self.bit_width)

        term_check = [False  for _ in range(len(self.terms))]

        for k in range(K+1):
            # Add Cnot gate
            if k>0:
                for n, (i,j) in enumerate(self.layout):
                    if self.solver.model()[self.cnot[k-1][n]] == True:
                        qc.cx(i,j)

            # Add parameters
            for i in range(self.bit_width):
                matrix_A_k_row = []
                for j in range(self.bit_width):
                    matrix_A_k_row.append(self.solver.model()[self.matrix_A[k][i][j]])
                for n in range(len(self.terms)):
                    if term_check[n]==False and self.terms[n] == matrix_A_k_row:
                        qc.rz(theta[n],i)
                        term_check[n]=True
                        break
                                       
        return qc

# from z3 import Solver, Bool, Or, And, Sum, Not, Xor, set_param, Implies, AtLeast, AtMost, sat, Optimize, simplify
# from functools import reduce
# from qiskit import QuantumCircuit
# from qiskit.circuit import Parameter
# import numpy as np
# import time

# class z3_edge_cnot:
#     def __init__(self, num_qubit, layout=False, terms=[], G=False, I=False):
#         """
#         Initializes the CNOT gate with bit-width for qubits.
#         Args:
#             num_qubit (int): the number of qubits of QAOA
#             F (List): a list of term need to perform
#             layout (List): a list of layout edges
#             permutation (Boolean): if we need permutation
#             G (list): a square matrix to control finial parity matrix
#             I (list): a square matrix to control initial parity matrix
#         """
#         if G==False and  I==False:
#             raise("Incomplete, Information, should initial input parity or output parity")
#         self.bit_width = num_qubit
#         self.finial_matrix = G
#         self.initial_matrix = I
#         self.terms = terms
#         self.mixed_layer_identity = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
#         self.layout = layout

#         # self.mix_layer_matrix = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        
#         set_param("parallel.enable", True)
#         # set_param("parallel.threads.max", 4)
#         self.solver = Solver()

#         self.cnot = []
#         self.matrix_A = []

#         self.F = []

#     def initialize_variables(self, K):
#         """
#         Initialize control qubit(q), target qubit(t), parity matrix(A), and intermediate expressions(h)
#         """
#         for k in range(K):
#             self.cnot.append([Bool(f"cnot_{k}_{i}") for i in range(len(self.layout))])
#         for k in range(K+1):
#             self.matrix_A.append([[Bool(f'matrix_A_{k+1}_{row_idx}_{col_idx}') for col_idx in range(self.bit_width)]
#                 for row_idx in range(self.bit_width)])
    
#     def constant_initial_clauses(self):
#         if self.initial_matrix:
#             for i in range(self.bit_width):
#                 for j in range(self.bit_width):
#                     if self.initial_matrix[i][j] == True:  # Constant is True
#                         self.solver.add(self.matrix_A[0][i][j])  # Single positive literal
#                     elif self.initial_matrix[i][j] == False:  # Constant is False
#                         self.solver.add(Not(self.matrix_A[0][i][j]))  # Single negated literal
    
#     def constant_finial_clauses(self, K):
#         """
#         Defines the final state clauses for all result qubits based on the CNOT operation.
#         :param k: Number of CNOT gates.
#         """
#         if self.finial_matrix:
#             for i in range(self.bit_width):
#                 for j in range(self.bit_width):
#                     if self.finial_matrix[i][j] ==  True:  # Constant is True
#                         self.solver.add(self.matrix_A[K][i][j])  # Single positive literal
#                     elif self.finial_matrix[i][j] ==  False:  # Constant is False
#                         self.solver.add(Not(self.matrix_A[K][i][j]))  # Single negated literal 
    
#     def depend_finial_clauses(self, K, rep):
#         """
#         Defines the final state clauses for all result qubits based on the CNOT operation.
#         :param k: Number of CNOT gates.
#         """
#         for block in rep:
#             rows = block['rows']
#             for i in rows:
#                 for p , subcolumns in zip(block['columns'], block['relate']):
#                     xor_entry = []
#                     for j in subcolumns:
#                         xor_entry.append(self.matrix_A[K][i][j])
#                     self.solver.add(self.matrix_A[K][i][p] == reduce(Xor,xor_entry))
                
    
#     def term_check_clauses(self, K):
#         for t in self.terms:
#                 self.solver.add(Or(
#                 [ 
#                     And([
#                         self.matrix_A[k][i][j] == t[j]
#                         for j in range(self.bit_width)
#                         ])               
#                     for k in range(1, K+1) for i in range(self.bit_width)
#                 ]
#                 ))

#     def validity_clauses(self, K):
#         """
#         Making sure each cnot is valid
#         """
#         for i in range(K): 
#             self.solver.add(AtMost(*self.cnot[i],1))
#             self.solver.add(AtLeast(*self.cnot[i],1))

#     def dependency_clauses(self, K):
#         """
#         Encodes dependencies between the results of consecutive CNOT gates.
#         :param k: Number of CNOT gates.
#         """
#         for k in range(K):
#             for e , (i,j) in  enumerate(self.layout):
#                 for p in range(self.bit_width):
#                     if p == j:
#                         for r in range(self.bit_width):
#                             self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][j][r] != self.matrix_A[k+1][j][r] ))
#                             self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][j][r] == self.matrix_A[k+1][j][r] ))
#                     else:
#                         for r in range(self.bit_width):
#                             self.solver.add(Implies(self.cnot[k][e], self.matrix_A[k][p][r] == self.matrix_A[k+1][p][r]))
    
#     def solve(self, k, display=True):
#         self.initialize_variables(k)
#         self.constant_finial_clauses(k)
#         self.constant_initial_clauses()
#         if self.terms:
#             self.term_check_clauses(k)
#         self.validity_clauses(k)
#         self.dependency_clauses(k)
        
#         start_time = time.time()
#         sat_or = str(self.solver.check()) 
#         end_time = time.time() 
        
#         elapsed_time = end_time - start_time

#         if display:
#                 print(f"Elapsed time: {elapsed_time:.6f} seconds")

#         if sat_or == "sat":
#             print("solution found for " + str(k))
#             model = self.solver.model()
#             return True, k, elapsed_time, model
#         else:
#             if display:
#                 print("No solution found for " + str(k))
#             return False, k, elapsed_time, None
        
#     def perfer_k_cnot_clauses(self, k, qubits):
#         for i, (n,m) in enumerate(self.layout):
#             if (n not in qubits) or (m not in qubits):
#                 self.solver.add(Not(self.cnot[k][i]))
        
#     def output_perfer_solving(self, K, qubits):
#         for k in range(K-1, 0, -1):
#             self.solver.push()
#             self.perfer_k_cnot_clauses(k, qubits)
#             sat_or = str(self.solver.check()) 
#             if sat_or == "sat":
#                 print( str(k) + "th cnot perferred")
#             else:
#                 self.solver.pop()
#                 self.solver.check()
#                 return k+1

#     def input_perfer_solving(self, K, qubits):
#         for k in range(K):
#             self.solver.push()
#             self.perfer_k_cnot_clauses(k, qubits)
#             sat_or = str(self.solver.check()) 
#             if sat_or == "sat":
#                 print( str(k) + "th cnot perferred")
#             else:
#                 self.solver.pop()
#                 self.solver.check()
#                 return k
    
#     def extract_parity_matrix_at_time(self, m):
#         A0 = np.zeros([self.bit_width,self.bit_width])
#         for i in range(self.bit_width):
#             for j in range(self.bit_width):
#                 if str(self.solver.model()[self.matrix_A[m][i][j]]) == 'True':
#                     A0[i][j] = 1
#         return [list(map(bool, a)) for a in A0]
    
#     def extract_boolean_term(self, m):
#         A0 = np.zeros(self.bit_width)
#         for i in range(self.bit_width):
#             if str(self.solver.model()[self.boolean_terms[m][i]]) == 'True':
#                 A0[i] = 1
#         return [bool(a) for a in A0]
    
#     def extract_quantum_circuit_from_model(self, K, theta):
#         qc = QuantumCircuit(self.bit_width)

#         term_check = [False  for _ in range(len(self.terms))]

#         for k in range(K+1):
#             # Add Cnot gate
#             if k>0:
#                 for n, (i,j) in enumerate(self.layout):
#                     if self.solver.model()[self.cnot[k-1][n]] == True:
#                         qc.cx(i,j)

#             # Add parameters
#             for i in range(self.bit_width):
#                 matrix_A_k_row = []
#                 for j in range(self.bit_width):
#                     matrix_A_k_row.append(self.solver.model()[self.matrix_A[k][i][j]])
#                 for n in range(len(self.terms)):
#                     if term_check[n]==False and self.terms[n] == matrix_A_k_row:
#                         qc.rz(theta[n],i)
#                         term_check[n]=True
#                         break
                                       
#         return qc

####################### Old version #######################

# from z3 import Solver, Bool, Or, And, Sum, Not, Xor, set_param, Implies, AtLeast, AtMost, sat, Optimize, simplify
# from functools import reduce
# from qiskit import QuantumCircuit
# from qiskit.circuit import Parameter
# import numpy as np
# import time

# from z3 import Solver, Bool, Or, And, Sum, Not, Xor, set_param, Implies, AtLeast, AtMost, sat, Optimize, simplify
# from functools import reduce
# from qiskit import QuantumCircuit
# from qiskit.circuit import Parameter
# import numpy as np
# import time

# class z3_edge_cnot:
#     def __init__(self, num_qubit, layout=False, terms=False, G=False, I=False):
#         """
#         Initializes the CNOT gate with bit-width for qubits.
#         Args:
#             num_qubit (int): the number of qubits of QAOA
#             F (List): a list of term need to perform
#             layout (List): a list of layout edges
#             permutation (Boolean): if we need permutation
#             G (list): a square matrix to control finial parity matrix
#             I (list): a square matrix to control initial parity matrix
#         """
#         if G==False and  I==False:
#             raise("Incomplete, Information, should initial input parity or output parity")
#         self.bit_width = num_qubit
#         self.finial_matrix = G
#         self.initial_matrix = I
#         self.terms = terms
#         self.mixed_layer_identity = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
#         self.layout = layout

#         # self.mix_layer_matrix = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        
#         set_param("parallel.enable", True)
#         # set_param("parallel.threads.max", 4)
#         self.solver = Solver()

#         self.cnot = []
#         self.matrix_A = []

#         self.F = []

#     def initialize_variables(self, K):
#         """
#         Initialize control qubit(q), target qubit(t), parity matrix(A), and intermediate expressions(h)
#         """
#         for k in range(K):
#             self.cnot.append([Bool(f"cnot_{k}_{i}") for i in range(len(self.layout))])
#         for k in range(K+1):
#             self.matrix_A.append([[Bool(f'matrix_A_{k+1}_{row_idx}_{col_idx}') for col_idx in range(self.bit_width)]
#                 for row_idx in range(self.bit_width)])
    
#     def constant_initial_clauses(self):
#         if self.initial_matrix:
#             for i in range(self.bit_width):
#                 for j in range(self.bit_width):
#                     if self.initial_matrix[i][j]:  # Constant is True
#                         self.solver.add(self.matrix_A[0][i][j])  # Single positive literal
#                     else:  # Constant is False
#                         self.solver.add(Not(self.matrix_A[0][i][j]))  # Single negated literal
    
#     def constant_finial_clauses(self, K):
#         """
#         Defines the final state clauses for all result qubits based on the CNOT operation.
#         :param k: Number of CNOT gates.
#         """
#         if self.finial_matrix:
#             for i in range(self.bit_width):
#                 for j in range(self.bit_width):
#                     if self.finial_matrix[i][j]:  # Constant is True
#                         self.solver.add(self.matrix_A[K][i][j])  # Single positive literal
#                     else:  # Constant is False
#                         self.solver.add(Not(self.matrix_A[K][i][j]))  # Single negated literal 
    
#     def term_check_clauses(self, K):
#         for t in self.terms:
#                 self.solver.add(Or(
#                 [ 
#                     And([
#                         self.matrix_A[k][i][j] == t[j]
#                         for j in range(self.bit_width)
#                         ])               
#                     for k in range(1, K+1) for i in range(self.bit_width)
#                 ]
#                 ))

#     def validity_clauses(self, K):
#         """
#         Making sure each cnot is valid
#         """
#         for i in range(K): 
#             self.solver.add(AtMost(*self.cnot[i],1))
#             self.solver.add(AtLeast(*self.cnot[i],1))

#     def dependency_clauses(self, K):
#         """
#         Encodes dependencies between the results of consecutive CNOT gates.
#         :param k: Number of CNOT gates.
#         """
#         for k in range(K):
#             for e , (i,j) in  enumerate(self.layout):
#                 for p in range(self.bit_width):
#                     if p == j:
#                         for r in range(self.bit_width):
#                             self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][j][r] != self.matrix_A[k+1][j][r] ))
#                             self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][j][r] == self.matrix_A[k+1][j][r] ))
#                     else:
#                         for r in range(self.bit_width):
#                             self.solver.add(Implies(self.cnot[k][e], self.matrix_A[k][p][r] == self.matrix_A[k+1][p][r]))
    
#     def solve(self, k, display=True):
#         self.initialize_variables(k)
#         self.constant_finial_clauses(k)
#         self.constant_initial_clauses()
#         if self.terms:
#             self.term_check_clauses(k)
#         self.validity_clauses(k)
#         self.dependency_clauses(k)
        
#         start_time = time.time()
#         sat_or = str(self.solver.check()) 
#         end_time = time.time() 
        
#         elapsed_time = end_time - start_time

#         if display:
#                 print(f"Elapsed time: {elapsed_time:.6f} seconds")

#         if sat_or == "sat":
#             print("solution found for " + str(k))
#             model = self.solver.model()
#             return True, k, elapsed_time, model
#         else:
#             print("No solution found for " + str(k))
#             return False, k, elapsed_time, None
    
#     def extract_parity_matrix_at_time(self, m):
#         A0 = np.zeros([self.bit_width,self.bit_width])
#         for i in range(self.bit_width):
#             for j in range(self.bit_width):
#                 if str(self.solver.model()[self.matrix_A[m][i][j]]) == 'True':
#                     A0[i][j] = 1
#         return [list(map(bool, a)) for a in A0]
    
#     def extract_boolean_term(self, m):
#         A0 = np.zeros(self.bit_width)
#         for i in range(self.bit_width):
#             if str(self.solver.model()[self.boolean_terms[m][i]]) == 'True':
#                 A0[i] = 1
#         return [bool(a) for a in A0]
    
#     def extract_quantum_circuit_from_model(self, K, theta):
#         qc = QuantumCircuit(self.bit_width)

#         term_check = [False  for _ in range(len(self.terms))]

#         for k in range(K+1):
#             # Add Cnot gate
#             if k>0:
#                 for n, (i,j) in enumerate(self.layout):
#                     if self.solver.model()[self.cnot[k-1][n]] == True:
#                         qc.cx(i,j)

#             # Add parameters
#             for i in range(self.bit_width):
#                 matrix_A_k_row = []
#                 for j in range(self.bit_width):
#                     matrix_A_k_row.append(self.solver.model()[self.matrix_A[k][i][j]])
#                 for n in range(len(self.terms)):
#                     if term_check[n]==False and self.terms[n] == matrix_A_k_row:
#                         qc.rz(theta,i)
#                         term_check[n]=True
#                         break
                                       
#         return qc

####################### Old version #######################

# class z3_edge_cnot:
#     def __init__(self, num_qubit, layout=False, terms=False, G=False, I=False):
#         """
#         Initializes the CNOT gate with bit-width for qubits.
#         Args:
#             num_qubit (int): the number of qubits of QAOA
#             F (List): a list of term need to perform
#             layout (List): a list of layout edges
#             permutation (Boolean): if we need permutation
#             G (list): a square matrix to control finial parity matrix
#             I (list): a square matrix to control initial parity matrix
#         """
#         if G==False and  I==False:
#             raise("Incomplete, Information, should initial input parity or output parity")
#         self.bit_width = num_qubit
#         self.finial_matrix = G
#         self.initial_matrix = I
#         self.terms = terms
#         self.mixed_layer_identity = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
#         self.layout = layout

#         # self.mix_layer_matrix = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        
#         set_param("parallel.enable", True)
#         # set_param("parallel.threads.max", 4)
#         self.solver = Solver()

#         self.cnot = []
#         self.matrix_A = []
#         self.boolean_terms = []

#         self.F = []

#     def initialize_variables(self, K):
#         """
#         Initialize control qubit(q), target qubit(t), parity matrix(A), and intermediate expressions(h)
#         """
#         for k in range(K):
#             self.cnot.append([Bool(f"cnot_{k}_{i}") for i in range(len(self.layout))])
#             self.boolean_terms.append([Bool(f"bool_term_{k}_{i}") for i in range(self.bit_width)])
#         for k in range(K+1):
#             self.matrix_A.append([[Bool(f'matrix_A_{k+1}_{row_idx}_{col_idx}') for col_idx in range(self.bit_width)]
#                 for row_idx in range(self.bit_width)])
    
#     def constant_initial_clauses(self):
#         if self.initial_matrix:
#             for i in range(self.bit_width):
#                 for j in range(self.bit_width):
#                     if self.initial_matrix[i][j]:  # Constant is True
#                         self.solver.add(self.matrix_A[0][i][j])  # Single positive literal
#                     else:  # Constant is False
#                         self.solver.add(Not(self.matrix_A[0][i][j]))  # Single negated literal
    
#     def constant_finial_clauses(self, K):
#         """
#         Defines the final state clauses for all result qubits based on the CNOT operation.
#         :param k: Number of CNOT gates.
#         """
#         if self.finial_matrix:
#             for i in range(self.bit_width):
#                 for j in range(self.bit_width):
#                     if self.finial_matrix[i][j]:  # Constant is True
#                         self.solver.add(self.matrix_A[K][i][j])  # Single positive literal
#                     else:  # Constant is False
#                         self.solver.add(Not(self.matrix_A[K][i][j]))  # Single negated literal 

#     def boolean_terms_build_clauses(self, end_K):    
#         for k in range(end_K):
#             for n, (_, j) in enumerate(self.layout):
#                 for i in range(self.bit_width):
#                     self.solver.add(Implies(self.cnot[k][n], self.boolean_terms[k][i] == self.matrix_A[k+1][j][i] ))

#     def boolean_function_check_clauses(self, end_K):  
#         for term in self.terms:
#             self.solver.add(simplify(Or(
#                 [ And([self.boolean_terms[k][col] == term[col] for col in range(self.bit_width)]) for k in range(end_K)]
#                 )))
#             if term not in self.F:
#                 self.F.append(term)

#     def validity_clauses(self, K):
#         """
#         Making sure each cnot is valid
#         """
#         for i in range(K): 
#             self.solver.add(AtMost(*self.cnot[i],1))
#             self.solver.add(AtLeast(*self.cnot[i],1))

#     def dependency_clauses(self, K):
#         """
#         Encodes dependencies between the results of consecutive CNOT gates.
#         :param k: Number of CNOT gates.
#         """
#         for k in range(K):
#             for e , (i,j) in  enumerate(self.layout):
#                 for p in range(self.bit_width):
#                     if p == j:
#                         for r in range(self.bit_width):
#                             self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][j][r] != self.matrix_A[k+1][j][r] ))
#                             self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][j][r] == self.matrix_A[k+1][j][r] ))
#                     else:
#                         for r in range(self.bit_width):
#                             self.solver.add(Implies(self.cnot[k][e], self.matrix_A[k][p][r] == self.matrix_A[k+1][p][r]))
    
#     def solve(self, k, display=True):
#         self.initialize_variables(k)
#         self.constant_finial_clauses(k)
#         self.constant_initial_clauses()
#         if self.terms:
#             self.boolean_terms_build_clauses(k)
#             self.boolean_function_check_clauses(k)
#         self.validity_clauses(k)
#         self.dependency_clauses(k)
        
#         start_time = time.time()
#         sat_or = str(self.solver.check()) 
#         end_time = time.time() 
        
#         elapsed_time = end_time - start_time

#         if display:
#                 print(f"Elapsed time: {elapsed_time:.6f} seconds")

#         if sat_or == "sat":
#             print("solution found for " + str(k))
#             model = self.solver.model()
#             return True, k, elapsed_time, model
#         else:
#             print("No solution found for " + str(k))
#             return False, k, elapsed_time, None
    
#     def extract_parity_matrix_at_time(self, m):
#         A0 = np.zeros([self.bit_width,self.bit_width])
#         for i in range(self.bit_width):
#             for j in range(self.bit_width):
#                 if str(self.solver.model()[self.matrix_A[m][i][j]]) == 'True':
#                     A0[i][j] = 1
#         return [list(map(bool, a)) for a in A0]
    
#     def extract_boolean_term(self, m):
#         A0 = np.zeros(self.bit_width)
#         for i in range(self.bit_width):
#             if str(self.solver.model()[self.boolean_terms[m][i]]) == 'True':
#                 A0[i] = 1
#         return [bool(a) for a in A0]
    
#     def extract_quantum_circuit_from_model(self, K, theta):
#         qc = QuantumCircuit(self.bit_width)

#         term_check = [False  for _ in range(len(self.F))]

#         for k in range(K+1):
#             # Add Cnot gate
#             if k>0:
#                 for n, (i,j) in enumerate(self.layout):
#                     if self.solver.model()[self.cnot[k-1][n]] == True:
#                         qc.cx(i,j)

#             # Add parameters
#             for i in range(self.bit_width):
#                 matrix_A_k_row = []
#                 for j in range(self.bit_width):
#                     matrix_A_k_row.append(self.solver.model()[self.matrix_A[k][i][j]])
#                 for n in range(len(self.F)):
#                     if term_check[n]==False and self.F[n] == matrix_A_k_row:
#                         qc.rz(theta[0],i)
#                         term_check[n]=True
#                         break
                                       
#         return qc