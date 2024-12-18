def test_PySAT():
   """
   This is a WebAssembly power Python shell,
   where you can try the examples in the browser:
   1. Type code in the input cell and press
      Shift + Enter to execute;
   2. Or copy paste the code, and click on
      the "Run" button in the toolbar
   3. By the way, TAB-based autocompletion works!
   """

   # the standard way to import PySAT:

   from pysat.formula import CNF
   from pysat.solvers import Solver

   # create a satisfiable CNF formula "(-x1 ∨ x2) ∧ (-x1 ∨ -x2)":
   cnf = CNF(from_clauses=[[-1, 2], [-1, -2]])

   # create a SAT solver for this formula:
   with Solver(bootstrap_with=cnf) as solver:
      # 1.1 call the solver for this formula:
      print('formula is', f'{"s" if solver.solve() else "uns"}atisfiable')

      # 1.2 the formula is satisfiable and so has a model:
      print('and the model is:', solver.get_model())

      # 2.1 apply the MiniSat-like assumption interface:
      print('formula is',
         f'{"s" if solver.solve(assumptions=[1, 2]) else "uns"}atisfiable',
         'assuming x1 and x2')

      # 2.2 the formula is unsatisfiable,
      # i.e. an unsatisfiable core can be extracted:
      print('and the unsatisfiable core is:', solver.get_core())

def test_graph_vis():
   import networkx as nx
   import matplotlib.pyplot as plt

   G = nx.DiGraph()
   G.add_edges_from(
[('A.B-Fcard', 'A.B-Gcard'),
 ('A-Gcard', 'A.B-Fcard'),
 ('A.C-Fcard', 'A.C-Gcard'),
 ('A-Gcard', 'A.C-Fcard'),
 ('A-Fcard', 'A-Gcard'),
 ('D.E-Fcard', 'D.E-Gcard'),
 ('D-Gcard', 'D.E-Fcard'),
 ('D-Fcard', 'D-Gcard'),
 ('D.E-Fcard', '[fcard.D.E == 0]'),
 ('A.C-Fcard', '[fcard.D.E == 1]'),
 ('A.C-Fcard', 'D.E-Fcard'),
 ('A.B-Fcard', '[fcard.D.E == 0]'),
 ('D.E-Fcard', '[fcard.D.E == 1]'),
 ('A.B-Fcard', 'D.E-Fcard')]
   )
   values = [0.75 if (node.startswith('[') and node.endswith(']')) else 0.25 for node in G.nodes()]

   # Specify the edges you want here
   red_edges = [edge for edge in G.edges() if (edge[0].startswith('[') and edge[0].endswith(']')) or (edge[1].startswith('[') and edge[1].endswith(']'))]
   black_edges = [edge for edge in G.edges() if edge not in red_edges]

   # Need to create a layout when doing
   # separate calls to draw nodes and edges
   pos = nx.spring_layout(G)

   import pprint
   import copy
   pprint.pprint(pos)
   pos_lab = copy.deepcopy(pos)
   for v in pos_lab.values():
      v[1] -= 0.05

   nx.draw_networkx_nodes(G, pos, cmap=plt.get_cmap('jet'), 
                        node_color = values, node_size = 500)
   nx.draw_networkx_labels(G, pos_lab)
   nx.draw_networkx_edges(G, pos, edgelist=red_edges, edge_color='r', arrows=True)
   nx.draw_networkx_edges(G, pos, edgelist=black_edges, arrows=True)
   plt.show()

test_graph_vis()