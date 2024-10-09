from collections import defaultdict

class Graph:
    def __init__(self):
        self.graph = defaultdict(list)
        self.cycle_handling = 'None'  # None/Simple/Complex
        self.cycles = {}
 
    def add_edge(self, edge):
        self.graph[edge[1]]
        if edge[1] not in self.graph[edge[0]]:
            self.graph[edge[0]].append(edge[1])

    # Function to perform DFS traversal
    def DFS(self, node, visited, rec_stack):
        # Mark the current node as visited and add it to the recursion stack
        visited[node] = True
        rec_stack[node] = True
        
        # Recur for all the neighboring vertices
        for neighbor in self.graph[node]:
            # If neighbor is not visited, then recur for it
            if not visited[neighbor]:
                if self.DFS(neighbor, visited, rec_stack):
                    return True
            # If neighbor is already visited and present in recursion stack, then cycle exists
            if rec_stack[neighbor]:
                return True

        # Remove the node from recursion stack
        rec_stack[node] = False
        return False

    # Function to detect cycle in directed graph using DFS
    def detect_cycle_DFS(self):
        # Create a visited set and a recursion stack
        visited = defaultdict(self.visited_def_value)
        rec_stack = defaultdict(self.visited_def_value)
        cycle = []
        # Perform DFS traversal for all nodes to detect cycle
        for node in list(self.graph.keys()):
            if not visited[node]:
                if self.DFS(node, visited, rec_stack):
                    cycle.append({k: v for k, v in rec_stack.items() if v is True})
                    rec_stack = defaultdict(self.visited_def_value)
        return cycle

    def sort_vert(self, n, visited, stack):
        visited[n] = True

        for element in self.graph[n]:
            if visited[element] is False:
                self.sort_vert(element, visited, stack)
        stack.insert(0, n)

    def visited_def_value(self):
        return False

    def topo_sort(self):
        cycle_detection = True
        while cycle_detection is True:
            cycles = self.detect_cycle_DFS()
            cycle_detection = False if self.cycle_handling in ['Simple', 'None'] or cycles == [] else True
            if self.cycle_handling == 'None':
                # TODO proper error handling
                # print('Error, cycles are forbidden according to settings.')
                break
            for index, cycle in enumerate(cycles):
                deps = []
                
                for element in (cycle_elems:=list(cycle.keys())):
                    deps = list(set(deps + self.graph[element]))
                    del self.graph[element]
                cycle_name = f'cycle_{index}'
                cycle_inh = False
                for x in cycle_elems:
                    if x in self.cycles.keys():
                        cycle_name = x
                        cycle_inh = True
                        break
                if cycle_inh is False:
                    self.cycles.update({cycle_name: cycle_elems})
                else:
                    [self.cycles[cycle_name].append(x) for x in cycle_elems if x != cycle_name]
                for elem_from, elem_to in self.graph.items():
                    self.graph[elem_from] = list(map(lambda item: item if item not in cycle_elems else cycle_name, elem_to))
                self.graph[cycle_name]
                for element in deps:
                    if element not in cycle_elems:
                        self.add_edge((cycle_name, element))
        stack = []
        visited = defaultdict(self.visited_def_value)
        for element in list(self.graph.keys()):
            if visited[element] is False:
                self.sort_vert(element, visited, stack)
        
        return stack, cycles