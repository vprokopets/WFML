import re
import copy
import time
import itertools

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


def benchmark(time_prev, name):
    timestep = time.perf_counter()
    res = timestep - time_prev
    #print(f'Time for {name}: {(res:=timestep - time_prev)};')
    return timestep, res


# time_start = time.perf_counter()
# deps = [['A','B'], ['B','C'], ['C','A'], ['B','D'], ['D','B'], ['D', 'K'], ['C', 'L'], ['M', 'A']]
# graph = Graph()
# for dep in deps:
#     graph.add_edge(dep)

# graph.topo_sort()


class Test:
    def __init__(self) -> None:
        self.metamodel = {}
        self.inheritance = []
        self.features_to_configure = {}
        self.card_boundaries = {
            '*': [(0, 1e6)],
            '!': [(1, 1e6)],
            '?': [(0, 1)],
            'or': [(1, 1e6)],
            'xor': [(1, 1)]
        }
        self.constraints = []
        self.constraint_pattern = {
            'Assign': {
                'Fcard': [],
                'Gcard': [],
                'Value': []
            },
            'Read': {
                'Fcard': [],
                'Gcard': [],
                'Value': []
            },
            'ParentFeature': '',
            'isValidated': False,
            'Expression': ''
        }

    def initialize_feature(self, name, fcard=1, gcard='all', value=None, abstract=None, inheritance=None, attribute=None):
        mm = self.metamodel
        for level in name.split('.'):
            if level not in mm.keys():
                mm.update({level: {'__self__': {
                        'DeactStandard': False,
                        'ActiveF': True if fcard != 0 else False,
                        'ActiveG': True,
                        'Active': True if fcard != 0 else False,
                        'Fcard': fcard,
                        'Gcard': gcard,
                        'Value': value,
                        'Abstract': abstract,
                        'Inheritance': inheritance,
                        'Attribute': attribute
                        }}})
                self.handle_fcards(name, mm[level], fcard)
            mm = mm[level]

    def get_original(self, feature):
        return re.sub(r'\_\d+', '', feature)
    
    def define_inheritance(self):
        seq, _ = self.topo_sort(self.inheritance, rev=True)
        for feature in seq:
            md = self.read_metadata(feature)
            if (super_feature:=md['__self__']['Inheritance']) is not None:
                md_copy = copy.deepcopy(self.read_metadata(super_feature))
                del md_copy['__self__']
                md.update(md_copy)

    def update_metadata(self, name, field, value):
        md = self.read_metadata(name)
        old_value = md['__self__'][field]
        md['__self__'][field] = value
        print(f'Update metadata: {name} | {field}: {value}')
        if field == 'Inheritance':
            self.inheritance.append((name, value))
        elif field == 'Fcard':
            if self.check_card_value(old_value, value, field) is True:
                self.handle_fcards(name, md, value)
        elif field == 'Gcard':
            if self.check_card_value(old_value, value, field) is True:
                self.handle_gcards(name, md, value)
    
    def is_card_defined(self, value):
        return False if (value in ['*', '!', '?', 'xor', 'or'] or 
            (isinstance(value, str) and (len(value.split(',')) > 1 or len(value.split('..')) > 1))) else True
    
    def check_card_value(self, old_value, value, card_type):
        check_curr = self.is_card_defined(old_value)
        check_new = self.is_card_defined(value)

        if check_curr is False and check_new is True:
            if old_value in self.card_boundaries.keys():
                card_boundaries = self.card_boundaries[old_value]
            else:
                card_boundaries = []
                for card_interval in old_value.split(','):
                    if len(values:=card_interval.split('..')) > 1:
                        card_boundaries.append((int(values[0]), int(values[1])))
                    else:
                        card_boundaries.append((int(card_interval), int(card_interval)))
            if isinstance(value, list) and card_type == 'Gcard':
                value_to_check = len(value)
            elif isinstance(value, str) and card_type == 'Gcard':
                value_to_check = 1
            else:
                value_to_check = int(value)
            if any(value_to_check >= x[0] and value_to_check <= x[1] in x for x in card_boundaries):
                res = True
            else:
                res = False
                # TODO proper error message
                print(f'Wrong cardinality value ({value_to_check}), must be in range {card_boundaries}')
        else:
            res = True
        if res is True:
            self.check_card_in_constraints(value, card_type)
        return res

    def check_card_in_constraints(self, value, card_type):
        pass

    def handle_fcards(self, name, md, repeats):
        name_split = name.rsplit('.', 1)
        pname, fname = name_split[0], name_split[-1]
        tlf = len(name_split) == 1
        par_md = self.metamodel if tlf is True else self.read_metadata(pname)
        repl_md = {}
        if isinstance(repeats, int) and repeats > 0:
            for index in range(repeats):
                new_name = fname if repeats == 1 else f'{fname}_{index}'
                if new_name not in par_md.keys():
                    repl_md.update({new_name: copy.deepcopy(md)})
                    repl_md[new_name]['__self__']['ActiveF'] = True
            par_md.update(repl_md)
            for k, v in par_md.items():
                index = k.rsplit('_', 1)
                if k != '__self__' and index[0] in fname:
                    v['__self__']['ActiveF'] = False if len(index) > 1 and (int(index[1]) >= repeats or repeats == 1) else True
                    self.update_active_state(k if tlf is True else f'{pname}.{k}')
        md['__self__']['ActiveF'] = False if (repeats != 1 and not isinstance(repeats, str)) else True
        md['__self__']['DeactStandard'] = True if (not isinstance(repeats, str) and repeats >= 1) else False
        self.update_active_state(name)

    def get_constraint_mappings(self, constraint):
        constr_ready = True
        all_mappings, all_mappings_fcard, features, fcard_features, res = [], [], [], [], []
        for type in ['Assign', 'Read']:
            for field in ['Gcard', 'Value']:
                features.extend(constraint[type][field])
            fcard_features.extend(constraint[type]['Fcard'])
        for feature in set(features):
            all_mappings.append(self.get_feature_mappings(feature, self.metamodel))

        for feature in all_mappings:
            for mapping in feature:
                full_mappings = []
                for index, _ in enumerate(name_split:=mapping.split('.')):
                    full_mappings.append(self.get_original('.'.join(name_split[:index + 1])))
                for value_type in ['Fcard', 'Gcard']:
                    if any([x in self.features_to_configure[value_type] for x in set(full_mappings + feature)]):
                        constr_ready = False
    
        for feature in set(fcard_features):
            all_mappings_fcard.append(self.get_feature_mappings(feature, self.metamodel, filter=False))
        all_mappings = all_mappings + all_mappings_fcard

        for feature in all_mappings_fcard:
            for mapping in feature:
                full_mappings = []
                for index, _ in enumerate(name_split:=mapping.split('.')):
                    full_mappings.append(self.get_original('.'.join(name_split[:index + 1])))
                if any([x in self.features_to_configure['Fcard'] for x in set(full_mappings + feature)]):
                    constr_ready = False

        if constr_ready is True:
            combinations = itertools.product(*all_mappings)
            filtered_combinations = self.filter_combinations(combinations)

            if filtered_combinations == []:
                constr_ready = False
            for comb in filtered_combinations:
                subres = {}
                for feature in comb:
                    subres.update({self.get_original(feature): feature})
                res.append(subres)
        return res, constr_ready
    
    def filter_combinations(self, combinations):
        res = []
        for comb in combinations:
            valid_elems = {}
            valid_comb = True
            for elem in comb:
                name_split = elem.split('.')
                for index, _ in enumerate(name_split):
                    fname = '.'.join(name_split[:index+1])
                    if (fname_orig:=self.get_original(fname)) not in valid_elems:
                        valid_elems.update({fname_orig: fname})
                    else:
                        if valid_elems[fname_orig] != fname:
                            valid_comb = False
            if valid_comb is True:
                res.append(comb)
        return res
    
    def get_feature_mappings(self, feature, md, filter=True, layer=0, fname=''):
        res = []
        name_split = feature.split('.') if not isinstance(feature, list) else feature
        for k, v in md.items():
            if k != '__self__' and (v['__self__']['Active'] is True or 
                                    (filter is False and v['__self__']['DeactStandard'] is False)) and name_split[layer] in k:
                if layer < len(name_split) - 1:
                    res = res + self.get_feature_mappings(feature, v, filter, layer + 1, f'{fname}.{k}' if layer >= 1 else k)
                else:
                    res.append(f'{fname}.{k}' if layer >= 1 else k)
        return res
    
    def handle_gcards(self, name, md, value):
        if value not in ['xor', 'or']:
            for k, v in md.items():
                if k != '__self__' :
                    v['__self__']['ActiveG'] = True if k.rsplit('.', 1)[-1] == value else False
                    self.update_active_state(f'{name}.{k}')

    def read_metadata(self, name, field=None):
        mm = self.metamodel
        for level in name.split('.'):
            mm = mm[level]
        return mm if field is None else mm['__self__'][field]

    def topo_sort(self, deps, rev=False):
        graph = Graph()
        for dep in deps:
            graph.add_edge(dep)
        
        seq, cycles = graph.topo_sort()
        if rev is True:
            seq.reverse()
        return seq, cycles

    def update_active_state(self, name):
        md = self.read_metadata(name)['__self__']
        md['Active'] = md['ActiveF'] and md['ActiveG']

    def get_product(self, md, res={}):
        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True:
                self_value = {} if v['__self__']['Value'] is None else v['__self__']['Value']
                res.update({k: self_value})
                if len(v.values()) > 1:
                    res.update({k: self.get_product(v, res[k])})
        return res
    
    def get_undefined_features(self, tlf, md, layer=0, pname=''):
        res = {
            'Fcard': [],
            'Gcard': [],
            'Value': []
        }
        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True and(layer > 0 or tlf in k):
                feature_md = v['__self__']
                skip = True
                fname = f'{pname}.{k}' if layer >= 1 else k
                if not self.is_card_defined(feature_md['Fcard']):
                    res['Fcard'].append(fname)
                elif not self.is_card_defined(feature_md['Fcard']):
                    res['Gcard'].append(fname)
                elif feature_md['Attribute'] is not None and feature_md['Value'] is None:
                    res['Value'].append(fname)
                else:
                    skip = False

                if len(v.values()) > 1 and not skip:
                    subres = self.get_undefined_features(feature, v, layer + 1, fname)
                    for md_type in res.keys():
                        res[md_type].extend(subres[md_type])
        if layer == 0:
            self.features_to_configure = copy.deepcopy(res)  
        return res

    def validate_constraints(self):

        tlf_set = set([self.get_original(x) for x in self.metamodel.keys()])
        for tlf in tlf_set:
            for constraint in self.constraints:
                constr_ready = True
                if self.get_original(constraint['ParentFeature'].split('.')[0]) == tlf:
                    constr_deact = self.get_feature_mappings(constraint['ParentFeature'], self.metamodel)
                    print(constr_deact)
                    if constr_deact == []:
                        #TODO proper log message
                        print(f'Constraint {constraint['Expression']} is deactivated (parent feature {constraint["ParentFeature"]} will not be present in the product).')
                    else:
                        mappings, constr_ready = self.get_constraint_mappings(constraint)
                        print('------------------')
                        print(f'Constraint {constraint['Expression']} is {"not ready" if constr_ready is False else "ready"} for validation')
                        print(mappings)
                    



waffle = Test()
print('--------------===========New run===========--------------')
features = ['X', 'X.A', 'X.A.E', 'X.B', 'X.B.C', 'X.B.D']
for feature in features:
    waffle.initialize_feature(feature)
print('asdasds')
waffle.define_inheritance()
waffle.update_metadata('X', 'Fcard', '*')
waffle.update_metadata('X.B', 'Fcard', '?')

# constraint = copy.deepcopy(waffle.constraint_pattern)
# constraint['ParentFeature'] = 'X.A'
# constraint['Read']['Fcard'].append('X.B')
# constraint['Expression'] = 'fcard.parent.B == 1'
# waffle.constraints.append(constraint)

constraint = copy.deepcopy(waffle.constraint_pattern)
constraint['ParentFeature'] = 'X.A'
constraint['Assign']['Value'].append('X.B.C')
constraint['Read']['Value'].append('X.A.E')
constraint['Expression'] = 'X.B.C = X.A.E'
waffle.constraints.append(constraint)

print(waffle.get_undefined_features('X', waffle.metamodel))
waffle.validate_constraints()
waffle.update_metadata('X', 'Fcard', 2)

waffle.update_metadata('X_1.A', 'Fcard', 0)
waffle.update_metadata('X_1.B', 'Fcard', 1)

print(waffle.get_undefined_features('X', waffle.metamodel))
waffle.validate_constraints()
waffle.update_metadata('X_1.B', 'Fcard', '1..3, 5, 7..9')

print(waffle.get_undefined_features('X', waffle.metamodel))
waffle.validate_constraints()



# waffle = Test()

# featuresA = ['A', 'A.A1', 'A.A2']
# featuresB = ['B', 'B.B1']
# featuresC = ['C', 'C.C1']
# featuresD = ['D', 'D.D1']

# parents = [['B', 'A'], ['C', 'A'], ['D', 'B']]

# for features in [featuresA, featuresB, featuresC, featuresD]:
#     for feature in features:
#         waffle.initialize_feature(feature)

# for parent in parents:
#     waffle.update_metadata(parent[0], 'Inheritance', parent[1])

# waffle.define_inheritance()
# waffle.update_metadata('B', 'Fcard', 3)
# waffle.update_metadata('B_1.A1', 'Fcard', 3)
# waffle.update_metadata('B_1.A1', 'Fcard', 2)
# waffle.update_metadata('C', 'Fcard', 3)
# pprint.pprint(waffle.get_product(waffle.metamodel))
# constraint_features = ['B.A1', 'C.C1', 'B.B1']
# waffle.get_constraint_mappings(constraint_features)

# waffle.update_metadata('A', 'Fcard', '1..3, 5, 7..9')
# waffle.update_metadata('A.A1', 'Gcard', 'xor')
# waffle.update_metadata('A.A1', 'Fcard', '?')
# waffle.update_metadata('A.A2', 'Attribute', 'int')
# print(waffle.get_undefined_features('A', waffle.metamodel))

# waffle.update_metadata('A', 'Fcard', 4)