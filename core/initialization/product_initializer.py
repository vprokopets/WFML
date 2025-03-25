import copy
import logging
import pprint

from collections import defaultdict

from core.auxiliary import cname, topo_sort
from core.initialization.feature_initializer import FeatureInitializer


class ProductInitializer:
    def __init__(self, workspace, storage):
        self.workspace = workspace
        self.storage = storage
        self.feature_initializer = FeatureInitializer(workspace)
        self.dependencies = []
        self.constraint_groups_representation = {}

    def build_metagraph(self):
        # tree dependencies analysis (parent-child relations + fcard-gcard/value relations)
        for tlf, md in self.workspace.features.items():
            if md['__self__']['Abstract'] is None:
                self._tree_dependencies_analysis(tlf)

        # cross-tree dependencies analysis (from constraints)
        cross_tree_dependencies, parent_dependencies, independent_features = self._cross_tree_dependencies_analysis()
        self.dependencies.extend(cross_tree_dependencies)

        # define restrictions, e.g., feature A.B must be configured after feature A but before constraint A.B > 2
        sequence_restrictions = self._sequence_restriction_analysis(parent_dependencies)
        # group constraints and features that are connected with cross-tree dependencies
        # to resolve them during single wizard step
        self.constraint_groups = self._group_constraint_dependencies(sequence_restrictions)

        # for example of constraint [A.B > 2] with parent feature A
        # (A -> A.B), (A.B.value -> constraint) ==>> (A -> Waffle_Constraint_Group_1)
        # dependencies_to_remove are required to adjust configuration sequence for constraints
        dependencies_to_remove = self._replace_dependencies_that_are_in_group()
        self._define_configuration_sequence(independent_features, dependencies_to_remove)

        self.storage.register_initialization_data(
            self.dependencies,
            self.configuration_sequence,
            self.sequence_filtered,
            self.constraint_groups,
            self.constraint_groups_representation
        )

    def define_inheritance(self, parsing_objects):
        seq, _ = topo_sort(self.workspace.inheritance, rev=True)
        for feature in seq:
            md = self.workspace.read_metadata(feature)
            if (super_feature := md['__self__']['Inheritance']) is not None:
                md_copy = copy.deepcopy(self.workspace.read_metadata(super_feature))
                if parsing_objects == 'Feature':
                    del md_copy['__self__']
                    md.update(md_copy)
                if parsing_objects == 'Constraint':
                    self._recursive_inheritance(md_copy, feature, md)

    def group_constraints(self):
        for group_name in self.constraint_groups.keys():
            self.constraint_groups_representation.update({group_name: []})
            # representation for logging, e.g., A.B - [C > 2]
            for index in range(self.storage.configuration_sequence.index(group_name) + 1, len(self.storage.configuration_sequence)):
                if ((elem := self.storage.configuration_sequence[index]).startswith('Constraint_')):
                    for constraint in self.workspace.constraints.values():
                        if constraint['ID'] == elem:
                            self.constraint_groups_representation[group_name].append(
                                (f'{constraint['Metadata']['ParentFeature']} - ',
                                 f'{constraint['Metadata']['Expression']}')
                            )
                else:
                    break
        self.workspace.register_constraint_groups(self.constraint_groups_representation)

    def initialize_product(self, model):
        # To separate concerns of checking features and constraints.
        # Since constraints need to collect information of adhered features, we firstly need to initialize whole feature workspace
        # ('Feature' loop) and only then assign constraints ('Constraint' loop)
        for parsing_objects in ['Feature', 'Constraint']:
            for element in model.elements:
                # Skip parsing of global constraints
                # TODO add parsing of global constraints
                if cname(element) == 'Feature':
                    self.feature_initializer.parse_feature(element, parsing_objects=parsing_objects)
            self.define_inheritance(parsing_objects)

    def _cross_tree_dependencies_analysis(self):
        dependencies = []
        parent_dependencies = []
        independent_constraints = []

        for constraint in self.workspace.constraints.values():
            parent_feature = constraint['Metadata']['ParentFeature']
            # constraint dependencies are not checked for abstract features
            if self.workspace.features[parent_feature.split('.')[0]]['__self__']['Abstract'] is None:
                # TODO check the constraints that should be involved under this flag
                independent_constraint_flag = True
                for metadata in constraint['Metadata']['Precedence'].values():
                    for position, expression in metadata.items():
                        # append affected feature to appropriate list (assign/read)
                        if isinstance(expression, dict) and not (position == 2 and metadata['Class'] == 'prec50'):
                            assign_type = 'Assign' if ((position == 0 and metadata['Class'] == 'prec10')
                                                       or (position == 1 and metadata['Class'] == 'prec11' and expression == 'excludes')) else 'Read'
                            for feature_name, feature_type in expression.items():
                                if feature_type == 'Fname':
                                    feature_type = 'Fcard'
                                if feature_type == 'Childs':
                                    feature_type = 'Fcard'
                                    childs = self.workspace.get_feature_childrens(feature_name, filter_active=False)
                                    for child in childs:
                                        if child not in constraint['Metadata'][assign_type][feature_type]:
                                            constraint['Metadata'][assign_type][feature_type].append(child)
                                else:
                                    if feature_name not in constraint['Metadata'][assign_type][feature_type]:
                                        constraint['Metadata'][assign_type][feature_type].append(feature_name)
                                if assign_type == 'Assign':
                                    if feature_type == 'Fcard':
                                        constraint['Metadata']['Read']['Gcard'].append(feature_name.rsplit('.', 1)[0])
                                    else:
                                        constraint['Metadata']['Read']['Fcard'].append(feature_name)
                        # special handling for filter x where y operation
                        # this constraint should be executed after affected in 'y' children features are configured
                        # not after feature 'x' is configured
                        elif position == 1 and metadata['Class'] == 'prec24':
                            pass
                        elif position == 2 and metadata['Class'] == 'prec24':
                            self._filter_x_where_y_handling(constraint, expression, parent_feature, metadata, assign_type)
                        # handling for unique x in y operation, adding all features affected in x
                        elif position == 1 and metadata['Class'] == 'prec50':
                            self._unique_x_in_y_handling(constraint, metadata)

                # TODO check when independent constraints appear
                for k, v in constraint['Metadata']['Assign'].items():
                    for feature in v:
                        dependencies.append((f'{constraint['ID']}', f'{feature}-{k}'))
                        independent_constraint_flag = False
                for k, v in constraint['Metadata']['Read'].items():
                    dependencies.extend([(f'{x}-{k}', f'{constraint['ID']}') for x in v])
                    dependencies.extend([(f'{constraint['Metadata']['ParentFeature']}-Fcard', f'{x}-{k}') for x in v])
                parent_dependencies.append((f'{constraint['Metadata']['ParentFeature']}-Fcard', f'{constraint['ID']}'))
                dependencies.append((f'{constraint['Metadata']['ParentFeature']}-Fcard', f'{constraint['ID']}'))
                if independent_constraint_flag is True:
                    independent_constraints.append(constraint['ID'])

        # to remove duplicates
        filtered_dependencies = list(set(dependencies))
        return filtered_dependencies, parent_dependencies, independent_constraints

    def _tree_dependencies_analysis(self, feature, parent=None):
        md = self.workspace.read_metadata(feature)
        self.dependencies.append((f'{feature}-Fcard', f'{feature}-{'Gcard' if md['__self__']['Attribute'] is None else 'Value'}'))
        if parent is not None:
            md_par = self.workspace.read_metadata(parent)
            self.dependencies.append((f'{parent}-{'Gcard' if md_par['__self__']['Attribute'] is None else 'Value'}',
                                      f'{feature}-Fcard'))
        for key in md.keys():
            if key != '__self__':
                self._tree_dependencies_analysis(f'{feature}.{key}', feature)

    # merge function to  merge all sublist having common elements.
    def _merge_common(self, lists):
        neigh = defaultdict(set)
        visited = set()
        for each in lists:
            for item in each:
                neigh[item].update(each)

        def comp(node, neigh=neigh, visited=visited, vis=visited.add):
            nodes = set([node])
            next_node = nodes.pop
            while nodes:
                node = next_node()
                vis(node)
                nodes |= neigh[node] - visited
                yield node
        for node in neigh:
            if node not in visited:
                yield sorted(comp(node))

    def _recursive_inheritance(self, md, inh_feature, inh_md):
        for k, v in md.items():
            if k == '__self__':
                if v['Constraints'] is not None:
                    for constraint in v['Constraints']:
                        if inh_md['__self__']['Constraints'] is None:
                            inh_md['__self__']['Constraints'] = []
                        if constraint not in inh_md['__self__']['Constraints']:
                            constr_md = self.workspace.constraints[constraint]
                            inh_md['__self__']['Constraints'].append(self.feature_initializer.constraint_initializer.parse_constraint(constr_md['Object'],
                                                                                              inh_feature)['ID'])
            else:
                self._recursive_inheritance(v, f'{inh_feature}.{k}', inh_md[k])

    def _unique_x_in_y_handling(self, constraint, metadata):
        feature_childrens = self.workspace.get_feature_childrens(list(metadata[2].keys())[0], True)
        feature_childrens_filtered = [x for x in feature_childrens if x.rsplit('.')[-1] == metadata[1]]
        for feature in feature_childrens_filtered:
            constraint['Metadata']['Read']['Value'].append(feature)

    def _filter_x_where_y_handling(self, constraint, expression, parent_feature, metadata, assign_type):
        for condition in constraint['Metadata']['Precedence'][expression].values():
            # TODO test this condition set
            if isinstance(condition, dict):
                for feature_name, feature_type in condition.items():
                    split_check = feature_name.split(f'{parent_feature}.')
                    # to get all occurences of affected features
                    # i.e., for constraint filter childs.A where Type == 'Category'
                    # Waffle needs to get all childrens of A, e.g., A.B, A.C, A.D
                    # and then check A.B.Type, A.C.Type, A.D.Type
                    # Here, second_part means condition feature that will be attached, for this example - Type
                    # for the first part A.B, A.C, A.D will be substituted to get full feature paths
                    second_part = split_check[-1] if len(split_check) > 1 else None
                    first_part = metadata[1]
                    for first_part_name, first_part_type in first_part.items():
                        if first_part_type != 'Childs':
                            full_name = f'{first_part_name}.{second_part}' if second_part is not None else first_part_name
                            try:
                                self.workspace.read_metadata(full_name)
                                constraint['Metadata'][assign_type][feature_type].append(full_name)
                                if feature_name not in constraint['Metadata']['FilterStub'].keys():
                                    constraint['Metadata']['FilterStub'].update({feature_name: {}})
                                constr_data = {full_name: {'initial': first_part_name, 'additional': second_part}}
                                constraint['Metadata']['FilterStub'][feature_name].update(constr_data)
                            except KeyError:
                                pass
            # TODO check this condition set
            elif isinstance(condition, str):
                first_part = metadata[1]
                second_part = condition
                for first_part_name, first_part_type in first_part.items():
                    if first_part_type != 'Childs':
                        full_name = f'{first_part_name}.{second_part}' if second_part is not None else first_part_name
                        try:
                            self.workspace.read_metadata(full_name)
                            constraint['Metadata'][assign_type]['Value'].append(full_name)
                            if second_part not in constraint['Metadata']['FilterStub'].keys():
                                constraint['Metadata']['FilterStub'].update({second_part: {}})
                            constr_data = {full_name: {'initial': first_part_name, 'additional': second_part}}
                            constraint['Metadata']['FilterStub'][second_part].update(constr_data)
                        except KeyError:
                            pass

    def _sequence_restriction_analysis(self, parent_dependencies):
        sequence_restrictions = {}
        element_pattern = {
            'Before': [],
            'After': []
        }

        # define restrictions, e.g., feature A.B must be configured after feature A but before constraint A.B > 2
        for dependency in self.dependencies:
            if dependency not in parent_dependencies:
                for index, element in enumerate(dependency):
                    if element not in sequence_restrictions.keys():
                        sequence_restrictions.update({element: copy.deepcopy(element_pattern)})
                    connection = 'Before' if index == 0 else 'After'
                    sequence_restrictions[element][connection].append(dependency[0 if connection == 'After' else 1])
        return sequence_restrictions

    def _group_constraint_dependencies(self, sequence_restrictions):
        groups = []
        for element, data in sequence_restrictions.items():
            if element.startswith('Constraint_'):
                group = data['After'] + data['Before']
                group_filtered = []
                # TODO wrong logic - need to split groups in some cases (see brise.wfl in examples)
                # to filter 'After' dependencies, i.e., if some element should be configured after
                # features A and A.B, Waffle leaves only the latter for dependency graph simplification
                for elem in group:
                    include = True
                    for elem_alt in group:
                        if (a := elem.split('-')[0]) in (b := elem_alt.split('-')[0]) and a != b:
                            include = False
                    if include is True:
                        group_filtered.append(elem)
                groups.append(group_filtered)
        # dict for faster access using ID
        constraint_groups = {}
        for index, group_merged in enumerate(list(self._merge_common(groups))):
            constraint_groups.update({f'Waffle_Constraint_Group_{index}': group_merged})
        return constraint_groups

    def _replace_dependencies_that_are_in_group(self):
        # i.e., 'Waffle_Constraint_Group_{index}'
        new_deps = []

        # dependencies that will be replaced
        rm_deps = []
        rm_deps_dict = {}

        for index, dep in enumerate(self.dependencies):
            temp_dict = {}
            upd_flag = False
            for index_alt, elem in enumerate(dep):
                # fill in all dependencies to remove
                for group_name, group in self.constraint_groups.items():
                    if elem in group:
                        temp_dict.update({index_alt: group_name})
                        upd_flag = True
                        if index not in rm_deps:
                            rm_deps.append(index)
                            if group_name not in rm_deps_dict.keys():
                                rm_deps_dict.update({group_name: []})
                            rm_deps_dict[group_name].append(dep)
                if index_alt not in temp_dict.keys():
                    temp_dict.update({index_alt: elem})
            # add new dependency
            if upd_flag is True:
                new_deps.append((temp_dict[0], temp_dict[1]))
        # reverse to prevent index shift during removing
        for index in sorted(rm_deps, reverse=True):
            del self.dependencies[index]
        self.dependencies.extend(new_deps)
        return rm_deps_dict

    def _define_configuration_sequence(self, independent_constraints, rm_deps_dict):
        self.configuration_sequence, self.cycles = topo_sort(self.dependencies)
        # TODO check whether this is required
        for i_constr in independent_constraints:
            self.configuration_sequence.remove(i_constr)
            index_last = 0
            for dep in self.dependencies:
                if i_constr == dep[1] and (check := self.configuration_sequence.index(dep[0])) > index_last:
                    index_last = check
            self.configuration_sequence.insert(index_last + 1, i_constr)

        # constraint validation sequence was defined based on constraint group dependencies
        # it is correct in general, but inner group dependencies are not taken into account here
        # i.e., Waffle knows that constraint_1 and constraint_2 should be validated
        # after Waffle_Constraint_Group_1 features configuration
        # but at this point there is not defined whether constraint_1 or constraint_2 should be validated first
        # therefore, Waffle performs group level topology sorting to define that
        for constraint_group_id, dependencies_to_remove in rm_deps_dict.items():
            constraint_group_configuration_sequence, _ = topo_sort(dependencies_to_remove)
            constraint_sequence = [x for x in constraint_group_configuration_sequence if x.startswith('Constraint_')]
            constr_names = []
            constr_index = []
            # collect metadata for constraints that goes after constraint group
            for index in range(self.configuration_sequence.index(constraint_group_id), len(self.configuration_sequence) - 1):
                if self.configuration_sequence[index + 1].startswith('Constraint_'):
                    constr_names.append(self.configuration_sequence[index + 1])
                    constr_index.append(index + 1)
                else:
                    break
            constr_names_new = []
            # replace constraints validation sequence with the correct one
            for constr in constraint_sequence:
                if constr in constr_names:
                    constr_names_new.append(constr)
            for enum_index, seq_index in enumerate(constr_index):
                if enum_index < len(constr_names_new):
                    self.configuration_sequence[seq_index] = constr_names_new[enum_index]
        logging.debug('-----------------------------------')
        logging.debug(pprint.pformat(self.workspace.inheritance))

        # to define wizard steps (constraints are validated after connected wizard configuration step)
        self.sequence_filtered = []
        for step in self.configuration_sequence:
            if not step.startswith('Constraint_'):
                self.sequence_filtered.append(step)

        logging.debug(pprint.pformat(self.dependencies))
        logging.debug(pprint.pformat(self.configuration_sequence))
        logging.debug(pprint.pformat(self.constraint_groups))
