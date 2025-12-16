import copy
import logging
import re

from core.auxiliary import is_card_defined


class Workspace:
    # Prevent usage as a feature name
    KEYWORDS = ['abstract', 'all', 'assert', 'disj', 'else', 'enum',
                'if', 'in', 'lone', 'max', 'maximize', 'min',
                'minimize', 'mux', 'no', 'not', 'one', 'opt',
                'or', 'product', 'res', 'some', 'sum', 'then', 'xor', '_', 'fcard', 'gcard', 'waffle.error']

    CARD_BOUNDARIES = {
        '*': [(0, 1e6)],
        '+': [(1, 1e6)],
        '?': [(0, 1)],
        'or': [(1, 1e6)],
        'xor': [(1, 1)]
    }
    PREC_BOOL = ['prec23', 'prec22', 'prec21', 'prec20', 'prec19', 'prec18', 'prec14', 'prec11', 'prec0', 'term']

    def __init__(self, api):
        self.api = api
        self.debug_mode = api.debug_mode

        self.features = {}
        self.constraints = {}
        self.inheritance = []
        self.initial_fcards = {}
        self.configuration_history = {}
        self.constraint_metadata = {}
        self.constr_err_md = {}
        self.constraint_groups_w = {}

        self.current_stage = None

        # TODO belongs to another module (move)
        self.dependency_graph_data = {}
        self.graph_colormap = {
            'Skipped': '#808080',
            'In Progress': '#3366CC',
            'Configured': '#008000'
        }

    def get_feature_base_name(self, feature):
        return re.sub(r'\_\d+', '', feature)

    def get_root_feature(self, feature):
        return feature.split('.')[0]

    def is_feature_active(self, name):
        # to extract data from hierarchical feature workspace
        feature_metadata = self.features
        for level in name.split('.'):
            feature_metadata = feature_metadata[level]
            if feature_metadata['__self__']['Active'] is False:
                return False
        return True

    def save_constraint_data(self):
        for k, v in self.constraints.items():
            self.constraint_metadata.update({k: v['Metadata']})

    def register_dependency_graph_layout(self, graph_data):
        # TODO move out of here
        self.dependency_graph_data = graph_data
        for node in self.dependency_graph_data['nodes']:
            if node['label_long'].startswith('Waffle_Constraint_Group_'):
                node['data'] = self.constraint_groups_w[node['label_long']]
            elif node['label_long'].startswith('Constraint_'):
                node['data'] = self.constraints[node['label_long']]['Metadata']['Expression'].replace("'", '"').replace('"', r'\"')
            else:
                node['data'] = self.read_feature_data(node['label_long'].split('-')[0])

    def change_dependency_graph_state(self, node, state):
        # TODO move out of here
        color = self.graph_colormap[state]
        self.dependency_graph_data['nodes'][self.dependency_graph_data['indices'][node]]['color'] = color

    def update_metadata(self, name, field, value, constraint=None):
        logging.info(f'Updating field "{field}" for feature "{name}" with value "{value}"')
        metadata = self.read_feature_data(name)
        metadata['__self__'][field] = value

        if self.current_stage is not None:
            if f'{name}-{field}' not in self.configuration_history:
                self.configuration_history.update({f"{name}-{field}": []})
            self.configuration_history[f'{name}-{field}'].append({
                "Type": field,
                "Value": value,
                "Source": f"Stage {self.current_stage}" if constraint is None else f"From constraint {constraint}",
                "Stage": self.api.storage.test_sequence.index(self.current_stage) + 1
            })
        if field == 'Inheritance':
            self.inheritance.append((name, value))
        elif field == 'Fcard':
            self.handle_fcards(name, metadata, value)
            self.update_child_history_cards(name, field, value, metadata)
        elif field == 'Gcard':
            self.handle_gcards(name, metadata, value)
            list_value = list(value) if not isinstance(value, list) else value
            for gcard_value in list_value:
                self.update_child_history_cards(name, field, gcard_value, metadata)

    def update_child_history_cards(self, parent_feature, card_type, card_value, md, prefix=None):
        for fname, fmetadata in md.items():
            if fname != '__self__':
                if (card_type == 'Fcard' and card_value == 0) or (card_type == 'Gcard' and card_value not in fname):
                    nfname = f'{prefix}.{fname}' if prefix is not None else f'{parent_feature}.{fname}'
                    if f'{nfname}-Fcard' not in self.configuration_history:
                        self.configuration_history.update({f'{nfname}-Fcard': []})
                    self.configuration_history[f'{nfname}-Fcard'].append({
                        "Type": 'Fcard',
                        "Value": 0,
                        "Source": f"Parent feature {parent_feature} || {card_type} with value {card_value}",
                        "Stage": self.api.storage.test_sequence.index(self.current_stage) + 1
                    })
                    if isinstance(fmetadata, dict):
                        self.update_child_history_cards(parent_feature, card_type, card_value, fmetadata, nfname)

    def handle_fcards(self, name, md, repeats):
        repeats = md['__self__']['Fcard']
        name_split = name.rsplit('.', 1)
        pname, fname = name_split[0], name_split[-1]
        tlf = len(name_split) == 1
        par_md = self.features if tlf is True else self.read_feature_data(pname)
        repl_md = {}
        if isinstance(repeats, int) and repeats > 0:
            for index in range(repeats):
                new_name = fname if repeats == 1 else f'{fname}_{index}'
                if new_name not in par_md:
                    repl_md.update({new_name: copy.deepcopy(md)})
                    repl_md[new_name]['__self__']['ActiveByFcard'] = True
            par_md.update(repl_md)
            for k, v in par_md.items():
                index = k.rsplit('_', 1)
                if (len(index) > 1 and index[-1].isdigit()) and (k != '__self__' and index[0] in fname):
                    v['__self__']['ActiveByFcard'] = False if len(index) > 1 and ((index[1].isdigit() and int(index[1]) >= repeats)
                                                                            or repeats == 1) else True
                    self.update_active_state(k if tlf is True else f'{pname}.{k}')
        md['__self__']['ActiveByFcard'] = False if (repeats != 1 and not isinstance(repeats, str)) else True
        md['__self__']['DeactStandard'] = True if (not isinstance(repeats, str) and repeats >= 1) else False

        self.update_active_state(name)

        # TODO update card check mechanism
        # self.check_cardinality_in_constraints(repeats, 'Feature', name)

    def get_feature_childrens(self, feature, full_tree=False, filter_active=True):
        md = self.read_feature_data(feature)
        res = []
        for k, v in md.items():
            if k != '__self__' and (v['__self__']['Active'] is True or filter_active is False):
                if full_tree is True:
                    res.extend(self.get_feature_childrens(f'{feature}.{k}', True))
                res.append(f'{feature}.{k}')
        return res

    def get_feature_mappings(self, feature, md, filter=True, layer=0, fname=''):
        res = []
        name_split = feature.split('.') if not isinstance(feature, list) else feature
        for k, v in md.items():
            if (k != '__self__'
                    and (v['__self__']['Active'] is True or (filter is False and v['__self__']['DeactStandard'] is False))
                    and self.get_feature_base_name(name_split[layer]) == self.get_feature_base_name(k)):
                if layer < len(name_split) - 1:
                    res.extend(self.get_feature_mappings(feature, v, filter, layer + 1, f'{fname}.{k}' if layer >= 1 else k))
                else:
                    res.append(f'{fname}.{k}' if layer >= 1 else k)
        return res

    def handle_gcards(self, name, md, value):
        if value not in ['xor', 'or']:
            if not isinstance(value, list):
                value = [value]
            for k, v in md.items():
                if k != '__self__':
                    v['__self__']['ActiveByGcard'] = True if any([k.rsplit('.', 1)[-1] == x for x in value]) else False
                    self.update_active_state(f'{name}.{k}')

            # TODO update card check mechanism
            # self.check_cardinality_in_constraints(value, 'Group', name)

    def read_feature_data(self, name: str, field: str = None):
        """
        Traverses the dictionary tree to find a feature.
        Raises ValueError if path is invalid.
        """
        mm = self.features
        try:
            for level in name.split('.'):
                mm = mm[level]
        except KeyError:
            raise ValueError(f"Feature path '{name}' not found in workspace.")

        if field is None:
            return mm

        if '__self__' not in mm:
            raise ValueError(f"Feature node '{name}' is missing metadata ('__self__').")

        return mm['__self__'].get(field)

    def calculate_active_state(self, metadata):
        """Determines if a feature is effectively active."""
        if metadata.get('Abstract') is not None:
            return False

        # A feature is active only if both its feature and group cardinalities allow it
        return metadata.get('ActiveByFcard', True) and metadata.get('ActiveByGcard', True)

    def update_active_state(self, name):
        md = self.read_feature_data(name)['__self__']
        md['Active'] = self.calculate_active_state(md)
        logging.debug(f'Update active state for {name}: {md['ActiveByFcard']} | {md['ActiveByGcard']} | {md['Active']}')

    def get_product(self, md, res):
        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True:
                self_value = {} if v['__self__']['Value'] is None else v['__self__']['Value']
                res.update({k: self_value})
                if len(v.values()) > 1:
                    res.update({k: self.get_product(v, res[k])})
        return res

    def get_unconfigured_features(self, tlf, md=None, layer=0, pname='', all_features=False):
        res = {
            'Fcard': [],
            'Gcard': [],
            'Value': []
        }
        md = self.features if md is None else md

        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True and (layer > 0 or tlf in k):
                feature_md = v['__self__']
                fname = f'{pname}.{k}' if layer >= 1 else k
                skip = False
                if not is_card_defined(feature_md['Fcard']):
                    res['Fcard'].append(fname)
                    skip = True
                if not is_card_defined(feature_md['Gcard']) and (fname not in res['Fcard'] or all_features is True):
                    res['Gcard'].append(fname)
                    skip = True
                if ((feature_md['Attribute'] not in [None, 'predefined'] and feature_md['Value'] is None)
                        and (fname not in res['Fcard'] or all_features is True)):
                    res['Value'].append(fname)
                    skip = True

                if len(v.values()) > 1 and (not skip or all_features):
                    subres = self.get_unconfigured_features(tlf, v, layer + 1, fname, all_features)
                    for md_type in res:
                        res[md_type].extend(subres[md_type])
        return res

    def get_next_constraints(self, step):
        return [] if step not in self.constraint_groups else self.constraint_groups[step]

    def activate_fcards(self):
        for feature, card_md in self.initial_fcards.items():
            self.handle_fcards(feature, card_md['MM'], card_md['Value'])

    def disable_abstract_features(self):
        for metadata in self.features.values():
            if metadata['__self__']['Abstract'] is not None:
                metadata['__self__'].update({'Active': False})

    def register_constraint_groups(self, constraint_groups):
        self.constraint_groups = constraint_groups

    def get_constraint_expression(self, constraint):
        return self.constraints[constraint]['Metadata']['Expression']
