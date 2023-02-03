import itertools
import re
import pandas as pd
import pprint
import string
import random
import copy

class GoD(object):
    pass


class Truths(object):
    def __init__(self, base: list, expression: str):
        self.base = base
        self.expression = expression
        self.res = {'Base': self.base}
        # generate the sets of booleans for the bases
        self.base_conditions = list(itertools.product([False, True],
                                                      repeat=len(base)))

        # regex to match whole words defined in self.bases
        # used to add object context to variables in self.phrases
        self.p = re.compile(r'(?<!\w)(' + '|'.join(self.base) + r')(?!\w)')
        combination_index = 0
        for conditions_set in self.base_conditions:
            combination_index += 1
            self.combination = {combination_index: {}}
            for index, var in enumerate(self.base):
                self.combination[combination_index].update({var: conditions_set[index]})
            subres = self.calculate(*conditions_set)
            self.combination[combination_index].update({'Result': subres})
            self.res.update(self.combination)

    def calculate(self, *args):
        # store bases in an object context
        g = Gob()
        for a, b in zip(self.base, args):
            setattr(g, a, b)

        item = self.p.sub(r'g.\1', self.expression)
        print(item)
        return pd.eval(item)


# a = Truths(['a', 'b', 'c'], '(a or c) xor b')
# print(a)
# pprint.pprint(a.res)

class Namespace:

    def __init__(self) -> None:
        self.initial_cdata_pattern = {
            'ActiveF': True,
            'ActiveG': True,
            'Fcard': None
        }

        self.initial_vdata_pattern = {
            'ActiveF': True,
            'ActiveG': True,
            'Gcard': None,
            'Value': None,
        }

        self.feature_pattern = {
            'Type': None,
            'Abstract': None,
            'SuperFeature': None,
            'Reference': None,
            'DeepReference': None,
            'RequiredFcard': None,
            'InitialC': copy.deepcopy(self.initial_cdata_pattern),
            'InitialV': copy.deepcopy(self.initial_vdata_pattern),
            'MappingsC': {},
            'MappingsV': {}
        }

        self.constraint_pattern = {
            'RelatedFeature': None,
            'Constraint': None,
            'HigherOperation': None,
            'Operations': [],
            'Read': {
                'Fcard': [],
                'Gcard': [],
                'Value': []
            },
            'Assign': {
                'Fcard': [],
                'Gcard': [],
                'Value': []
            },
            'Expression': '',
            'Pattern': {},
            'TruthTable': [],
            'Validated': False
        }

        self.top_level_pattern = {
            'Features': {},
            'Constraints': {},
            'ConstraintsValidationOrder': [],
            'Validated': False
        }

        self.namespace = {}
        self.var_attrc = ['Fcard']
        self.var_attrv = ['Value', 'Gcard']

    def generate_feature_sample(self, fname, params):
        pattern = copy.deepcopy(self.feature_pattern)

        tlf = fname.split('.')[0]
        if tlf not in self.namespace.keys():
            self.namespace.update({tlf: copy.deepcopy(self.top_level_pattern)})
        self.namespace[tlf]['Features'].update({fname: pattern})

        for key, value in params.items():
            self.update_namespace(fname, key, value, 'Initial')

        pattern['MappingsC'].update({fname: copy.deepcopy(self.namespace[tlf]['Features'][fname]['InitialC'])})
        pattern['MappingsV'].update({fname: copy.deepcopy(self.namespace[tlf]['Features'][fname]['InitialV'])})

    def generate_constraint_sample(self, rf, features, afeatures):
        pattern = copy.deepcopy(self.constraint_pattern)
        pattern['Read'] = features
        pattern['Assign'] = afeatures
        pattern['RelatedFeature'] = rf

        tlf = rf.split('.')[0]
        if tlf not in self.namespace.keys():
            self.namespace.update({tlf: copy.deepcopy(self.top_level_pattern)})
        self.namespace[tlf]['Constraints'].update({f'{random.random() * 1000}': pattern})

    def update_namespace(self, fname, field, value, mapping=None):
        tlf = fname.split('.')[0]

        if field in self.var_attrc:
            suffix = 'C'
        elif field in self.var_attrv:
            suffix = 'V'
        else:
            suffix = ''
        if (mapping == 'Initial' and suffix != ''):
            namespace = self.namespace[tlf]['Features'][fname][f'Initial{suffix}']
        elif mapping == 'Initial':
            namespace = self.namespace[tlf]['Features'][fname]
        else:
            namespace = self.namespace[tlf]['Features'][fname][f'Mappings{suffix}'][mapping]
        namespace[field] = value
        self.check_integrities(tlf)
        if field in ['Fcard', 'Gcard'] and mapping != 'Initial':
            self.activation_flag_update(self.namespace[tlf]['Features'], field, value, mapping)

    def get_feature(self, fname, ftype=None):
        original = self.get_original_name(fname)
        tlf = original.split('.')[0]
        suffix = 'C' if ftype == 'Fcard' else 'V'
        res = self.namespace[tlf]['Features'][original][f'Mappings{suffix}'][fname]
        return res

    def get_feature_childrens(self, fname, own_only_flag=True):
        res = {}
        original = self.get_original_name(fname)
        tlf = original.split('.')[0]
        namespace = self.namespace[tlf]['Features']
        for feature in namespace.values():
            for mapping, mvalue in feature['MappingsV'].items():
                is_child = (len(mapping.split('.')) - len(fname.split('.'))) == 1 if own_only_flag is True else (len(mapping.split('.')) - len(fname.split('.'))) >= 1
                if mapping.startswith(fname) and is_child is True:
                    res.update({mapping: mvalue})
        return res

    def activation_flag_update(self, namespace, field, value, mapping=None):
        filter_field = f'{mapping}.{value}' if field == 'Gcard' else mapping
        for feature, fvalue in namespace.items():
            for suffix in ['C', 'V']:
                for mapping, mvalue in fvalue[f'Mappings{suffix}'].items():
                    if field == 'Gcard':
                        if len(mapping.split('.')) > len(filter_field.split('.')) and filter_field.rsplit('.', 1)[0] in mapping:
                            mvalue['ActiveG'] = False if filter_field not in mapping else True
                    else:
                        if len(mapping.split('.')) > len(filter_field.split('.')) and filter_field in mapping:
                            if value == 0 or not isinstance(value, int):
                                mvalue['ActiveF'] = False
                            elif value >= 1:
                                if mapping.split(filter_field)[1][0] == '_':
                                    index = int(mapping.split(filter_field)[1][1])
                                    mvalue['ActiveF'] = False if index >= value else True

    def get_mappings_for_constraint(self, constraint_data):
        mappings = {'Assign': {}, 'Read': {}}
        constraint_ready = True
        for assign_type in ['Assign', 'Read']:
            for ftype in constraint_data[assign_type].keys():
                card_flag = True if ftype == 'Fcard' else False
                for feature in constraint_data[assign_type][ftype]:
                    tlf = self.get_original_name(feature[0])
                    namespace = self.namespace[tlf]['Features']
                    try:
                        fmappings = self.get_filtered_values(self.map_feature(feature, card_flag), namespace, False)
                        for mapping in fmappings['Value']:
                            split = mapping.split('.')
                            for index in range(0, len(split)):
                                fname = '.'.join(split[:index + 1])
                                original = self.get_original_name(fname)
                                if original not in mappings[assign_type].keys():
                                    mappings[assign_type].update({original: []})
                                if fname not in mappings[assign_type][original]:
                                    mappings[assign_type][original].append(fname)
                        print(f'Features {feature} {assign_type}: {self.get_filtered_values(self.map_feature(feature, False), namespace, False)}')
                    except Exception:
                        constraint_ready = False
        return constraint_ready, mappings

    def filter_mappings_for_constraint(self, constraint, mappings):
        res = {'Assign': None, 'Read': None}
        for assign_type in ['Assign', 'Read']:
            combinations = itertools.product(*mappings[assign_type].values())
            filtered_combinations = []
            counter = 0
            for comb in combinations:
                counter += 1
                rm = False
                for part in comb:
                    for x in comb:
                        if self.get_original_name(x).startswith(self.get_original_name(part)) and len(x.split(".")) > len(part.split(".")):
                            if not x.startswith(part):
                                rm = True
                                break
                if rm is False:
                    filtered_combinations.append(comb)
            print(f'Uniltered combinations for constraint {assign_type} {constraint} ({counter})')
            print(f'Filtered combinations for constraint {assign_type} {constraint} ({len(filtered_combinations)}): {filtered_combinations}')
            res[assign_type] = filtered_combinations
        return res

    def validate_constraints(self, tlf):
        for constraint, value in self.namespace[tlf]['Constraints'].items():
            constraint_ready, mappings = self.get_mappings_for_constraint(value)
            if constraint_ready is True:
                res = self.filter_mappings_for_constraint(constraint, mappings)
                if len(res['Assign']) > 0 and len(res['Assign']) != len(res['Read']):
                    print(f'Len of assign mappings ({len(res["Assign"])}) is not equal to len read mappings ({len(res["Read"])})')
            else:
                print(f'Constraint {constraint} is not ready to validate')

    def map_feature(self, fname, cardinalities=True):
        split = fname.split('.')
        tlf = split[0]
        names = []
        for index in range(1, len(split) + 1):
            name = '.'.join(split[:index])
            fnamespace = self.namespace[tlf]['Features'][name]
            names_temp = []
            for key, value in fnamespace[f'MappingsC'].items():
                if not (key == self.get_original_name(key) and len(fnamespace[f'MappingsC']) > 1):
                    if index == len(split) and cardinalities is True:
                        repeats = 1
                    elif not isinstance(value['Fcard'], int):
                        print(f'Not possible to map due to non-defined cardinality {key}: {value}')
                        return []
                    else:
                        repeats = value['Fcard']
                    if names != []:
                        prev_names = names
                    else:
                        prev_names = [key]
                    for prev_name in prev_names:
                        for i in range(0, repeats):
                            full_name = prev_name if names == [] else f'{prev_name}.{split[index - 1]}'
                            names_temp.append(f'{full_name}_{i}' if repeats > 1 or (cardinalities is False and f"{full_name}_{i}" in fnamespace[f'MappingsV'].keys()) else full_name)
            names = list(dict.fromkeys(names_temp))
        return names

    def preprocess_step(self, tlf):
        fcards, values = self.check_integrities(tlf)
        undefined_cards = self.get_undefined_cards(fcards, values, tlf)
        if undefined_cards is None:
            undefined_values = self.get_filtered_values(values, self.namespace[tlf]['Features'])
        return undefined_cards if undefined_cards is not None else undefined_values

    def check_integrities(self, tlf):
        fcards = self.check_integrity(tlf, True)
        values = self.check_integrity(tlf, False)
        return fcards, values

    def check_integrity(self, tlf, cardinality=True):
        result = []
        namespace = self.namespace[tlf]['Features']
        suffix = 'C' if cardinality is True else 'V'
        for feature, value in namespace.items():
            check = self.map_feature(feature, cardinality)
            if check != []:
                for key in check:
                    if key not in value[f'Mappings{suffix}'].keys():
                        value[f'Mappings{suffix}'].update({key: copy.deepcopy(value[f'Initial{suffix}'])})
                result = result + check
        # print(f'Feature {tlf}. {"Cardinality" if cardinality is True else "Value"}: {result}')
        return result

    def get_undefined_cards(self, listc, listv, tlf):
        result = {'Fcard': [], 'Gcard': []}
        namespace = self.namespace[tlf]['Features']
        fcards = self.get_undefined_fcards(listc, namespace)
        gcards = self.get_undefined_gcards(listv, namespace)
        for card_type in result.keys():
            card_type_list = fcards if card_type == 'Fcard' else gcards
            another_type_list = fcards if card_type == 'Gcard' else gcards
            for celement in card_type_list:
                flag = True
                for aelement in another_type_list:
                    if aelement in celement:
                        flag = False
                if flag is True:
                    result[card_type].append(celement)
        return result if result != {'Fcard': [], 'Gcard': []} else None

    def get_undefined_fcards(self, list, namespace):
        result = []
        for feature in list:
            original = self.get_original_name(feature)
            feature_active_flag = (namespace[original]['MappingsC'][feature]['ActiveF'] and namespace[original]['MappingsC'][feature]['ActiveG'])
            fcard_value = namespace[original]['MappingsC'][feature]['Fcard']
            if not isinstance(fcard_value, int) and feature_active_flag is True:
                result.append(feature)
        return result

    def get_undefined_gcards(self, list, namespace):
        result = []
        for feature in list:
            gcard_to_define = False
            original = self.get_original_name(feature)
            feature_active_flag = (namespace[original]['MappingsV'][feature]['ActiveF'] and namespace[original]['MappingsV'][feature]['ActiveG'])
            gcard_value = namespace[original]['MappingsV'][feature]['Gcard']
            if feature_active_flag is True:
                if gcard_value in ['or', 'mux', 'xor']\
                        or isinstance(gcard_value, int)\
                        or re.match(r'^\d+$', str(gcard_value)):
                    gcard_to_define = True
                elif isinstance(gcard_value, str):
                    gcard_to_define = True
                    strspl = gcard_value.split(',')
                    for lexem in strspl:
                        if not (re.match(r'(\d+\.\.)+\d+', lexem) or re.match(r'^\d+$', lexem)):
                            gcard_to_define = False
                if gcard_to_define is True:
                    result.append(feature)
        return result

    def get_filtered_values(self, list, namespace, undefined=True):
        result = {'Value': []}
        for feature in list:
            original = self.get_original_name(feature)
            feature_active_flag = (namespace[original]['MappingsV'][feature]['ActiveF'] and namespace[original]['MappingsV'][feature]['ActiveG'])
            feature_value = namespace[original]['MappingsV'][feature]['Value']
            feature_type = namespace[original]['Type']
            if feature_active_flag is True:
                if (feature_value is None and undefined is True and feature_type not in [None, 'Predefined']) or undefined is False:
                    result['Value'].append(feature)
        return result if result != {'Value': []} else None

    def get_original_name(self, name):
        """
        Function to clear feature's name from suffixes.

        INPUTS
        name (type = str): feature's name.

        RETURN
        transformed name.
        """
        split = name.split('.')
        split = split[1:] if split[0] in ['fcard', 'gcard', 'Fcard', 'Gcard'] else split
        construct = []
        for part in split:
            construct.append(re.sub(r'_[0-9]+', '', part))
        return '.'.join(construct) if len(construct) > 1 else construct[0]

namespace = Namespace()
namespace.generate_feature_sample('A', {'Fcard': 1, 'Gcard': None, 'Type': None})
namespace.generate_feature_sample('A.B', {'Fcard': '*', 'Gcard': None, 'Type': None})
namespace.generate_feature_sample('A.B.C', {'Fcard': 2, 'Gcard': None, 'Type': 'Integer'})
namespace.generate_feature_sample('A.D', {'Fcard': 1, 'Gcard': None, 'Type': None})
namespace.generate_feature_sample('A.D.E', {'Fcard': 2, 'Gcard': None, 'Type': 'String'})
namespace.generate_feature_sample('B', {'Fcard': 1, 'Gcard': None, 'Type': None})
namespace.generate_feature_sample('B.A', {'Fcard': 6, 'Gcard': None, 'Type': 'String'})
res = namespace.preprocess_step('A')


print(f'Res before: {res}')
res = namespace.preprocess_step('B')
namespace.update_namespace('A', 'Fcard', 3, 'A')
res = namespace.preprocess_step('A')
print(f'Res after fcard: {res}')

namespace.generate_constraint_sample('A.B', {'Fcard': [], 'Gcard': [], 'Value': ['B.A']}, {'Fcard': [], 'Gcard': [], 'Value': ['A.B.C']})
namespace.validate_constraints('A')
