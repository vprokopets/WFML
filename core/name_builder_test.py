import copy
import re
import numpy as np
from pprint import pprint

feature_pattern = {
    'Value': None,
    'Type': None,
    'Fcard': None,
    'Gcard': None,
    'Active': None,
    'Abstract': None
}

constraint_pattern = {
    'Object': None,
    'Stage': None,
    'Precedences': None,
    'Active': None
}

top_level_pattern = {
    'Features': {},
    'Constraints': {}
}

def define_feature(type=None, fcard={'Original': 1}, gcard={'Original': None}, abstract=None):
    feature = copy.deepcopy(feature_pattern)
    feature['Type'] = type
    feature['Fcard'] = fcard
    feature['Gcard'] = gcard
    feature['Abstract'] = abstract
    return feature

def name_builder(feature, namespace, cardinality_type=None):
    feature_name = ''
    feature_list = {}
    feature_split = feature.split('.')
    if len(feature_split) == 1:
        features = []
        fcard = namespace[feature]['Fcard']
        for i in range(0, int(fcard['Original'])):
            features.append(f'{feature}_{i}' if int(fcard['Original']) > 1 else feature)
        feature_list.update({feature: features})
        return features
    for index, part in enumerate(feature_split):
        parent_feature = feature_name
        if cardinality_type == 'Fcard' and index == len(feature_split) - 1:
            if feature_list == {}:
                features = [part]
            else:
                features = []
                for feature in feature_list[feature_split[index - 1]]:
                    features.append(f'{feature}.{part}')
            gcard = namespace[parent_feature]['Gcard']
            features = filter_gcards(gcard, features)
            feature_list.update({part: features})
            break
        features = []
        feature_name = f'{feature_name}.{part}' if feature_name != '' else part
        fcard = namespace[feature_name]['Fcard']
        #print(fcard)
        if feature_list == {}:
            for i in range(0, int(fcard['Original'])):
                features.append(f'{part}_{i}' if int(fcard['Original']) > 1 else part)
        else:
            for key in fcard.keys():
                if key != 'Original':
                    for feature in feature_list[feature_split[index - 1]]:
                        if key.rsplit('.', 1)[0] == feature:
                            for i in range(0, int(fcard[key])):
                                features.append(f'{feature}.{part}_{i}' if int(fcard[key]) > 1 else f'{feature}.{part}')
                elif (key == 'Original' and len(fcard.keys()) == 1):
                    for feature in feature_list[feature_split[index - 1]]:
                        for i in range(0, int(fcard['Original'])):
                            features.append(f'{feature}.{part}_{i}' if int(fcard[key]) > 1 else f'{feature}.{part}')

            if cardinality_type != 'Gcard':
                gcard = namespace[parent_feature]['Gcard']
                features = filter_gcards(gcard, features)

        feature_list.update({part: features})
    return feature_list[feature_split[-1]]

def filter_gcards(gcard, features):
    gcard_features = []

    for key, value in gcard.items():
        if key != 'Original':
            for raw_feature in features:
                if len(raw_feature.split('.')[-1].split('_')) > 1:
                    feature = raw_feature.rsplit("_", 1)[0]
                else:
                    feature = raw_feature
                if feature == f'{key}.{value}':
                    gcard_features.append(raw_feature)
    if len(gcard.keys()) > 1:
        features = gcard_features
    return features


def get_unresolved_cardinalities(feature, namespace):
    fcards = []
    gcards = []
    for key, value in namespace.items():
        fcard = value['Fcard']['Original']
        gcard = value['Gcard']['Original']
        if key.split('.')[0] == feature:
            if len(value['Gcard'].keys()) == 1:
                if gcard in ['or', 'mux', 'xor']\
                        or isinstance(gcard, int)\
                        or re.match(r'^\d+$', str(gcard)):
                    gcards.append(key)
                elif isinstance(gcard, str):
                    gcards.append(key)
                    strspl = gcard.split(',')
                    for lexem in strspl:
                        if not (re.match(r'(\d+\.\.)+\d+', lexem) or re.match(r'^\d+$', lexem)):
                            gcards.remove(key)
            if len(value['Fcard'].keys()) == 1:
                if not isinstance(fcard, int) and not isinstance(fcard, list):
                    fcards.append(key)
    print(fcards)
    print(gcards)
    sublayer = define_next_sublayer(fcards, gcards, namespace)
    return sublayer

def get_unresolved_features(feature, namespace):
    result = {}
    for key, value in namespace.items():
        if key.split('.')[0] == feature:
            if value['Type'] is not None and value['Value'] is None:
                result.update({key: value['Type']})
    print(result)
    if result == {}:
        result = None
    else:
        for key in list(result.keys()):
            names = name_builder(key, namespace)
            for name in names:
                result.update({name: result[key]})
            result.pop(key, None)
    return result

def define_next_sublayer(fcards, gcards, namespace):
    result = {'Fcard': {}, 'Gcard': {}}
    cardinalities = np.unique(fcards + gcards)

    for card in cardinalities:
        card_split = card.split('.')
        print(card_split)
        find = ''
        for part in card_split:
            find = f'{find}.{part}' if find != '' else part
            print(find)
            if find in fcards:
                result['Fcard'].update({find: namespace[find]['Fcard']})
                break
            elif find in gcards:

                result['Gcard'].update({find: namespace[find]['Gcard']})
                print(result['Gcard'])
                break
    if result['Fcard'] == {} and result['Gcard'] == {}:
        result = None
    else:
        for cardinality_type in ['Fcard', 'Gcard']:
            for key in list(result[cardinality_type].keys()):
                print(key)
                names = name_builder(key, namespace, cardinality_type)
                print(f'names:{names}')
                if isinstance(names, list):
                    for name in names:
                        result[cardinality_type].update({name: result[cardinality_type][key]})
                    result[cardinality_type].pop(key, None)
    return result

def define_layer(top_level_feature):
    namespace = top_level_pattern['Features']

    sublayer = get_unresolved_cardinalities(top_level_feature, namespace)

    print(f'Following cardinalities need to be set up: {sublayer}')
    if sublayer is None:
        sublayer = get_unresolved_features(top_level_feature, namespace)
        print(f'Following features need to be configured: {sublayer}')
    return sublayer

def update_feature(feature, new_value, top_level_features):
    update_type = new_value.keys()[0]
    top_level_features[feature][update_type] = new_value[update_type]
    return top_level_features


a = define_feature(fcard={'Original': 2}, gcard={'Original': 'xor'})
b = define_feature()
c = define_feature(fcard={'Original': 1})
d = define_feature(type='integer')
d1 = define_feature()
f = define_feature(type='integer')
e = define_feature(type='integer')

top_level_pattern['Features'].update({'a': a})
top_level_pattern['Features'].update({'a.b': b})
top_level_pattern['Features'].update({'a.b.d': d})
top_level_pattern['Features'].update({'a.b.e': e})
top_level_pattern['Features'].update({'a.c': c})
top_level_pattern['Features'].update({'a.c.d': d1})
top_level_pattern['Features'].update({'a.c.d.f': f})
top_level_pattern['Features'].update({'a.c.d.e': e})

pprint(top_level_pattern)

res = define_layer('a')


#print('_________Test Fcard____________')
#fcards = get_unresolved_cardinalities('a', top_level_pattern['Features'], 'Fcard')
#print(fcards)
#print('_________Test Gcard____________')
#gcards = get_unresolved_cardinalities('a', top_level_pattern['Features'], 'Gcard')
#print(gcards)
#print('_________Test Layer____________')
#res = define_next_sublayer(fcards, gcards, top_level_pattern['Features'])
#print(res)
#print('________Test features__________')
#print(get_unresolved_features('a', top_level_pattern['Features']))

#print('__________Test name____________')
#pprint(name_builder('a.c.d.e', top_level_pattern['Features']))
#print('_______________________________')
#pprint(name_builder('a.c.d.f', top_level_pattern['Features']))