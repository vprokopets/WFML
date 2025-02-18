import itertools
import logging
import pprint


class ConstraintValidator:
    def __init__(self, workspace, storage):
        self.workspace = workspace
        self.storage = storage

    def validate_constraints(self):
        print('---------------------Validating constraints-------------------------')
        for index in range(self.storage.configuration_sequence.index(self.workspace.current_stage) + 1,
                           len(self.storage.configuration_sequence)):
            if ((elem := self.storage.configuration_sequence[index]).startswith('Constraint_')):
                logging.debug(f'Constraint {elem}')
                for constraint in self.workspace.constraints.values():
                    if constraint['ID'] == elem:
                        constraint_metadata = constraint['Metadata']
                        logging.debug('======================================================')
                        logging.info(f'Evaluating constraint {constraint_metadata['Expression']}')   
                        self._get_constraint_mappings(constraint)
                        self.workspace.constr_err_md = {}
                        if self.workspace.debug_mode is False:

                            try:
                                constraint['Object'].name.validate_constraint(constraint_metadata)
                            except Exception as e:
                                mapping_md = constraint['Object'].name.mapping_md
                                for feature, mapping in mapping_md['Current'].items():
                                    if feature in constraint_metadata['FeaturesPrec'].keys():
                                        self.workspace.constr_err_md.update({feature: self.workspace.read_metadata(mapping)})
                                logging.exception("Constraint validation was unsuccessfull!")
                                try:
                                    msg, _ = e.args
                                    ret = e
                                    exception_type = 'Waffle validation error'
                                except ValueError:
                                    msg = constraint['Object'].name.get_error_message(f'{e}')
                                    values = constraint['Object'].name.mapping_md['Current'].values()
                                    ret = Exception(msg, list(values))
                                    exception_type = 'Python exception'
                                return ret, exception_type
                        else:
                            constraint['Object'].name.validate_constraint(constraint_metadata)
                        break
            else:
                break
        return True, None

    def _get_constraint_mappings(self, constraint):

        features = {
            'Parent': [],
            'Fcard': [],
            'Value': []
        }

        flat_mappings = {
            'Parent': [],
            'Fcard': [],
            'Value': []
        }
        all_mappings = {}
        for type in ['Assign', 'Read']:
            for field in ['Fcard', 'Gcard', 'Value']:
                if type == 'Assign' and field == 'Fcard':
                    keyword = 'Parent'
                elif type == 'Read' and field in ['Gcard', 'Value']:
                    keyword = 'Value'
                else:
                    keyword = 'Fcard'
                full_tree = False if type == 'Assign' and field == 'Fcard' else True
                features_arr = constraint['Metadata'][type][field]
                for feature in features_arr:
                    split = feature.split('.')
                    for index, _ in enumerate(split[:len(split) if full_tree is False else len(split) - 1]):
                        if (ftr := '.'.join(split[:index + 1])) not in features_arr:
                            features_arr.append(ftr)

                features[keyword].extend(features_arr)
        features['Fcard'].append(constraint['Metadata']['ParentFeature'])

        features_to_configure = []
        for tlf in self.workspace.features.keys():
            features_to_configure.append(self.workspace.get_undefined_features(tlf, all_features=True))
        for k, v in features.items():
            for feature in set(v):
                if feature in constraint['Metadata']['FeaturesPrec'].keys():
                    filter = False if (any([x in self.workspace.prec_bool for x in constraint['Metadata']['FeaturesPrec'][feature]])
                                       or feature in constraint['Metadata']['Read']['Fcard']
                                       or feature in constraint['Metadata']['Assign']['Fcard']) else True
                else:
                    filter = True
                if feature not in all_mappings.keys():
                    all_mappings.update({feature: []})
                full_mapps = self.workspace.get_feature_mappings(feature, self.workspace.features, filter)
                if filter is False:
                    for mapps in full_mapps:
                        for i, _ in enumerate(mapps_spl := mapps.split('.')):
                            mapps_compose = '.'.join(mapps_spl[:i + 1])
                            if (mapps_orig := self.workspace.get_original(mapps_compose)) not in all_mappings.keys():
                                all_mappings.update({mapps_orig: []})
                            if mapps_compose not in all_mappings[mapps_orig]:
                                all_mappings[mapps_orig].append(mapps_compose)
                for mapps in full_mapps:
                    if mapps not in all_mappings[feature]:
                        all_mappings[feature].append(mapps)
                flat_mappings[k].extend(full_mapps)
        # TODO Improve unique x in y handling
        # -------------hotfix for unique x in y--------------------
        hotfix = True
        if hotfix is True:
            rm_mappings = []
            for k_prec, v_prec in constraint['Metadata']['Precedence'].items():
                if v_prec['Class'] == 'prec50':
                    for k_map, v_map in all_mappings.items():
                        if k_map.startswith(list(v_prec[2].keys())[0]) and k_map.rsplit('.')[-1] == v_prec[1] and v_map == []:
                            rm_mappings.append(k_map)

            for feature in rm_mappings:
                del all_mappings[feature]
        # ---------------------------------------------------------
        all_mappings_list = list(all_mappings.values())
        for part in all_mappings_list:
            part = list(set(part))
        combinations = itertools.product(*all_mappings_list)

        logging.debug(f'Mapping combinations for constraint {constraint['Metadata']['Expression']}')

        filtered_combinations = self._filter_combinations(combinations)
        logging.debug('---------------------------------')
        logging.debug(pprint.pformat(filtered_combinations))
        for comb in filtered_combinations:
            if str(comb) not in constraint['Metadata']['Mappings'].keys():
                subres = {}
                for feature in comb:
                    subres.update({self.workspace.get_original(feature): feature})
                constraint['Metadata']['Mappings'].update({str(comb): {
                    'Comb': subres,
                    'Active': True,
                    'Validated': False
                }})

        matched_features = []
        for k, v in flat_mappings.items():
            keywords = ['Gcard', 'Value'] if k == 'Value' else ['Fcard']
            for kw in keywords:
                for tlf_features_to_configure in features_to_configure:
                    for x in v:
                        if (x in tlf_features_to_configure[kw]
                           and self.workspace.get_original(x) not in constraint['Metadata']['Assign']['Fcard']):
                            matched_features.append(x)
        for mapping in constraint['Metadata']['Mappings'].values():
            parent_feature = mapping['Comb'][constraint['Metadata']['ParentFeature']]

            parent_check = self.workspace.read_metadata(parent_feature)['__self__']['Active']
            match_check = any([mf in mapping['Comb'].values() for mf in matched_features])

            mapping['Active'] = False if (match_check is True or parent_check is False) else True
            if mapping['Active'] is False:
                logging.debug((f'Mapping {mapping} for constraint {constraint['Metadata']['Expression']} '
                               f'was disabled. Parent check {parent_check} (False). Match check {match_check} (True)'))
                if match_check is True:
                    res = {}
                    for mf in matched_features:
                        res.update({mf: mf in mapping['Comb'].values()})
                    logging.debug(f'Match check disabled this constraint: {res}.')
                if parent_check is False:
                    logging.debug(f'Parent check disabled this constraint: {parent_feature} is not active.')

    def _filter_combinations(self, combinations):
        res = []
        for comb in combinations:
            logging.debug('____________________________')
            logging.debug(comb)
            valid_elems = {}
            valid_comb = True
            for elem in comb:
                name_split = elem.split('.')
                for index, _ in enumerate(name_split):
                    fname = '.'.join(name_split[:index+1])
                    if (fname_orig := self.workspace.get_original(fname)) not in valid_elems:
                        valid_elems.update({fname_orig: fname})
                    else:
                        if valid_elems[fname_orig] != fname:
                            logging.debug(f'COMBINATION {comb} is not valid '
                                          f'due to {valid_elems[fname_orig]} != {fname} | {fname_orig}')
                            valid_comb = False
            logging.debug(f'Adding combination {comb}')
            if valid_comb is True:
                res.append(comb)
        return res
