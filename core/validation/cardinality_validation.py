from core.auxiliary import is_card_defined


class CardinalityValidator:
    def __init__(self, workspace):
        self.workspace = workspace

    def check_cardinality_in_constraints(self, value, card_type, name):
        # TODO Currently, this fuction is not used - needs to be reimplemented in the future
        for constraint in self.constraints.values():
            constr_md = constraint['Metadata']
            check = self.get_feature_mappings(constr_md['ParentFeature'], self.metamodel)
            if check != []:
                for assign_type in ['Assign', 'Read']:
                    for feature_type in ['Fcard', 'Gcard', 'Value']:
                        if not (assign_type == 'Assign' and feature_type == 'Fcard'):
                            for feature in constr_md[assign_type][feature_type]:
                                check1 = self.get_feature_mappings(feature, self.metamodel)
                                # TODO new cardinality check mechanism
                                if feature in constr_md['FeaturesPrec'].keys():
                                    if check1 == [] and any([x not in self.PREC_BOOL
                                                             and not (x == 'prec12' and feature_type == 'Fcard')
                                                             for x in constr_md['FeaturesPrec'][feature]]):
                                        raise Exception(f'{card_type} cardinality value {value} for feature {name}'
                                                        f'leads to inability to validate constraint {constr_md['Expression']}',
                                                        name)

    def check_cardinality_value(self, name, value, card_type):
        md = self.workspace.read_feature_data(name)
        error_msg = ''
        old_value = md['__self__'][card_type]

        check_curr = is_card_defined(old_value)
        check_new = is_card_defined(value)

        if check_curr is False and check_new is True:
            if old_value in self.workspace.CARD_BOUNDARIES.keys():
                card_boundaries = self.workspace.CARD_BOUNDARIES[old_value]
            else:
                card_boundaries = []
                for card_interval in old_value.split(','):
                    if len(values := card_interval.split('..')) > 1:
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
                error_msg = f'Wrong cardinality value ({value_to_check}), must be in range {card_boundaries}'
        else:
            res = True

        return res, error_msg
