import logging

from core.auxiliary import cname

from textx import get_location


class ExpressionElement(object):
    def __init__(self, **kwargs):
        self.exception = None
        # textX will pass in parent attribute used for parent-child
        # relationships. We can use it if we want to.
        self.parent = kwargs.get('parent', None)

        # We have 'op' attribute in all grammar rules
        self.op = kwargs['op']
        self.src = True
        super(ExpressionElement, self).__init__()

    def check_cardinalities(self):
        """
        Function to check whether current cardinalities are applicable.
        """
        # TODO: Update cardinality rules for each prec. class (currently active for prec12 only)
        if len(self.op) > 1:
            res = self._get_mappings()
            for feature, mappings in res.items():
                if len(mappings) > 12:
                    msg = f'Cardinality value of {feature} should be equal 1 (currently {len(mappings)})'
                    raise Exception(self.get_error_message(msg))
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.check_cardinalities()

    def connect_waffle(self, api=None):
        """
        Function to initialize constraint object attributes.
        Also, it detects any features that are present in other tree branches.
        As a result, a connection (own feature - another branch feature) is assigned.

        INPUTS
        reverse (type = bool): the flag that reverses the connection direction.
        api (type = Waffle() object): Waffle API object.
        """
        self.api = api
        if isinstance(self.op, list):
            for part in self.op:
                if isinstance(part, ExpressionElement):
                    part.connect_waffle(api)
        elif isinstance(self.op, ExpressionElement):
            self.op.connect_waffle(api)

    def get_error_message(self, message):
        """
        Function to create a formatted error message.

        INPUTS
        message (type = string): unformatted error message.

        RETURN
        msg (type = string): formatted error message.
        """
        ol = self._tx_position_end - self._tx_position
        msg = ''.join((f'{message}.\n',
                       f'Constraint expression: {self.constr_md['Expression']}\n'
                       f'Error position: Line {get_location(self)["line"]},',
                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol}\n'))
        return msg

    def validate_constraint(self, constr_md):
        logging.debug('Inner constraint function')
        logging.debug(constr_md['Mappings'].values())
        for index, mapping in enumerate(mappings := constr_md['Mappings'].values()):
            if mapping['Active'] is True and mapping['Validated'] is False:
                self.mapping_md = {
                    'Index': index,
                    'Current': mapping['Comb'],
                    'Total': len(mapping['Comb']),
                    'All': [x['Comb'] for x in mappings],
                    'ExceptionFlag': False,
                    'FilterFlag': None
                }
                self._parse(self.mapping_md, constr_md)
                logging.debug(f'The mapping {index} was validated.')
            logging.debug((f'The mapping {index} is {'not' if mapping['Active'] is False else ''} active '
                           f'and was {'not' if mapping['Validated'] is False else ''} validated.'))
        logging.info(f'All mappings for constraint {constr_md['Expression']} were checked.')
        for mapping in mappings:
            mapping['Validated'] = True

    def _boolify(self, feature_metadata):
        """
        Function to transform feature to boolean type.
        If the input feature is not boolean, then we show the presence of this feature.

        INPUTS
        feature (type = any): feature to check

        RETURN
        result (type = bool): the result of transformation.
        """
        if not isinstance(feature_metadata, bool):
            try:
                return self.api.workspace.feature_is_active(feature_metadata['Fname'])
            except Exception:
                return True
        else:
            return feature_metadata

    def _check_exception(self, res: bool, err_msg: str):
        """
        Function to check should an exception be triggered.
        It depends on self.exception attribute.
        It prevents the triggering of an exception for inner boolean expressions while they are a part of another expression.

        INPUTS
        res (type = bool): check results.
        err_msg (type = string): an error message that can be displayed
        """
        if res is False and self.exception is True:
            raise Exception(self.get_error_message(err_msg), list(self.mapping_md['Current'].values()))

    def _get_mappings(self):
        """
        Function to get a mapped feature clone according to the mapping table.

        RETURN
        result (type = string): mapped feature clone.
        """
        result = {}
        for part in self.op:
            if isinstance(part, ExpressionElement):
                sub = part._get_mappings()
                for key, value in sub.items():
                    if key not in result.keys():
                        result.update({key: value})
                    else:
                        unique = list(set(result[key] + value))
                        result.update({key: unique})
        return result

    def _get_value(self, feature_metadata, ftype=None):
        logging.debug(f'Getting feature data for {feature_metadata}')
        if isinstance(feature_metadata, dict):
            if self.mapping_md['FilterFlag'] is not None and 'Fname' in feature_metadata.keys():
                feature_metadata_new = self._filter_stub(feature_metadata)
                if feature_metadata != feature_metadata_new:
                    feature_metadata = feature_metadata_new
                    logging.debug('SWAP HERE')
                else:
                    return feature_metadata['Fname']
            ftype = "Value" if feature_metadata['IsFeature'] is False else ftype
            return feature_metadata[feature_metadata['Ftype'] if ftype is None else ftype]
        else:
            return feature_metadata

    def _filter_stub(self, feature_metadata):
        if feature_metadata['Fname'] in self.mapping_md['FilterFlag'].keys():
            feature_metadata_new = self.api.workspace.read_metadata(self.mapping_md['FilterFlag'][feature_metadata['Fname']])['__self__']
            feature_metadata_new.update({
                'IsFeature': True,
                'Ftype': feature_metadata['Ftype'],
            })
            logging.debug((f'Feature metadata was successfully swapped from {feature_metadata['Fname']} '
                          f'to {feature_metadata_new}'))
        else:
            feature_metadata_new = feature_metadata
        return feature_metadata_new

    def _parse(self, mapping_md, constr_md):
        """
        Function to parse an expression string in self object.

        RETURN
        ret (variable type): result of parsing.
        """
        self.mapping_md = mapping_md
        self.constr_md = constr_md
        if len(self.op) == 1:
            ret = self.op[0]._parse(self.mapping_md, self.constr_md)
        else:
            if self.mapping_md['ExceptionFlag'] is False:
                self.exception, self.mapping_md['ExceptionFlag'] = True, True
            if cname(self) != 'prec23':
                self.res = [self.op[x]._parse(self.mapping_md, self.constr_md) if isinstance(self.op[x], ExpressionElement)
                            else self.op[x] for x in range(len(self.op))]
            ret = self.value
        return ret
