import copy
import json
import itertools
import logging
import pprint
import re

from collections import defaultdict
from functools import reduce
from os.path import join, dirname
from textx import metamodel_from_file, get_location, get_metamodel
from textx.export import metamodel_export, model_export

from core.graph import Graph

# Global variables.
keywords = ['abstract', 'all', 'assert', 'disj', 'else', 'enum',
            'if', 'in', 'lone', 'max', 'maximize', 'min',
            'minimize', 'mux', 'no', 'not', 'one', 'opt',
            'or', 'product', 'res', 'some', 'sum', 'then', 'xor', '_', 'fcard', 'gcard', 'waffle.error']

# Logging configuration.
logging.basicConfig(format='%(levelname)s: %(asctime)s %(message)s', level=logging.INFO, datefmt='%m/%d/%Y %I:%M:%S %p')


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

    def parse_constraint(self, constr_md):
        # print('Inner constraint function')
        # pprint.pprint(constr_md['Mappings'].values())
        for index, mapping in enumerate(mappings:=constr_md['Mappings'].values()):
            pprint.pprint(mapping)
            if mapping['Active'] is True and mapping['Validated'] is False:
                mapping_md = {
                    'Index': index,
                    'Current': mapping['Comb'],
                    'Total': len(mapping['Comb']),
                    'All': [x['Comb'] for x in mappings],
                    'ExceptionFlag': False
                }
                # print(f'Parsing mapping {index + 1} of {len(mappings)} | Mapping values: {list(mapping['Comb'].values())}')
                self.parse(mapping_md, constr_md)
        for mapping in mappings:
            mapping['Validated'] = True
    
    def parse(self, mapping_md, constr_md):
        """
        Function to parse an expression string in self object.

        RETURN
        ret (variable type): result of parsing.
        """
        self.mapping_md = mapping_md
        self.constr_md = constr_md
        if len(self.op) == 1:
            ret = self.op[0].parse(self.mapping_md, self.constr_md)
        else:
            if mapping_md['ExceptionFlag'] is False:
                self.exception, mapping_md['ExceptionFlag'] = True, True
            if self.api.cname(self) != 'prec23':
                self.res = [self.op[x].parse(self.mapping_md, self.constr_md) if isinstance(self.op[x], ExpressionElement) else self.op[x] for x in range(len(self.op))]
            ret = self.value
        return ret
    
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

    def check_exception(self, res: bool, err_msg: str):
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

    def get_mappings(self):
        """
        Function to get a mapped feature clone according to the mapping table.

        RETURN
        result (type = string): mapped feature clone.
        """
        result = {}
        for part in self.op:
            if isinstance(part, ExpressionElement):
                sub = part.get_mappings()
                for key, value in sub.items():
                    if key not in result.keys():
                        result.update({key: value})
                    else:
                        unique = list(set(result[key] + value))
                        result.update({key: unique})
        return result

    def set_mappings(self, mappings):
        """
        Function to set the mapping table.

        INPUTS
        mappings (type = dict): features mapping table.
        """
        self.mapping_md = mappings
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.set_mappings(mappings)

    def check_cardinalities(self):
        """
        Function to check whether current cardinalities are applicable.
        """
        # TODO: Update cardinality rules for each prec. class (currently active for prec12 only)
        if len(self.op) > 1:
            res = self.get_mappings()
            for feature, mappings in res.items():
                if len(mappings) > 12:
                    msg = f'Cardinality value of {feature} should be equal 1 (currently {len(mappings)})'
                    raise Exception(self.get_error_message(msg))
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.check_cardinalities()

    def boolify(self, feature_metadata):
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
                return self.api.feature_is_active(feature_metadata['Fname'])
            except Exception:
                return True
        else:
            return feature_metadata

    def get_value(self, feature_metadata, ftype = None):
        if isinstance(feature_metadata, dict):
            ftype = "Value" if feature_metadata['IsFeature'] is False else ftype
            return feature_metadata[feature_metadata['Ftype'] if ftype is None else ftype]
        else:
            return feature_metadata

class prec24(ExpressionElement):
    @property
    def value(self):
        """
        prec24 class performs filter operation.

        RETURN
        ret (variable type): previous level object if no prec24 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.info(f'Level 24 Operation filter x where y.')
        self.api.keyword = 'ChildNamespace'
        key, condition = self.get_value(self.op[1].parse(self.mapping_md, self.constr_md)), self.op[2]
        self.api.keyword = ''
        return self.filter(condition, key)

    def filter(self, condition, key):
        """
        Function to filter features by constraint.

        INPUTS
        condition (type = ExpressionElement): constraint to check.
        key (type = dict): feature's namespace.

        RETURN
        res (type = list): list of filtered features.
        """
        res = []
        self.api.keyword = 'ReplaceFeature'
        keys = list(key.keys())
        tmp = []
        for item in keys:
            data = self.api.namespace[self.api.tlf]['Features'][self.api.get_original_name(item)]['MappingsV'][item]
            if data['ActiveF'] is True and data['ActiveG'] is True:
                tmp.append(item)
        for item in keys:
            self.api.replace_feature = item
            if self.get_value(condition.parse(self.mapping_md, self.constr_md)) is True:
                res.append(item)

        self.api.keyword = ''
        logging.debug(f'filter Result: {res}')
        return res

class prec23(ExpressionElement):
    @property
    def value(self):
        """
        ! prec23 class operations returns bool value.
        ! If prec23 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec23 class performs operation IF..THEN..ELSE.

        RETURN
        ret (variable type): previous level object if no prec23 operations are not presented in constraint
                            operation result in opposite case.
        """

        logging.debug("Level 23 IF THEN ELSE statement.")

        # Perform IF expression check.
        statement = self.op[1].parse(self.mapping_md, self.constr_md)
        print(f'IF ELSE STATEMENT {statement}')
        # If 'IF' expression was true, ther perform THEN expression.
        if statement is True:
            self.get_value(self.op[2].parse(self.mapping_md, self.constr_md))
        # If not, then perform ELSE expression if it exist. In the opposite case, do nothing.
        elif statement is False and len(self.op) > 3:
            self.get_value(self.op[3].parse(self.mapping_md, self.constr_md))
        return statement


class prec22(ExpressionElement):
    @property
    def value(self):
        """
        ! prec22 class operations returns bool value.
        ! If prec22 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec22 class performs operation IFF.

        RETURN
        ret (variable type): previous level object if no prec22 operations are not presented in constraint
                            operation result in opposite case.
        """

        logging.debug("Level 22 boolean IFF operation")

        left, operation, right = self.boolify(self.op[0].parse(self.mapping_md, self.constr_md)), self.op[1], self.boolify(self.op[2].parse(self.mapping_md, self.constr_md))
        ret = left == right

        self.check_exception(ret, f'Expression ({left} {operation} {right})')
        return ret

class prec21(ExpressionElement):
    @property
    def value(self):
        """
        ! prec21 class operations returns bool value.
        ! If prec21 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec21 class performs operation IMPLIES.

        RETURN
        ret (variable type): previous level object if no prec21 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug("Level 21 boolean IMPLIES operation")

        left, operation, right = self.boolify(self.op[0].parse(self.mapping_md, self.constr_md)), self.op[1], self.boolify(self.op[2].parse(self.mapping_md, self.constr_md))
        ret = not left or right

        self.check_exception(ret, f'Expression ({left} {operation} {right})')
        return ret

class prec20(ExpressionElement):
    @property
    def value(self):
        """
        ! prec20 class operations returns bool value.
        ! If prec20 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec20 class performs operation OR.

        RETURN
        ret (variable type): previous level object if no prec20 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug("Level 20 boolean OR operation")

        left = self.boolify(self.op[0].parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.boolify(r.parse(self.mapping_md, self.constr_md))
            ret = left or right
            self.check_exception(ret, f'Expression ({left} {operation} {right})')
            left = ret
        return ret

class prec19(ExpressionElement):
    @property
    def value(self):
        """
        ! prec19 class operations returns bool value.
        ! If prec19 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec19 class performs operation XOR.

        RETURN
        ret (variable type): previous level object if no prec19 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug("Level 19 boolean XOR operation")

        left = self.boolify(self.op[0].parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.boolify(r.parse(self.mapping_md, self.constr_md))
            ret = bool(left) ^ bool(right)
            self.check_exception(ret, f'Expression ({left} {operation} {right})')
            left = ret
        return ret

class prec18(ExpressionElement):
    @property
    def value(self):
        """
        ! prec18 class operations returns bool value.
        ! If prec18 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec18 class performs operation AND.

        RETURN
        ret (variable type): previous level object if no prec18 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug("Level 18 boolean AND operation")

        left = self.boolify(self.op[0].parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.boolify(r.parse(self.mapping_md, self.constr_md))
            logging.info(f"Level 18 boolean {left} {operation} {right} operation")
            ret = left and right
            self.check_exception(ret, f'Expression ({left} {operation} {right})')
            left = ret
        return ret

class prec17(ExpressionElement):
    @property
    def value(self):
        # TODO Fullfull functionality or remove this class.
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'U' or operation == 'untill':
                pass
        return ret

class prec16(ExpressionElement):
    @property
    def value(self):
        # TODO Fullfull functionality or remove this class.
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'W' or operation == 'weakuntill':
                pass
        return ret

class prec15(ExpressionElement):
    @property
    def value(self):
        # TODO Fullfull functionality or remove this class.
        ret = self.op[0].value
        if ret == 'F' or ret == 'eventually':
            pass
        elif ret == 'G' or ret == 'globally':
            pass
        elif ret == 'X' or ret == 'next':
            pass
        return ret

class prec14(ExpressionElement):
    @property
    def value(self):
        """
        ! prec14 class operations returns bool value.
        ! If prec14 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec14 class performs operation NOT.

        RETURN
        ret (variable type): previous level object if no prec14 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug("Level 14 boolean NO operation")

        operation, right = self.op[0], self.boolify(self.op[1].parse(self.mapping_md, self.constr_md))
        ret = not(right)

        self.check_exception(ret, f'Expression ({operation} {right})')
        return ret

class prec13(ExpressionElement):
    @property
    def value(self):
        """
        ! prec13 class operations returns bool value.
        ! If prec13 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec13 class performs quantification operations.
        These operations are used to perform prec12 operations with variables with fcard > 1.
        For example,
        a -> integer
        [fcard.a = 3]
        [one a > 2]
        means that exactly one from comparison operations [a0 > 2], [a1 > 2], [a2 > 2] should return True.

        RETURN
        ret (variable type): previous level object if no prec13 operations are not presented in constraint
                            operation result in opposite case.
        """
        self.exception_flag = False
        ret = False
        mapping_iter = self.get_wfml_data('Iterable.Mapping.Current')
        mapping_iter_sum = self.get_wfml_data('Iterable.Mapping.Total')
        if mapping_iter == 0:
            mapping_current = []
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            # Take exception flag if it was still not taken.
            if self.get_wfml_data('Flags.Exception') is False:
                logging.debug("Level 13 Exception flag.")
                self.update_wfml_data('Flags.Exception', True)
                self.exception_flag = True
            operand.value

            # Perform comparison operation to all mappings.
            if mapping_iter < mapping_iter_sum and len(self.op) > 1:
                mapping_current.append(self.op[1].value)
                logging.debug(f'Mapping Current append {self.op[1].value} mapping iter {mapping_iter}')

            # Count number of True results and perform quantification operation.
            if mapping_iter == mapping_iter_sum - 1 and len(self.op) > 1:
                number = mapping_current.count(True)
                logging.debug(f'Check Operation {operation}. Values {mapping_current}')

                if operation == 'no' or operation == 'none':
                    if number == 0:
                        ret = True

                elif operation == 'lone':
                    if number >= 1:
                        ret = True

                elif operation == 'one':
                    if number == 1:
                        ret = True

                elif operation == 'some':
                    if number > 1:
                        ret = True

                # Raise exception if result is False and exception flag was taken by this operation.
                if ret is False and self.exception_flag is True:
                    raise Exception(f'Expression operation {operation} {mapping_current} was not satisfied.')

        # Release exception flag.
        if self.exception_flag is True:
            self.update_wfml_data('Flags.Exception', False)

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret


class prec12(ExpressionElement):
    @property
    def value(self):
        """
        ! prec12 class operations returns bool value.
        ! If prec12 class operations are not part of higher-level operations,
        then exception will be raised if operation result is False.

        prec12 class performs comparison operations.

        RETURN
        ret (variable type): previous level object if no prec12 operations are not presented in constraint
                            operation result in opposite case.
        """
        for l, op, r in zip(self.res[0::2], self.res[1::2], self.res[2::2]):
            left, operation, right = self.get_value(l), op, self.get_value(r)
            left, right = [self.get_value(feature) for feature in [left, right]]
            logging.info(f'Level 12 comparison {left} {operation} {right} operation')
            if operation == '<':
                ret = left < right
            elif operation == '>':
                ret = left > right
            elif operation == '==':
                ret = left == right
            elif operation == '>=':
                ret = left >= right
            elif operation == '<=':
                ret = left <= right
            elif operation == '!=':
                ret = left != right
            elif operation == 'in':
                ret = left in right
            elif operation == 'not in':
                ret = left not in right
            self.check_exception(ret, f'Expression ({left} {operation} {list(right.keys()) if isinstance(right, dict) else right})')
        return ret

    def check_cardinalities(self):
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.check_cardinalities()

class prec11(ExpressionElement):
    @property
    def value(self):
        """
        prec11 class performs requires and excludes operations.

        RETURN
        ret (variable type): previous level object if no prec11 operations are not presented in constraint
                            operation result in opposite case.
        """
        left, operation, right = self.boolify(self.res[0]), self.res[1], self.boolify(self.res[2])
        if operation == 'requires':
            ret = not left or (left and right)
            print(f'REQUIRES CHECK {left} | {right} | {ret}')
            self.check_exception(ret, 'Required feature does not exist')
        elif operation == 'excludes':
            ret = not (left and right)
            print(f'EXCLUDES CHECK {left} | {right} | {ret}')
            self.check_exception(ret, 'One of the features under excludes constraint should not exist')
        return ret

class prec10(ExpressionElement):
    @property
    def value(self):
        """
        prec10 class performs assignment operation.

        RETURN
        ret (variable type): previous level object if no prec10 operations are not presented in constraint
                            operation result in opposite case.
        """

        fname = self.get_value(self.res[0], 'Fname')
        field = self.get_value(self.res[0], 'Ftype')
        value = self.get_value(self.res[2])

        self.api.update_metadata(fname, field, value)

        return True


class prec9(ExpressionElement):
    @property
    def value(self):
        """
        prec9 class performs addition and subtraction operations.

        RETURN
        ret (variable type): previous level object if no prec9 operations are not presented in constraint
                            operation result in opposite case.
        """
        ret = self.get_value(self.op[0].parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, r.parse(self.mapping_md, self.constr_md)
            right = self.get_value(right)
            logging.info(f'Level 9 Math operation {ret} {operation} {right} ')
            if operation == '+':
                ret += right
            elif operation == '-':
                ret -= right
        return ret


class prec8(ExpressionElement):
    @property
    def value(self):
        """
        prec8 class performs miltiplication, division and remainer operations.

        RETURN
        ret (variable type): previous level object if no prec8 operations are not presented in constraint
                            operation result in opposite case.
        """
        ret = self.get_value(self.op[0].parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.get_value(r.parse(self.mapping_md, self.constr_md))
            logging.info(f'Level 8 Math operation {ret} {operation} {right} ')
            if operation == '*':
                ret *= right
            elif operation == '/':
                ret /= right
            elif operation == '%':
                ret %= right
        return ret


class prec7(ExpressionElement):
    @property
    def value(self):
        """
        prec7 class performs min and max operations.

        RETURN
        ret (variable type): previous level object if no prec7 operations are not presented in constraint
                            operation result in opposite case.
        """
        # TODO debug checks for list type
        operation, right = self.op[0], self.get_value(self.op[1].parse(self.mapping_md, self.constr_md))
        if operation == 'min':
            logging.debug(f"Level 8 min operation")
            ret = min(right)

        elif operation == 'max':
            logging.debug(f"Level 8 max operation")
            ret = max(right)

        elif operation == 'size':
            logging.debug(f"Level 8 size operation")
            ret = len(right)
        return ret


class prec6(ExpressionElement):
    @property
    def value(self):
        """
        prec6 class performs sum, product and count operations.

        RETURN
        ret (variable type): previous level object if no prec6 operations are not presented in constraint
                            operation result in opposite case.
        """
        # TODO debug checks for list type
        operation, right = self.op[0], self.get_value(self.op[1].parse(self.mapping_md, self.constr_md))
        if operation == 'sum':
            logging.debug(f"Level 7 sum operation: {operation}")
            ret = sum(right)

        elif operation == 'product':
            logging.debug(f"Level 7 product operation: {operation}")
            ret = reduce((lambda x, y: x * y), right)

        elif operation == '#':
            logging.debug(f"Level 7 count operation: {operation}")
            ret = len(right)
        return ret


class prec50(ExpressionElement):
    @property
    def value(self):
        """
        prec50 class performs unique x in y operation.

        RETURN
        ret (variable type): previous level object if no prec50 operations are not presented in constraint
                            operation result in opposite case.
        """
        self.api.keyword = 'AllFeatures'
        print('------------------------------')
        for index, part in enumerate(self.op):
            try:
                print(f'Part {index}: {part.parse(self.mapping_md, self.constr_md)}')
            except AttributeError:
                print(f'Part {index}: {part} is a {type(part)}')
        right = self.get_value(self.op[2].parse(self.mapping_md, self.constr_md))
        self.api.keyword = ''
        left = self.get_value(self.op[1].parse(self.mapping_md, self.constr_md))
        logging.debug(f'Level 5.0 Operation unique x in y.')
        ret = self.find_unique(right, left)

        return ret

    def find_unique(self, input, key, res=None):
        """
        Function to find all unique elements in list (no repeats).

        INPUTS
        input (type = dict): feature's namespace.
        key (type = dict): keyword to filter.

        RETURN
        res (type = list): list of filtered features.
        """
        if res is None:
            res = []
        for feature, namespace in input.items():
            if feature.split('.')[-1] == key:
                if namespace['Value'] is not None and namespace['Value'] not in res:
                    res.append(namespace['Value'])
        return res


class prec5(ExpressionElement):
    @property
    def value(self):
        # TODO prec5 - domain operation
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<:':
                pass
        return ret


class prec4(ExpressionElement):
    @property
    def value(self):
        # TODO prec4 - range operation
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == ':>':
                pass
        return ret


class prec3(ExpressionElement):
    @property
    def value(self):
        """
        prec3 class performs lists union operation.

        RETURN
        ret (variable type): previous level object if no prec3 operation is not presented in constraint
                            merged lists in opposite case.
        """
        left, operation, right = self.get_value(self.op[0].parse(self.mapping_md, self.constr_md)), self.op[1], self.get_value(self.op[2].parse(self.mapping_md, self.constr_md))

        # Perform list union if such operation exist.
        if operation == ',' or operation == '++':
            if type(left) == list and type(right) == list:
                ret = list(set(left) | set(right))
            elif type(left) != list:
                raise Exception(f'Parameter {left} is not list.')
            elif type(right) != list:
                raise Exception(f'Parameter {right} is not list.')
        return ret


class prec2(ExpressionElement):
    @property
    def value(self):
        """
        prec2 class performs lists difference operation.

        RETURN
        ret (variable type): previous level object if no prec2 operation is not presented in constraint
                            merged lists in opposite case.
        """
        left, operation, right = self.get_value(self.op[0].parse(self.mapping_md, self.constr_md)), self.op[1], self.get_value(self.op[2].parse(self.mapping_md, self.constr_md))

        # Perform list difference if such operation exist.
        if operation == '--' and type(left) == list and type(right) == list:
            ret = list(set(left) - set(right))
        elif operation == '--' and type(left) != list:
            raise Exception(f'Parameter {left} is not list.')
        elif operation == '--' and type(right) != list:
            raise Exception(f'Parameter {right} is not list.')
        return ret


class prec1(ExpressionElement):
    @property
    def value(self):
        """
        prec1 class performs lists merging operations.

        RETURN
        ret (variable type): previous level object if no prec1 operations are not presented in constraint
                            merged lists in opposite case.
        """
        # TODO Rethink prec1 and prec0 classes as their functionality is duplicated.
        left, operation, right = self.get_value(self.op[0].parse(self.mapping_md, self.constr_md)), self.op[1], self.get_value(self.op[2].parse(self.mapping_md, self.constr_md))

        # Perform list merge (without duplicates) if such operation exist.
        if operation == '**' and type(left) == list and type(right) == list:
            ret = list(set(left) & set(right))
        elif operation == '**' and type(left) != list:
            raise Exception(f'Parameter {left} is not list.')
        elif operation == '**' and type(right) != list:
            raise Exception(f'Parameter {right} is not list.')

        return ret


class prec0(ExpressionElement):
    @property
    def value(self):
        """
        prec0 class performs lists concatenation ('..') and merging ('&') operations.

        RETURN
        op (variable type): term object if no prec0 operations are not presented in constraint
                            concatenated/merged lists in opposite case.
        """
        left, operation, right = self.get_value(self.op[0].parse(self.mapping_md, self.constr_md)), self.op[1], self.get_value(self.op[2].parse(self.mapping_md, self.constr_md))

        # Perform list concatenation (with duplicates) if such operation exist.
        if operation == '..' and type(left) == list and type(right) == list:
            ret = left + right
        elif operation == '..' and type(left) != list:
            raise Exception(f'Parameter {left} is not list.')
        elif operation == '..' and type(right) != list:
            raise Exception(f'Parameter {right} is not list.')

        # Perform list merge (without duplicates) if such operation exist.
        if operation == '&' and type(left) == list and type(right) == list:
            ret = list(set(left) & set(right))
        elif operation == '&' and type(left) != list:
            raise Exception(f'Parameter {left} is not list.')
        elif operation == '&' and type(right) != list:
            raise Exception(f'Parameter {right} is not list.')
        return ret


class term(ExpressionElement):
    @property
    def value(self):
        """
        Function to check type of op value (variable, number, string, etc.) and return it.

        RETURN
        op (variable type): variable, number, string, etc.
        """
        op = self.op
        if isinstance(op, ExpressionElement):
            logging.debug(f"Operation object: {op} with value {type(op)}")
            res = self.get_value(op.parse(self.mapping_md, self.constr_md))
            return self.get_value(op.parse(self.mapping_md, self.constr_md))
        elif isinstance(op, str) and op not in keywords:
            is_list = True if any(op.startswith(x[0]) and op.endswith(x[1]) for x in [('[', ']'), ('{', '}')]) else False

            repl = ['[', ']', '{', '}', "'", '"', ' ']
            for pattern in repl:
                op = op.replace(pattern, '')
            res = [self.autoconvert(x) for x in op.split(',')] if is_list is True else self.autoconvert(op)

        else:
            res = op

        return res

    def parse(self, mapping_md, constr_md):
        self.mapping_md = mapping_md
        self.constr_md = constr_md
        if (obj_id:=id(self)) in constr_md['Features'].keys():
            obj_md = constr_md['Features'][obj_id]
            fname = mapping_md['Current'][(orig:=list(obj_md.keys())[0])]
            ftype = list(obj_md.values())[0]
            ret = self.api.read_metadata(fname)['__self__']
            ret.update({'GFcard': len(set(itertools.chain.from_iterable([sub[orig]] for sub in mapping_md['All']))),
                         'Fname': fname,
                         'Ftype': ftype,
                         'IsFeature': True})
            if mapping_md['ExceptionFlag'] is False:
                self.exception, mapping_md['ExceptionFlag'] = True, True
                self.check_exception(self.boolify(ret), f'Expression {fname}')
        else:
            ret = {'IsFeature': False,
                   'Value': self.value}

        return ret

    def boolify_str(self, string):
        if string == 'True':
            return True
        if string == 'False':
            return False
        raise ValueError('String value is not Boolean.')

    def autoconvert(self, string):
        for fn in (self.boolify_str, int, float):
            try:
                return fn(string)
            except ValueError:
                pass
        return string


class Waffle:
    def __init__(self) -> None:
        self.reset()
    
    def reset(self):
        self.prec_bool = ['prec23', 'prec22', 'prec21', 'prec20', 'prec19', 'prec18', 'prec14', 'prec11', 'prec0', 'term']
        self.metamodel, self.stage_snap, self.last_snap = {}, {}, {}
        self.exception_flag = False
        self.initial_fcards, self.groups = {}, {}
        self.inheritance = []
        self.metagraph = []
        self.features_to_configure = {}
        self.id_counter = 0
        self.card_boundaries = {
            '*': [(0, 1e6)],
            '+': [(1, 1e6)],
            '?': [(0, 1)],
            'or': [(1, 1e6)],
            'xor': [(1, 1)]
        }
        self.constraints = {}
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
            'Requires': {
                'Fcard': [],
                'Gcard': [],
                'Value': []
            },
            'Mappings': {},
            'ParentFeature': '',
            'isValidated': False,
            'Expression': '',
            'Precedence': {},
            'Features': {},
            'FeaturesPrec': {}
        }

    def initialize_feature(self, name, fcard, gcard, value, abstract, inheritance, attribute, constraints):
        mm = self.metamodel
        self.test_graph = []
        for level in name.split('.'):
            if level not in mm.keys():
                mm.update({level: {'__self__': {
                        'DeactStandard': False,
                        'ActiveF': True,
                        'ActiveG': True,
                        'Active': True ,
                        'Fcard': 1,
                        'Gcard': 'all',
                        'Value': None,
                        'Abstract': None,
                        'Inheritance': None,
                        'Attribute': None,
                        'Constraints': None
                        }}})
            mm = mm[level]
            
        mm.update({'__self__': {
                        'DeactStandard': False,
                        'ActiveF': True if fcard != 0 else False,
                        'ActiveG': True,
                        'Active': True if fcard != 0 else False,
                        'Fcard': fcard if fcard is not None else 1,
                        'Gcard': gcard if gcard is not None else 'all',
                        'Value': value,
                        'Abstract': abstract,
                        'Inheritance': inheritance.replace(':', '') if inheritance is not None else None,
                        'Attribute': attribute.replace('->', '') if attribute is not None else None,
                        'Constraints': None
                        }})

        if inheritance is not None:
            self.inheritance.append((name, mm['__self__']['Inheritance']))

        self.initial_fcards.update({name: {
            'MM': mm,
            'Value': fcard
        }})

    def get_original(self, feature):
        return re.sub(r'\_\d+', '', feature)
    
    def get_tlf(self, feature):
        return feature.split('.')[0]
    
    def feature_is_active(self, name):
        mm = self.metamodel
        for level in name.split('.'):
            mm = mm[level]
            if mm['__self__']['Active'] is False:
                return False
        return True

    def define_inheritance(self):
        seq, _ = self.topo_sort(self.inheritance, rev=True)
        print('-----------------------')
        for feature in seq:
            md = self.read_metadata(feature)
            if (super_feature:=md['__self__']['Inheritance']) is not None:
                md_copy = copy.deepcopy(self.read_metadata(super_feature))
                constr_copy = md_copy['__self__']['Constraints']
                
                del md_copy['__self__']
                md.update(md_copy)
                for constr in constr_copy:
                    print(f'{feature} | {constr} | {md['__self__']['Constraints']}')
                    if md['__self__']['Constraints'] is None:
                        md['__self__']['Constraints'] = []
                    if constr not in md['__self__']['Constraints']:
                        print(self.constraints.keys())
                        constr_md = self.constraints[constr]
                        md['__self__']['Constraints'].append(self.parse_constraint(constr_md['Object'], feature)['ID'])

    def update_metadata(self, name, field, value):
        print(f'Updating field {field} for feature {name} with value {value}')
        md = self.read_metadata(name)
        if field == 'Value' and 'Array' in (attr_type:=md['__self__']['Attribute']):
            try:
                value = value.replace(' ','').split(',')
                if attr_type == 'floatArray':
                    for v in value:
                        v = float(v)
                elif attr_type == 'integerArray':
                    for v in value:
                        v = int(v)
            except Exception as e:
                return e
        md['__self__'][field] = value
        if field == 'Inheritance':
            self.inheritance.append((name, value))
        elif field == 'Fcard':
            if self.check_card_value(name, value, field) == (True, ''):
                self.handle_fcards(name, md, value)
        elif field == 'Gcard':
            if self.check_card_value(name, value, field) == (True, ''):
                self.handle_gcards(name, md, value)
    
    def is_card_defined(self, value):
        return False if (value in ['*', '+', '?', 'xor', 'or'] or 
            (isinstance(value, str) and (len(value.split(',')) > 1 or len(value.split('..')) > 1))) else True
    
    def check_card_value(self, name, value, card_type):
        md = self.read_metadata(name)
        error_msg = ''
        old_value = md['__self__'][card_type]

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
                error_msg = f'Wrong cardinality value ({value_to_check}), must be in range {card_boundaries}'
        else:
            res = True

        return res, error_msg

    def check_card_in_constraints(self, value, card_type, name):
        for constraint in self.constraints.values():
            constr_md = constraint['Metadata']
            check = self.get_feature_mappings(constr_md['ParentFeature'], self.metamodel)
            if check != []:
                for assign_type in ['Assign', 'Read']:
                    for feature_type in ['Fcard', 'Gcard', 'Value']:
                        if not (assign_type == 'Assign' and feature_type == 'Fcard'):
                            for feature in constr_md[assign_type][feature_type]:
                                check1 = self.get_feature_mappings(feature, self.metamodel)
                                if feature in constr_md['FeaturesPrec'].keys():
                                    if check1 == [] and any([x not in self.prec_bool and not (x == 'prec12' and feature_type == 'Fcard') for x in constr_md['FeaturesPrec'][feature]]):
                                        raise Exception(f'{card_type} cardinality value {value} for feature {name} leads to inability to validate constraint {constr_md['Expression']}', name)

    def handle_fcards(self, name, md, repeats):
        repeats = md['__self__']['Fcard']
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
                    v['__self__']['ActiveF'] = False if len(index) > 1 and ((index[1].isdigit() and int(index[1]) >= repeats) or repeats == 1) else True
                    self.update_active_state(k if tlf is True else f'{pname}.{k}')
        md['__self__']['ActiveF'] = False if (repeats != 1 and not isinstance(repeats, str)) else True
        md['__self__']['DeactStandard'] = True if (not isinstance(repeats, str) and repeats >= 1) else False

        self.update_active_state(name)
        return self.check_card_in_constraints(repeats, 'Feature', name)

    def get_constraint_mappings(self, constraint):
       
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
                        if (ftr:='.'.join(split[:index + 1])) not in features_arr:
                            features_arr.append(ftr)

                features[keyword].extend(features_arr)
        features['Fcard'].append(constraint['Metadata']['ParentFeature'])     
   
        features_to_configure = []
        for tlf in self.metamodel.keys():
            features_to_configure.append(self.get_undefined_features(tlf, all_features=True))
        for k, v in features.items():
            for feature in set(v):
                if feature in constraint['Metadata']['FeaturesPrec'].keys():
                    filter = False if any([x in self.prec_bool for x in constraint['Metadata']['FeaturesPrec'][feature]]) or feature in constraint['Metadata']['Read']['Fcard'] else True
                else:
                    filter = True
                if feature not in all_mappings.keys():
                    all_mappings.update({feature: []})
                full_mapps = self.get_feature_mappings(feature, self.metamodel, filter)
                if filter is False:
                    for mapps in full_mapps:
                        for i, _ in enumerate(mapps_spl:=mapps.split('.')):
                            mapps_compose = '.'.join(mapps_spl[:i + 1])
                            if (mapps_orig:=self.get_original(mapps_compose)) not in all_mappings.keys():
                                all_mappings.update({mapps_orig: []})
                            if mapps_compose not in all_mappings[mapps_orig]:
                                all_mappings[mapps_orig].append(mapps_compose)
                for mapps in full_mapps:
                    if mapps not in all_mappings[feature]:
                        all_mappings[feature].append(mapps)
                flat_mappings[k].extend(full_mapps)
        all_mappings_list = list(all_mappings.values())
        for part in all_mappings_list:
            part = list(set(part))
        combinations = itertools.product(*all_mappings_list)
        filtered_combinations = self.filter_combinations(combinations)

        for comb in filtered_combinations:
            if str(comb) not in constraint['Metadata']['Mappings'].keys():
                subres = {}
                for feature in comb:
                    subres.update({self.get_original(feature): feature})
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
                        if x in tlf_features_to_configure[kw] and self.get_original(x) not in constraint['Metadata']['Assign']['Fcard']:
                            matched_features.append(x)
        print(f'MATCHED FEATURES: {matched_features} | {tlf_features_to_configure}')
        for mapping in constraint['Metadata']['Mappings'].values():
            mapping['Active'] = False if any([mf in mapping['Comb'].values() for mf in matched_features]) else True              
    
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
    
    def get_feature_childrens(self, feature, full_tree=False):
        md = self.read_metadata(feature)
        res = []
        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True:
                if full_tree is True:
                    res.extend(self.get_feature_childrens(f'{feature}.{k}', True))
                res.append(f'{feature}.{k}')
        return res
                
    def get_feature_mappings(self, feature, md, filter=True, layer=0, fname=''):
        res = []
        name_split = feature.split('.') if not isinstance(feature, list) else feature
        for k, v in md.items():
            if k != '__self__' and (v['__self__']['Active'] is True or 
                                    (filter is False and v['__self__']['DeactStandard'] is False)) and self.get_original(name_split[layer]) == self.get_original(k):
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
            return self.check_card_in_constraints(value, 'Group', name)

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
        md['Active'] = md['ActiveF'] and md['ActiveG'] if md['Abstract'] is None else False

    def get_product(self, md, res):
        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True:
                self_value = {} if v['__self__']['Value'] is None else v['__self__']['Value']
                res.update({k: self_value})
                if len(v.values()) > 1:
                    res.update({k: self.get_product(v, res[k])})
        return res
    
    def get_undefined_features(self, tlf, md=None, layer=0, pname='', all_features=False):
        res = {
            'Fcard': [],
            'Gcard': [],
            'Value': []
        }
        md = self.metamodel if md is None else md
        
        for k, v in md.items():
            if k != '__self__' and v['__self__']['Active'] is True and(layer > 0 or tlf in k):
                feature_md = v['__self__']
                fname = f'{pname}.{k}' if layer >= 1 else k
                skip = False
                if not self.is_card_defined(feature_md['Fcard']):
                    res['Fcard'].append(fname)
                    skip = True
                if not self.is_card_defined(feature_md['Gcard']) and (fname not in res['Fcard'] or all_features is True):
                    res['Gcard'].append(fname)
                    skip = True
                if (feature_md['Attribute'] not in [None, 'predefined'] and feature_md['Value'] is None) and (fname not in res['Fcard'] or all_features is True):
                    res['Value'].append(fname)
                    skip = True

                if len(v.values()) > 1 and (not skip or all_features):
                    subres = self.get_undefined_features(tlf, v, layer + 1, fname, all_features)
                    for md_type in res.keys():
                        res[md_type].extend(subres[md_type])
        print(f'Undefined features: {res}')
        return res

    def validate_constraints(self, step):
        main = True
        if main:
            print(f'STEP: {step}')
            for index in range(self.seq.index(step) + 1, len(self.seq)):
                if ((elem:=self.seq[index]).startswith('Constraint_')):
                    for constraint in self.constraints.values():
                        if constraint['ID'] == elem:
                            constr_md = constraint['Metadata']
                            print(f'Evaluating constraint {constr_md['Expression']}')
                            self.get_constraint_mappings(constraint)
                            pprint.pprint(constr_md)
                            if self.debug_mode is False:

                                try:
                                    constraint['Object'].name.parse_constraint(constr_md)
                                except Exception as e:
                                    return e
                            else:
                                constraint['Object'].name.parse_constraint(constr_md)
                            break
                else:
                    break
        else:
            for constraint in self.constraints.values():
                
                constr_md = constraint['Metadata']
                print(f'Evaluating constraint {constr_md['Expression']}')
                self.get_constraint_mappings(constraint)
                if self.debug_mode is False:

                    try:
                        constraint['Object'].name.parse_constraint(constr_md)
                    except Exception as e:
                        return e
                else:
                    constraint['Object'].name.parse_constraint(constr_md)
        return True
    
    def cname(self, obj):
        """
        Function to return class name of object.

        INPUTS
        obj: object to check.

        RETURN
        (type = string): object`s class name.
        """
        return obj.__class__.__name__

    def parse_feature(self, feature, parent_name=None, parse_type='Feature', abstract=False):
        """
        ! This method is recursive.

        Function to define features.

        INPUTS
        feature (type = feature): feature to define.
        parent_namespace (type = dict): parent feature namespace to fullfill.

        RETURN
        parent_namespace (type = dict): fullfilled parent namespace. Only for not top-level features.
        """
        feature_name = feature.name if parent_name is None else f'{parent_name}.{feature.name}'
        if abstract is False:
            abstract = True if feature.abstract is not None else False
        constraints = []
        for child_obj in feature.nested:
            for children in child_obj.child:
                if self.cname(children) == 'Feature':
                    self.parse_feature(children, feature_name, parse_type, abstract)
                elif self.cname(children) == 'Constraint' and parse_type == 'Constraint':
                    constraints.append(self.parse_constraint(children, feature_name)['ID'])
        if parse_type == 'Feature':
            if feature.super is not None and feature.reference is not None:
                raise Exception(f'Super feature and Reference feature could not appear at the same time for {feature_name}')
            if feature_name == 'Context' and feature.fcard not in [None, 1]:
                raise Exception(f'Context feature is not allowed to have cartinality value other than 1')
            self.initialize_feature(name=feature_name,
                                    fcard=feature.fcard,
                                    gcard=feature.gcard,
                                    value=feature.init,
                                    abstract=feature.abstract,
                                    inheritance=feature.super,
                                    attribute=feature.type,
                                    constraints=None)
        elif parse_type == 'Constraint' and constraints != []:
            self.update_metadata(feature_name, 'Constraints', constraints)

    def parse_constraint(self, constraint, parent_feature):
        """
        Function to define constraints in dict format.

        INPUTS
        constraint (type = textX generated class): constraint's object.
        related_feature (type = string): full name of the feature to which this constraint belongs.

        """
        self.pattern = copy.deepcopy(self.constraint_pattern)
        self.pattern.update({'ParentFeature': parent_feature})
        self.pattern.update({'Expression': self.get_constraint_position(constraint)})
        self.is_term = True
        self.parse_constraint_helper(constraint.name, parent_feature)
        constraint.name.connect_waffle(self)
        constraint = {
            'Object': constraint,
            'Metadata': copy.deepcopy(self.pattern),
            'ID': f'Constraint_{self.id_counter}'
        }

        self.constraints.update({f'Constraint_{self.id_counter}': constraint})
        self.id_counter += 1
        return constraint

    def get_constraint_position(self, constraint):
        start_pos = get_location(constraint)
        end_pos = start_pos['col'] + constraint._tx_position_end - constraint._tx_position
        line = self.description.splitlines()[start_pos['line'] - 1]
        return line[start_pos['col'] - 1 : end_pos - 1]

    def parse_constraint_helper(self, constraint, parent_feature):
        cname = constraint.__class__.__name__
        self.last_elem_id = 0
        
        if isinstance(constraint, ExpressionElement):
            if isinstance(constraint.op, list):
                res = {}
                if len(elements:=constraint.op) > 1:
                    self.is_term = False

                for index, op in enumerate(elements):
                    subres = self.parse_constraint_helper(op, parent_feature)
                    
                    if isinstance(subres, str) and len(elements) >= 1 and subres not in keywords:
                        fname, card_keyword, is_feature = self.parse_feature_name(subres, parent_feature)
                        
                        if is_feature is True:
                            
                            if card_keyword in ['fcard', 'gcard']:
                                ftype = card_keyword.capitalize()
                            else:
                                ftype = 'Value'
                            
                            subres = {fname: ftype}
                            self.pattern['Features'].update({self.last_elem_id: subres})
                            if self.is_term is True:
                                subres[fname] = 'Fcard'
                                res.update({index: subres})
                                res.update({'Class': cname})
                                self.pattern['FeaturesPrec'].update({fname: ['term']})
                                self.pattern['Precedence'].update({id(constraint): res})
                    res.update({index: subres})
                if len(elements) > 1:
                    res.update({'Class': cname})
                    for md in res.values():
                        if isinstance(md, dict):
                            for fname in md.keys():
                                if fname not in self.pattern['FeaturesPrec'].keys():
                                    self.pattern['FeaturesPrec'].update({fname: [cname]})
                                else:
                                    self.pattern['FeaturesPrec'][fname].append(cname)
                                if cname in self.prec_bool:
                                    md[fname] = 'Fcard'
                    self.pattern['Precedence'].update({id(constraint): res})
                return id(constraint) if len(elements) > 1 else subres
            else:
                self.last_elem_id = id(constraint)
                return constraint.op
        else:
            return constraint

    def parse_feature_name(self, name, parent_feature):
        if '\'' in name or '\"' in name:
            return name, False, False
        indices = {
            'self': [],
            'parent': [],
            'fcard': [],
            'gcard': [],
            'gfcard': []
        }
        feature_indices = []
        for index, part in enumerate(split:=name.split('.')):
            if part in indices.keys():
                indices[part].append(index)
            else:
                feature_indices.append(index)
        for k, v in indices.items():
            if repeats:=len(v) > 1 and k != 'parent':
                print(f'Keyword {self} appears {repeats} times.')
            
        if len(indices['self']) > 1 and len(indices['parent']) > 1:
            print('Keywords "self" and "parent" can not appear at the same time.')
        
        if len(indices['fcard'] + indices['gcard'] + indices['gfcard']) > 1:
            print('Keywords "fcard", "gcard", and "gfcard" can not appear at the same time.')
        
        card_keyword = None
        for keyword in ['fcard', 'gcard', 'gfcard']:
            if len(indices[keyword]) > 0 and indices[keyword][0] != 0:
                print(f'Wrong position of keyword! {keyword}.')
            elif len(indices[keyword]) > 0:
                card_keyword = keyword
        rel_keyword = None
        for keyword in ['self', 'parent']:
            if len(indices[keyword]) > 0:
                if not(indices[keyword][0] == 0 or (indices[keyword][0] == 1 and card_keyword is not None)):
                    print(f'Wrong position of keyword!! {keyword}.')
                rel_keyword = (keyword, len(indices[keyword]))
            
            if len(feature_indices) > 0:
                for pos in indices[keyword]:
                    if pos > feature_indices[0]:
                        print(f'Wrong position of keyword!!! {keyword}.')
        skip_chars_card = 1 if card_keyword is not None else 0
        skip_chars_rel = rel_keyword[1] if rel_keyword is not None  else 0

        par_split = parent_feature.split('.')
        repl_chars_res = par_split[:len(par_split) - (rel_keyword[1] if rel_keyword is not None and rel_keyword[0] == 'parent' else 0)]
        self_name = '.'.join(repl_chars_res + split[skip_chars_card + skip_chars_rel:])
        full_name = '.'.join(split[skip_chars_card + skip_chars_rel:])
        for check in [self_name, full_name, name]:
            try:
                self.read_metadata(check)
                is_feature = True
                res = check
                break
            except KeyError:
                res = name
                is_feature = False
                # TODO proper logging
                # print(f'{name} | {full_name} | {self_name} is not a correct feature | {par_split} | {repl_chars_res}')

        return res, card_keyword, is_feature
   
    def restore_stage_snap(self, step=None):
        """
        Function to restore stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.

        RETURN
        Stage snapshot.
        """
        
        self.metamodel = copy.deepcopy(self.stage_snap[step]['Metamodel'] if step is not None else self.last_snap['Metamodel'])
        constr_meta = copy.deepcopy(self.stage_snap[step]['Constraints'] if step is not None else self.last_snap['Constraints'])
        for k, v in constr_meta.items():
            self.constraints[k].update({'Metadata': v})
        print('===============!!!!!!!!!!!!!=============')
        print(f'STEP {step}')
        for k, v in self.stage_snap.items():
            print(f'STAGE {k}')
            for v1 in v['Constraints'].values():
                pprint.pprint(v1['Mappings'])

        if step is not None:
            rm_steps = []
            for snap_step in self.stage_snap.keys():
                if int(snap_step) >= int(step):
                    rm_steps.append(snap_step)
            for rm_step in rm_steps:
                del self.stage_snap[rm_step]
        logging.info(f"Namespace was restored due to {'unvalidated constraint' if step is None else 'going to previous step'}.")
        
    def save_stage_snap(self, step, data):
        """
        Function to read stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.
        data (type = dict): fields for this step
        """
        constr_meta = {}
        for k, v in self.constraints.items():
            constr_meta.update({k: v['Metadata']})
        self.last_snap = {
            'Metamodel': copy.deepcopy(self.metamodel),
            'Constraints': copy.deepcopy(constr_meta),
            'Fields': data
        }
        self.stage_snap.update({step: copy.deepcopy(self.last_snap)})

        
    
    def save_json(self):
        """
        Prepare and save final result.

        RETURN
        res (type = dict): final result
        """
        print('--------------------')
        pprint.pprint(self.metamodel)
        res = self.get_product(self.metamodel, {})
        pprint.pprint(res)
        logging.info('Final result was successfully created.')
        logging.debug(f'Final Model {res}')
        with open('./core/output/configuration.json', 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=4)

        # TODO: Pickling WFML for dynamicity
        # self.pickle_wfml_data()
        return res

    #merge function to  merge all sublist having common elements. 
    def merge_common(self, lists): 
        neigh = defaultdict(set) 
        visited = set() 
        for each in lists: 
            for item in each: 
                neigh[item].update(each) 
        def comp(node, neigh = neigh, visited = visited, vis = visited.add): 
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
    
    def build_feature_metagraph_deps(self, feature, parent=None):
        md = self.read_metadata(feature)
        self.metagraph.append((f'{feature}-Fcard', f'{feature}-{'Gcard' if md['__self__']['Attribute'] is None else 'Value'}'))
        if parent is not None:
            md_par = self.read_metadata(parent)
            self.metagraph.append((f'{parent}-{'Gcard' if md_par['__self__']['Attribute'] is None else 'Value'}', f'{feature}-Fcard'))
        for key in md.keys():
            if key != '__self__':
                self.build_feature_metagraph_deps(f'{feature}.{key}', feature)

    def build_metagraph(self):
        deps = []
        indep_constraints = []
        for tlf, md in self.metamodel.items():
            if md['__self__']['Abstract'] is None:
                self.build_feature_metagraph_deps(tlf)
        for constraint in self.constraints.values():
            par_feature = constraint['Metadata']['ParentFeature']
            if self.metamodel[par_feature.split('.')[0]]['__self__']['Abstract'] is None:
                flag = True
                for v in constraint['Metadata']['Precedence'].values():
                    for k1, v1 in v.items():
                        if isinstance(v1, dict):
                            assign_type = 'Assign' if k1 == 0 and v['Class'] == 'prec10' else 'Read'
                            for k2, v2 in v1.items():
                                constraint['Metadata'][assign_type][v2].append(k2)
                        
                        elif k1 == 1 and v['Class'] == 'prec50':    
                            a = self.get_feature_childrens(list(v[2].keys())[0], True)
                for k, v in constraint['Metadata']['Assign'].items():
                    for feature in v:
                        deps.append((f'{constraint['ID']}', f'{feature}-{k}'))
                        flag = FloatingPointError
                for k, v in constraint['Metadata']['Read'].items():
                    deps.extend([(f'{x}-{k}', f'{constraint['ID']}') for x in v])
                    deps.extend([(f'{constraint['Metadata']['ParentFeature']}-Fcard', f'{x}-{k}') for x in v])
                deps.append((f'{constraint['Metadata']['ParentFeature']}-Fcard', f'{constraint['ID']}'))
                if flag is True:
                    indep_constraints.append(constraint['ID'])

        for dep in list(set(deps)):
            self.metagraph.append(dep)
        
        flat_dict = {}
        elem_pattern = {
        'Before': [],
        'After': []
        }
        for dep in self.metagraph:
            for index, elem in enumerate(dep):
                if elem not in flat_dict.keys():
                    flat_dict.update({elem: copy.deepcopy(elem_pattern)})
                connection = 'Before' if index == 0 else 'After'
                flat_dict[elem][connection].append(dep[0 if connection == 'After' else 1])
        
        groups = []
        for k, v in flat_dict.items():
            if k.startswith('Constraint_'):
                group = v['After']
                group_filtered = []
                for elem in group:
                    include = True
                    for elem_alt in group:
                        if (a:=elem.split('-')[0]) in (b:=elem_alt.split('-')[0]) and a != b:
                            include = False
                    if include is True:
                        group_filtered.append(elem)
                groups.append(group_filtered)
        self.groups = {}
        for index, group in enumerate(list(self.merge_common(groups))):
            self.groups.update({f'Inner_Waffle_Group_{index}': group})
        
        new_deps = []
        rm_deps = []
        rm_deps_dict = {}
        for index, dep in enumerate(self.metagraph):
            temp_dict = {}
            upd_flag = False
            for index_alt, elem in enumerate(dep):
                
                for group_name, group in self.groups.items():
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
            if upd_flag is True:
                new_deps.append((temp_dict[0], temp_dict[1]))    
        for i in sorted(rm_deps, reverse=True):
            del self.metagraph[i]
        self.metagraph.extend(new_deps)

        self.seq, self.cycles = self.topo_sort(self.metagraph)
        
        for i_constr in indep_constraints:
            self.seq.remove(i_constr)
            index_last = 0
            for dep in self.metagraph:
                if i_constr == dep[1] and (check:=self.seq.index(dep[0])) > index_last:
                    index_last = check
            self.seq.insert(index_last + 1, i_constr)

        for k, v in rm_deps_dict.items():
            a, b = self.topo_sort(v)
            c = [x for x in a if x.startswith('Constraint_')]
            constr_names = []
            constr_index = []
            for index in range(self.seq.index(k), len(self.seq) - 1):
                if self.seq[index + 1].startswith('Constraint_'):
                    constr_names.append(self.seq[index + 1])
                    constr_index.append(index + 1)
                else:
                    break
            constr_names_new = []
            for constr in c:
                if constr in constr_names:
                    constr_names_new.append(constr)
            for enum_index, seq_index in enumerate(constr_index):
                self.seq[seq_index] = constr_names_new[enum_index]


        pprint.pprint(self.seq)
        pprint.pprint(self.groups)

    def init_fcards(self):
        for feature, card_md in self.initial_fcards.items():
            self.handle_fcards(feature, card_md['MM'], card_md['Value'])

    def disable_abstract_features(self):
        for metadata in self.metamodel.values():
            if metadata['__self__']['Abstract'] is not None:
                metadata['__self__'].update({'Active': False})

    def initialize_product(self, description: dict):
        """
        Performs initial model preprocessing.

        INPUTS
        description: model description from web interface or file.

        RETURN
        stages (type = list): sequence of feature to perform constraint solving.
        """
        self.reset()
        self.debug_mode = False  
        self.description = description
        # Read language grammar and create textX metamodel object from it.
        this_folder = dirname(__file__)
        mm = metamodel_from_file(join(this_folder, 'grammar.tx'),
                                 classes=[prec0, prec1, prec2, prec3,
                                          prec4, prec5, prec50, prec6, prec7, prec8,
                                          prec9, prec10, prec11, prec12, prec13,
                                          prec14, prec15, prec16, prec17,
                                          prec18, prec19, prec20, prec21, prec22, prec23, prec24, term],
                                 autokwd=True)

        # Reset shared info variables and create textX model object from description.

        self.model = mm.model_from_str(self.description)

        for parse_type in ['Feature', 'Constraint']:
            for element in self.model.elements:
                if self.cname(element) == 'Feature':
                    self.parse_feature(element, parse_type=parse_type)
        self.define_inheritance()
        self.disable_abstract_features()
        
        self.build_metagraph()
        self.init_fcards()
        pprint.pprint(self.metamodel)
        for constraint in self.constraints.values():
            pprint.pprint(constraint)
        
        return self.seq
