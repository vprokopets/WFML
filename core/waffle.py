import copy
import json
import itertools
import logging
import pandas as pd
import re
from core.feature_analyzer import FeatureAnalyzer
from core.feature_initializer import FeatureInitializer
from collections import defaultdict
from functools import reduce
import networkx as nx
from os.path import join, dirname
from textx import metamodel_from_file, get_location
from textx.export import metamodel_export, model_export

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
                       f'Constraint expression: {self.constraint_expression}\n'
                       f'Error position: Line {get_location(self)["line"]},',
                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol}\n'))
        return msg

    def parse(self):
        """
        Function to parse an expression string in self object.

        RETURN
        ret (variable type): result of parsing.
        """
        if len(self.op) == 1:
            ret = self.op[0].parse()
        else:
            if self.api.mode != 'Validate':
                if self.api.exception_flag is False:
                    self.api.exception_flag = True
                    self.exception = True
                else:
                    self.exception = False
                ret = self.value
                if self.exception is True:
                    self.api.exception_flag = False
            else:
                if self.__class__.__name__ in self.api.boolean:
                    ret = self.value
                else:
                    ret = True
        return ret

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
            raise Exception(self.get_error_message(err_msg))

    def cross_tree_check(self, reverse: bool = False, api=None):
        """
        Function to initialize constraint object attributes.
        Also, it detects any features that are present in other tree branches.
        As a result, a connection (own feature - another branch feature) is assigned.

        INPUTS
        reverse (type = bool): the flag that reverses the connection direction.
        api (type = Waffle() object): Waffle API object.
        """
        self.src = False
        self.api = api
        self.constraint_expression = api.constraint_expression
        if len(self.op) > 1:
            self.api.obj_id = self.__class__.__name__
            self.api.constraint['Operations'].append(self.__class__.__name__)
            if self.api.constraint['HigherOperation'] is None:
                upd = self.__class__.__name__
                if upd != 'prec23':
                    self.api.constraint.update({'HigherOperation': upd})
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.cross_tree_check(reverse, api)

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
                    result.update({key: value})
        return result

    def set_mappings(self, mappings):
        """
        Function to set the mapping table.

        INPUTS
        mappings (type = dict): features mapping table.
        """
        self.mappings = mappings
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

    def boolify(self, feature):
        """
        Function to transform feature to boolean type.
        If the input feature is not boolean, then we show the presence of this feature.

        INPUTS
        feature (type = any): feature to check

        RETURN
        result (type = bool): the result of transformation.
        """
        if not isinstance(feature, bool):
            try:
                feature_metadata = self.api.get_feature(feature)
                print(feature)
                print(feature_metadata)
                return feature_metadata['Active']
            except Exception:
                return feature != {'Original': None} and feature is not None
        else:
            return feature

    def parse_feature(self, feature, type='Value'):
        """
        Function to get the value of some type from the feature's metadata.

        INPUTS
        feature (type = any): feature to check.
        type (type = any): feature's metadata type.

        RETURN
        result (variable type): the result of the check.
        """
        if isinstance(feature, dict) and list(feature.keys()) == ['Feature', 'Value', 'Active', 'Mapping']:
            return feature[type]
        else:
            return feature

    def define_truth(self):
        """
        Function to define the truth table for boolean expression.
        """
        if len(self.op) > 1:
            self.exception = False
            if self.__class__.__name__ == self.api.constraint['HigherOperation']:
                self.api.constraint['TruthTable'].update({'Result': self.value})
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.define_truth()

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
        key, condition = self.op[1].parse(), self.op[2]
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
        for item in keys:
            mappings = self.api.name_builder(item, self.api.namespace[item.split('.')[0]]["Features"])
            for feature in mappings:
                self.api.replace_feature = [re.sub(r'_\d+', '', feature).rsplit('.', 1)[0], feature]
                if condition.parse() is True:
                    res.append(feature)

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
        statement = self.boolify(self.op[1].parse())
        print(f'Statement: {statement}')
        self.api.exception_flag = False
        # If 'IF' expression was true, ther perform THEN expression.
        if statement is True:
            self.op[2].parse()
        # If not, then perform ELSE expression if it exist. In the opposite case, do nothing.
        elif statement is False and len(self.op) > 3:
            self.op[3].parse()
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

        left, operation, right = self.boolify(self.op[0].parse()), self.op[1], self.boolify(self.op[2].parse())
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

        left, operation, right = self.boolify(self.op[0].parse()), self.op[1], self.boolify(self.op[2].parse())
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

        left = self.boolify(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.boolify(r.parse())
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

        left = self.boolify(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.boolify(r.parse())
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

        left = self.boolify(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.boolify(r.parse())
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

        operation, right = self.op[0], self.boolify(self.op[1].parse())
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
        for l, op, r in zip(self.op[0::2], self.op[1::2], self.op[2::2]):
            left, operation, right = l.parse(), op, r.parse()
            left, right = [self.parse_feature(feature) for feature in [left, right]]
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
            self.check_exception(ret, f'Expression ({left} {operation} {right})')
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
        left, operation, right = self.boolify(self.op[0].parse()), self.op[1], self.boolify(self.op[2].parse())
        print('________________')
        print(left)
        print(right)
        print(self.op[2].parse())
        if operation == 'requires':
            ret = not left or (left and right)
            self.check_exception(ret, 'Required feature does not exist')
        elif operation == 'excludes':
            ret = not (left and right)
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

        self.api.keyword = 'Update'
        left = self.op[0].parse()
        self.api.keyword = ''
        right = self.op[2].parse()
        print(f'Assign operation: {left} = {right}')
        self.api.update_namespace({left: right}, tmp=True, mappings=self.mappings)

        return True

    def cross_tree_check(self, reverse: bool = False, api=None):
        self.src = False
        self.api = api
        self.constraint_expression = api.constraint_expression
        if len(self.op) > 1:
            self.api.constraint['Operations'].append(self.__class__.__name__)
            if self.api.constraint['HigherOperation'] is None:
                self.api.constraint.update({'HigherOperation': self.__class__.__name__})
        for index, part in enumerate(self.op):
            if isinstance(part, ExpressionElement) and len(self.op) > 1 and index == 0:
                part.cross_tree_check(reverse=True, api=api)
            elif isinstance(part, ExpressionElement):
                part.cross_tree_check(reverse=reverse, api=api)

class prec9(ExpressionElement):
    @property
    def value(self):
        """
        prec9 class performs addition and subtraction operations.

        RETURN
        ret (variable type): previous level object if no prec9 operations are not presented in constraint
                            operation result in opposite case.
        """
        ret = self.parse_feature(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, r.parse()
            right = self.parse_feature(right)
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
        ret = self.parse_feature(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, r.parse()
            right = self.parse_feature(right)
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
        operation, right = self.op[0], self.op[1].parse()
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
        operation, right = self.op[0], self.op[1].parse()
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
        right = self.op[2].parse()
        self.api.keyword = ''
        left = self.op[1].parse()
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
            if feature.split('.')[-1] == key and namespace['Type'] is not None:
                for subfeature, value in namespace['Value'].items():
                    if subfeature != 'Original' and value not in res and not isinstance(value, dict):
                        res.append(value)
                    elif isinstance(value, dict) and 'Value' in value.keys() and value['Value'] not in res:
                        res.append(value['Value'])
        return res

    def cross_tree_check(self, reverse: bool = False, api=None):
        self.src = False
        self.api = api
        self.constraint_expression = api.constraint_expression
        if len(self.op) > 1:
            self.api.obj_id = self.__class__.__name__
            self.api.constraint['Operations'].append(self.__class__.__name__)
            if self.api.constraint['HigherOperation'] is None:
                upd = self.__class__.__name__
                self.api.constraint.update({'HigherOperation': upd})
            self.op[1].cross_tree_check(reverse, api)
            self.api.unique_key = self.op[1].parse()
            self.api.keyword = 'AllFeatures'
            self.op[2].cross_tree_check(reverse, api)
            self.api.keyword = ''
            self.api.unique_key = ''
        else:
            for part in self.op:
                if isinstance(part, ExpressionElement):
                    part.cross_tree_check(reverse, api)


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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()

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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()

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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()

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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()

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
            return op.parse()
        elif isinstance(op, str) and op not in keywords and self.src is False:
            op = self.parse_string()
            if self.api.keyword == 'Update' and self.is_feature is True:
                pass
            elif self.api.keyword == 'AllFeatures':
                op = self.api.get_feature_childrens(op, own_childrens_only=False)
            elif self.api.keyword == 'ChildNamespace':
                op = self.api.get_feature_childrens(op)
            elif self.is_feature is True and self.is_childs is False:
                if self.api.keyword == 'ReplaceFeature':
                    mappings = ['.'.join(op.split('.')[:x]) for x in range(1, len(op.split('.')) + 1)]
                else:
                    mappings = self.mappings
                try:
                    op = self.api.get_feature(op, tmp=self.tmp, mappings=mappings)
                    value = op['Value'] if op['Mapping'] != 'Original' else op['Feature']
                    op['Value'] = self.autoconvert(value) if isinstance(value, str) else value
                    op = op['Value']
                except KeyError:
                    if self.api.keyword == 'ReplaceFeature':
                        op = None
                    else:
                        msg = f'No such feature {op}'
                        raise Exception(self.get_error_message(msg))

            elif self.is_childs is True:
                op = self.api.get_feature_childrens(op, mappings=self.mappings)
        return op

    def parse_string(self, for_mapping=False):
        """
        Function to parse the string for some keywords and do appropriate replacements.

        INPUTS
        for_mapping (type = bool): keyword to capitalize world.

        RETURN
        op (type = str): modified string.
        """
        op = self.op
        check = False
        self.is_childs = False
        if '"' in op or "'" in op:
            op = op.replace("'", '').replace('"', '')
            self.is_feature = False
        else:
            if self.api.keyword == 'ReplaceFeature':
                op = f'{self.api.replace_feature[1]}.{op}'
            elif f'{self.api.rf}.{op}' in self.api.namespace[self.api.tlf]['Features'].keys():
                op = f'{self.api.rf}.{op}'
            if re.match(r'\{.+\}', op):
                op = op.replace('{', '').replace('}', '').replace(' ', '')
                logging.debug("List object")
                op = op.split(',')
                for index, element in enumerate(op):
                    op[index] = self.autoconvert(element)
                logging.debug(op)
            elif re.match(r'(\w+\.)+\w+', op):
                split = op.split('.', 2)
                if 'self' in split:
                    split[split.index('self')] = self.api.rf
                elif 'parent' in split:
                    split[split.index('parent')] = '.'.join(self.api.rf.split('.')[:len(self.api.rf.split('.')) - 1])
                elif 'tlf' in split:
                    split[split.index('tlf')] = self.api.rf.split('.')[0]
                op_type = split[0] if split[0] in ['fname', 'childs'] else None
                if op_type == 'childs':
                    self.is_childs = True
                    op = '.'.join(split[1:])
                    check = True
                elif op_type == 'fname':
                    op = '.'.join(split[1:])
                else:
                    if split[0] in ['fcard', 'gcard']:
                        if for_mapping is False:
                            split[0] = split[0].capitalize()
                        else:
                            split = split[1:]
                    op = '.'.join(split)
                    check = True
            else:
                if op == 'self':
                    op = self.api.rf
                else:
                    op = self.autoconvert(op)
            self.is_feature = check
        return op

    def constraint_sequence_check(self, reverse):
        """
        Function to define constraint validation sequence depending on cross-tree features.

        INPUTS
        reverse (type = bool): the flag that defines features to write value instead of default read.
        """
        op = self.parse_string()
        if self.is_feature is True:
            try:
                if self.api.keyword == 'AllFeatures':
                    res = []
                    op = self.api.get_feature_childrens(op, own_childrens_only=False).keys()
                    for key in op:
                        if key.split('.')[-1] == self.api.unique_key:
                            res.append(key)
                    op = res
                elif self.is_childs is True:
                    op = self.api.get_feature_childrens(op, mappings=self.mappings)
                else:
                    op = [op]
                for feature in op:
                    self.api.get_feature(feature)
                    field_type = feature.split('.', 1)[0] if feature.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
                    feature = feature.split('.', 1)[1] if feature.split('.', 1)[0] in ('Fcard', 'Gcard') else feature
                    if reverse is True:
                        self.api.constraint['FeaturesToAssign'][field_type].append(feature)
                    else:
                        self.api.constraint['Features'][field_type].append(feature)
                    if self.api.obj_id in [None, 'prec23']:
                        self.api.obj_id = self.__class__.__name__
                    if self.api.obj_id not in self.api.constraint['Pattern'].keys():
                        self.api.constraint['Pattern'].update({self.api.obj_id: []})
                    self.api.constraint['Pattern'][self.api.obj_id].append(feature)
            except KeyError:
                raise Exception(f'No such feature {op}')

    def parse(self):
        if self.api.mode != 'Validate':
            self.tmp = True
            ret = self.value
        else:
            if self.is_feature is True:
                op = self.parse_string()
                ret = self.api.truth_table[op]
            else:
                ret = True
        return ret

    def check_cardinalities(self):
        pass

    def set_mappings(self, mappings):
        self.mappings = mappings

    def get_mappings(self):
        result = {}
        self.tmp = True
        if self.is_feature is True:
            op = self.parse_string(for_mapping=True)
            res = self.api.get_feature(op, for_mapping=True)
            for feature in res:
                constructor_original = []
                constructor = []
                for subfeature in feature.split('.'):
                    constructor_original.append(re.sub(r'_\d+', '', subfeature))
                    constructor.append(subfeature)
                    original = '.'.join(constructor_original)
                    if original not in result.keys():
                        result.update({original: []})
                    if '.'.join(constructor) not in result[original]:
                        result[original].append('.'.join(constructor))
        return result

    def cross_tree_check(self, reverse: bool = False, api=None):
        self.src = False
        self.mappings = []
        self.api = api
        op = self.op
        self.tmp = False
        self.constraint_expression = api.constraint_expression
        if self.api.constraint['HigherOperation'] is None:
            self.api.constraint.update({'HigherOperation': self.__class__.__name__})
        if type(op) is str and op not in keywords:
            self.constraint_sequence_check(reverse)
        else:
            self.is_feature = False
            self.is_childs = False
        if isinstance(op, ExpressionElement):
            logging.debug(f"Operation object: {op} with value {type(op)}")
            return op.cross_tree_check(reverse, api)
        elif type(op) is str and op not in keywords and (re.match(r'(\w+\.)+\w+', op) or op in self.api.namespace.keys()):
            if 'self' in op.split('.', 2) or 'parent' in op.split('.', 2) or 'tlf' in op.split('.', 2):
                return
            forbidden_flag = False
            path = op.split('.', 1)

            # Check for cardinality keyword and remove it.
            if path[0] in ['fcard', 'gcard', 'fname', 'childs']:
                path = path[1].split('.', 1)

            # Forbid to add to cross-tree features own features written in full-path form.
            if path[0] == self.api.tlf:
                forbidden_flag = True
            feature = '.'.join(path)
            try:
                api.namespace[path[0]]['Features'][feature]
                if forbidden_flag is False and reverse is False:
                    api.cross_tree_dependencies.append([self.api.tlf, path[0]])
                elif forbidden_flag is False and reverse is True:
                    api.cross_tree_dependencies.append([path[0], self.api.tlf])
            except Exception:
                raise Exception(self.get_error_message(f'No such feature: {path[0]}.{path[1]}'))

    def boolify(self, string):
        if string == 'True':
            return True
        if string == 'False':
            return False
        raise ValueError('String value is not Boolean.')

    def autoconvert(self, string):
        for fn in (self.boolify, int, float):
            try:
                return fn(string)
            except ValueError:
                pass
        return string

    def define_truth(self):
        op = self.parse_string()
        if self.is_feature is True:
            return self.api.truth_table[op]

class Waffle():

    def get_stage_snap(self, step):
        """
        Function to read stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.

        RETURN
        Stage snapshot.
        """
        return self.stage_snap[step]

    def save_stage_snap(self, step, data):
        """
        Function to read stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.
        data (type = dict): fields for this step
        """
        self.last_snap = {
            'Namespace': copy.copy(self.namespace),
            'Fields': data
        }
        self.stage_snap.update({step: self.last_snap})

    def save_json(self):
        """
        Prepare and save final result.

        RETURN
        res (type = dict): final result
        """

        res = copy.deepcopy(self.dot_to_json())

        logging.info('Final result was successfully created.')
        logging.debug(f'Final Model {res}')
        print(f'Final Model {res}')
        with open('./core/output/configuration.json', 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=4)

        # TODO: Pickling WFML for future true dynamicity
        # self.pickle_wfml_data()
        return res

    def get_json(self):
        return open('./core/output/configuration.json', 'r')

    def dot_to_json(self):
        """
        Function to transform dot-split name to JSON tree-like structure.

        RETURN
        output (type = dict): dict object that represents JSON string.
        """
        output = {}

        for tlf in self.namespace.keys():
            for name, feature in self.namespace[tlf]['Features'].items():
                for mapping, value in feature['Value'].items():
                    print(feature['Active'])
                    if feature['Active'][mapping] is True:
                        path = ''
                        if (mapping != 'Original' and len(feature['Value'].items()) > 1):
                            path = mapping.split('.')
                        if len(feature['Value'].items()) == 1:
                            path = name.split('.')
                        if path != '':
                            flag = False
                            for fname in self.namespace[tlf]['Features'].keys():
                                if name in fname and name != fname:
                                    flag = True
                            if flag is False:
                                if value is None:
                                    res = {}
                                else:
                                    res = value
                                target = reduce(lambda d, k: d.setdefault(k, {}), path[:-1], output)
                                target[path[-1]] = res
        return output

    def reset(self):
        """
        Function to reset all attributes of Waffle class object.
        """
        self.namespace, self.cycles, self.stage_snap, self.last_snap, self.req_card = {}, {}, {}, {}, {}
        self.description, self.model, self.tlf, self.rf, self.keyword, self.replace_feature = '', '', '', '', '', ''
        self.cross_tree_dependencies, self.empty_stages, self.requirements = [], [], {}
        self.exception_flag = False
        self.constraint = None
        self.tmp = False
        self.obj_id = None
        self.unique_key = ''
        self.feature_analyzer = FeatureAnalyzer(self)
        self.feature_initializer = FeatureInitializer(self)
        self.boolean = ['prec23', 'prec22', 'prec21', 'prec20', 'prec19', 'prec18', 'prec14', 'prec11', 'term']

        self.stages = {
            "Generated": [],
            "Original": []
        }
        self.iterable = {
            "Stage": 0,
            "UnvalidatedFeatures": []
        }

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
        return '.'.join(construct)

    def update_namespace(self, data, mappings=None, tmp=False):
        """
        Function to update namespace with new data.

        INPUTS
        data (type = dict): data updated.
        mappings (type = list): current mappings list.
        tmp (type = bool): the flag that defines the source to update.
        """
        for key, value in data.items():
            field_type = key.split('.', 1)[0] if key.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
            feature = key.split('.', 1)[1] if key.split('.', 1)[0] in ('Fcard', 'Gcard') else key
            original_feature = re.sub(r'_[0-9]+', '', feature.replace('Fcard.', '').replace('Gcard.', ''))
            tlf = original_feature.split('.', 1)[0]
            if tmp is True:
                features_data = self.last_snap['Namespace'][tlf]['Features']
            else:
                features_data = self.namespace[tlf]['Features']
            if mappings is not None:
                feature_mapped = []
                constructor = []
                for part in feature.split('.'):
                    constructor.append(part)
                    original = '.'.join(constructor)
                    for mapping in mappings:
                        if original == re.sub(r'_\d+', '', mapping):
                            feature_mapped.append(mapping.split('.')[-1])
                feature = '.'.join(feature_mapped)
            features_data[original_feature][field_type].update({feature: value})
            features_data[original_feature]['Active'].update({feature: True})
            if field_type == 'Fcard':
                for subfeature in features_data.keys():
                    for index, mapping in enumerate(list(features_data[subfeature]['Active'].keys())):
                        if value == 0 and f'{feature}' in mapping and f'{feature}_' not in mapping:
                            features_data[subfeature]['Active'][mapping] = False
                            features_data[subfeature]['Active']['Original'] = False
                        elif tmp is True and f'{feature}' in mapping and f'{feature}_' not in mapping and value < len(list(features_data[subfeature]['Active'].keys())):
                            if index > value:
                                features_data[subfeature]['Active'][mapping] = False
                                features_data[subfeature]['Active']['Original'] = False
            elif field_type == 'Gcard':
                for subfeature in features_data.keys():
                    value = [value] if not isinstance(value, list) else value
                    for card in value:
                        if card not in ['xor', 'or'] and not isinstance(card, int):
                            if tmp is True:
                                raise Exception('Only -xor and -or group cardinalities are allowed to set via constraints.')
                    for mapping in features_data[subfeature]['Active'].keys():
                        if len(features_data[subfeature]['Active'].keys()) == 1 and 'Original' in features_data[subfeature]['Active'].keys():
                            key = subfeature
                        else:
                            key = mapping
                        if f'{feature}.' in key:
                            or_flag = False
                            for card in value:
                                if f'{feature}.{card.split(".")[-1]}' in key \
                                        or f'{feature}.{card.split(".")[-1]}_' in key:
                                    or_flag = True
                            if or_flag is False:
                                features_data[subfeature]['Active'][mapping] = False

    def get_feature(self, data, tmp=False, field_type=None, for_mapping=False, mappings=None):
        """
        Function to update namespace with new data.

        INPUTS
        data (type = dict): feature name.
        tmp (type = bool): the flag that defines the source to read from.
        field_type (type = str): field to read from (metadata: value, fcard, etc.).
        for_mapping (type = bool): the flag that defines that we must return all mappings for a feature.
        mappings (type = list): current mappings list.

        RETURN
        dict with the feature's data or all mapping names for this feature
        """
        feature = data.split('.', 1)[1] if data.split('.', 1)[0] in ('Fcard', 'Gcard') else data
        feature = re.sub(r'_\d+', '', feature)
        tlf = feature.split('.', 1)[0]
        if tmp is True:
            features_data = self.last_snap['Namespace'][tlf]['Features']
        else:
            features_data = self.namespace[tlf]['Features']
        if field_type is None:
            field_type = data.split('.', 1)[0] if data.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
        if for_mapping is True:
            return self.name_builder(feature, features_data)
        value, mapping = None, None
        if mappings is not None and mappings != ():
            feature_mapped = []
            constructor = []
            for part in feature.split('.'):
                constructor.append(part)
                original = '.'.join(constructor)
                for mapping in mappings:
                    if original == re.sub(r'_\d+', '', mapping):
                        feature_mapped.append(mapping.split('.')[-1])
            mapping = '.'.join(feature_mapped)
        else:
            mapping = 'Original'
        if mapping not in features_data[feature][field_type].keys():
            mapping = mapping.rsplit('_', 1)[0]
            if mapping not in features_data[feature][field_type].keys():
                mapping = 'Original'
        value = features_data[feature][field_type][mapping]
        return {'Feature': feature,
                'Value': value.split('.')[-1] if isinstance(value, str) and field_type == 'Gcard' else value,
                'Active': features_data[feature]['Active'][mapping] if mappings is not None and mappings != () else features_data[feature]['Active']['Original'],
                'Mapping': mapping}

    def get_feature_childrens(self, feature, own_childrens_only=True, without_mappings=False, mappings=None):
        """
        Function to update namespace with new data.

        INPUTS
        feature (type = dict): feature name.
        own_childrens_only (type = bool): the flag that forbids getting children of children
        without_mappings (type = str): the flag that forbids getting mapped features
        mappings (type = list): current mappings list.

        RETURN
        dict/list with features children
        """
        split = feature.split('.')
        tlf = self.get_original_name(split[0])
        childrens = {}
        if self.tmp is True:
            features_data = self.last_snap['Namespace'][tlf]['Features']
        else:
            features_data = self.namespace[tlf]['Features']
        for fname, subfeature in features_data.items():
            if subfeature['Abstract'] is None:
                if own_childrens_only is True and (len(fname.split('.')) == len(split) + 1
                                                and f'{self.get_original_name(feature)}.' in self.get_original_name(fname)):
                    childrens.update({fname: subfeature})
                elif own_childrens_only is False and (len(fname.split('.')) >= len(split) + 1
                                                and f'{self.get_original_name(feature)}.' in self.get_original_name(fname)):
                    childrens.update({fname: subfeature})
        if without_mappings is False:
            mapped_names = []
            for key in childrens.keys():
                mapped_names = mapped_names + self.name_builder(key, features_data)
            filtered_names = []
            if mappings is not None and mappings != ():
                feature_mapped = []
                constructor = []
                for part in feature.split('.'):
                    constructor.append(part)
                    original = '.'.join(constructor)
                    for mapping in mappings:
                        if original == re.sub(r'_\d+', '', mapping):
                            feature_mapped.append(mapping.split('.')[-1])
                mapping = '.'.join(feature_mapped)
            else:
                mapping = feature
            for name in mapped_names:
                if mapping in name:
                    filtered_names.append(name)
        else:
            mapped_names = list(childrens.keys())
            filtered_names = mapped_names
        return childrens if self.keyword in ['ChildNamespace', 'AllFeatures'] else filtered_names

    def validate_feature(self, tlf):
        """
        Function to validate all feature's constraints.

        INPUTS
        tlf (type = str): the name of top-level feature to validate.

        RETURN
        True if all constraints are valid
        """
        if self.debug_mode is True:
            self.validation_pipeline(tlf)
        else:
            try:
                self.validation_pipeline(tlf)
            except Exception as e:
                logging.info(f'! Exception happened during constraint validation: {e}.')
                return e
        return True

    def validation_pipeline(self, tlf):
        """
        Function to validate all feature's constraints.

        INPUTS
        tlf (type = str): the name of top-level feature to validate.
        """
        for feature_to_validate in self.namespace[tlf]['ConstraintsValidationOrder']:
            constraint = self.namespace[tlf]['Constraints'][feature_to_validate]
            check = self.name_builder(constraint['RelatedFeature'], self.namespace[tlf]['Features'])
            if isinstance(check, list) and len(check) > 0 and self.are_cardinalities_specified_in_constraints(constraint['RelatedFeature']) is True and constraint['Validated'] is False and self.are_cardinalities_specified(constraint) is True:
                self.tlf = tlf
                self.rf = constraint['RelatedFeature']
                self.exception_flag = False
                self.keyword = ''
                constraint_expression = f' \
                    {self.description.splitlines()[get_location(constraint["Constraint"])["line"] - 1].lstrip()}; '
                logging.info(f'Constraint validation for feature {self.rf}: {constraint_expression}')
                constraint['Constraint'].name.check_cardinalities()
                constraint['Constraint'].name.set_mappings([])
                mappings = constraint['Constraint'].name.get_mappings()
                if constraint['HigherOperation'] == 'term':
                    self.keyword = 'CheckFeaturePresence'
                self.map_and_parse(mappings, constraint['Constraint'].name)
                constraint['Validated'] = True

    def map_and_parse(self, mappings, constraint):
        """
        Function to validate all feature constraints.
        It maps every constraint accordingly to mappings of all the constraints' features.

        INPUTS
        mappings (type = dict): dict of all mappings.
        constraint (type = ExpressionElement): constraint object.
        """
        done = False
        combinations = itertools.product(*mappings.values())
        filtered_combinations = []

        for comb in combinations:
            rm = False
            for part in comb:
                if not any((len(part.split('.')) - len(x.split('.')) == 1) and x in part for x in comb) \
                        and len(part.split('.')) > 1:
                    rm = True
                    break
            if rm is False:
                filtered_combinations.append(comb)
        for comb in filtered_combinations:
            done = True
            self.iterable['UnvalidatedFeatures'] = comb
            constraint.set_mappings(comb)
            constraint.parse()
        if done is False:
            constraint.set_mappings([])
            constraint.parse()

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
                       f'Error position: Line {get_location(self)["line"]},',
                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol}\n'))
        return msg

    def name_builder(self, feature, namespace, cardinality_type=None):
        """
        Function to construct full feature name according to all cardinalities in the path.

        INPUTS
        feature (type = str): feature's name.
        namespace (type = dict): entire namespace.
        cardinality_type (type = str): specify field type.

        RETURN
        Feature's transformed name
        """
        feature_name = ''
        feature_list = {}
        feature_split = feature.split('.')
        if len(feature_split) == 1:
            features = []
            fcard = namespace[feature]['Fcard']
            if len(fcard.keys()) == 1:
                key = 'Original'
            else:
                key = feature
            try:
                if int(fcard[key]) > 0:
                    for i in range(0, int(fcard[key])):
                        features.append(f'{feature}_{i}' if int(fcard[key]) > 1 else feature)
            except Exception:
                features.append(feature)
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
                features = self.filter_gcards(gcard, features)
                feature_list.update({part: features})
                break
            features = []
            feature_name = f'{feature_name}.{part}' if feature_name != '' else part
            fcard = namespace[feature_name]['Fcard']

            if feature_list == {}:
                if isinstance(fcard['Original'], str) and len(fcard) == 1:
                    features.append(feature)
                elif isinstance(fcard['Original'], int) and len(fcard) == 1:
                    for i in range(0, int(fcard['Original'])):
                        features.append(f'{part}_{i}' if int(fcard['Original']) > 1 else part)
                else:
                    for key in fcard.keys():
                        if key != 'Original':
                            for i in range(0, int(fcard[key])):
                                features.append(f'{part}_{i}' if int(fcard[key]) > 1 else part)
            else:
                for key in fcard.keys():
                    if key != 'Original':
                        for feature in feature_list[feature_split[index - 1]]:
                            if key.rsplit('.', 1)[0] == feature:
                                for i in range(0, int(fcard[key])):
                                    features.append(f'{feature}.{part}_{i}' if int(fcard[key]) > 1 else f'{feature}.{part}')
                    elif (key == 'Original' and len(fcard.keys()) == 1) and isinstance(fcard['Original'], int):
                        for feature in feature_list[feature_split[index - 1]]:
                            for i in range(0, int(fcard['Original'])):
                                features.append(f'{feature}.{part}_{i}' if int(fcard[key]) > 1 else f'{feature}.{part}')
                    elif (key == 'Original' and len(fcard.keys()) == 1) and isinstance(fcard['Original'], str):
                        for feature in feature_list[feature_split[index - 1]]:
                            features.append(f'{feature}.{part}')
                gcard = namespace[parent_feature]['Gcard']
                features = self.filter_gcards(gcard, features)

            feature_list.update({part: features})
        return feature_list[feature_split[-1]]

    def filter_gcards(self, gcard, features):
        """
        Function to filter features according to group cardinalities.

        INPUTS
        gcard (type = dict): dict with all group cardinalities.
        features (type = dict): entire namespace.

        RETURN
        List of filtered features
        """
        gcard_features = []

        for key, value in gcard.items():
            if key != 'Original' and value not in ['xor', 'or'] and not isinstance(value, int):
                for raw_feature in features:
                    if len(raw_feature.split('.')[-1].split('_')) > 1:
                        feature = raw_feature.rsplit("_", 1)[0]
                    else:
                        feature = raw_feature
                    if isinstance(value, list):
                        for subvalue in value:
                            if feature == f'{key}.{subvalue.split(".")[-1]}':
                                gcard_features.append(raw_feature)
                    else:
                        subvalue = value
                        if feature == f'{key}.{subvalue.split(".")[-1]}':
                            gcard_features.append(raw_feature)
        for feature in features:
            if all(x not in feature for x in gcard.keys()):
                gcard_features.append(feature)
        if len(gcard.keys()) > 1:
            features = gcard_features
        return features

    def are_cardinalities_specified_in_constraints(self, feature):
        """
        Function to check whether cardinalities are specified.

        INPUTS
        feature (type = str): feature to check.

        RETURN
        res (type = bool): boolean that represents result
        """
        res = True
        for tlf in self.namespace.keys():
            for constraint in self.namespace[tlf]['Constraints'].values():
                split = feature.split('.')
                for part in range(0, len(split)):
                    check = '.'.join(split[:part + 1])
                    if (check in constraint['FeaturesToAssign']['Fcard'] or check in constraint['FeaturesToAssign']['Gcard']) and constraint['Validated'] is False:
                        res = False
        return res

    def are_cardinalities_specified(self, constraint):
        """
        Function to check whether cardinalities are specified.

        INPUTS
        feature (type = str): feature to check.

        RETURN
        res (type = bool): boolean that represents result
        """
        res = True
        features = []
        features.append(constraint['RelatedFeature'])
        features = features + constraint['Features']['Fcard']
        features = features + constraint['Features']['Gcard']
        features = features + constraint['Features']['Value']
        constraint_expression = f' \
                    {self.description.splitlines()[get_location(constraint["Constraint"])["line"] - 1].lstrip()}; '
        logging.info(f'Constraint validation for feature {self.rf}: {constraint_expression}')
        for feature in features:
            split = feature.split('.')
            tlf = split[0]
            cards = self.get_unresolved_cardinalities1(tlf, self.namespace[tlf]['Features'])
            cards_filtered = {'Fcard': [], 'Gcard': []}
            if isinstance(cards, dict):
                for type in cards.keys():
                    for card in cards[type].keys():
                        original = self.get_original_name(card)
                        if original not in cards_filtered:
                            cards_filtered[type].append(self.get_original_name(card))
            for part in range(0, len(split)):
                check = '.'.join(split[:part + 1])
                if check in cards_filtered['Fcard'] or (check in cards_filtered['Gcard'] and part != len(split) - 1):
                    res = False
        return res

    def get_unresolved_cardinalities1(self, feature, namespace):
        """
        Function to get a list of cardinalities that are not specified yet.

        INPUTS
        feature (type = dict): top-level feature to get cardinalities.
        namespace (type = dict): entire namespace.

        RETURN
        List of not specified cardinalities
        """
        result = {'Fcard': {}, 'Gcard': {}}
        for key, value in namespace.items():
            if key.split('.')[0] == feature:
                mappings_f = self.name_builder(key, namespace)
                for mapping in mappings_f:
                    fcard, fcard_to_define = self.parse_fcard(mapping, value)
                    if fcard_to_define is True:
                        result['Fcard'].update({mapping: fcard})
                for mapping in mappings_f:
                    gcard, gcard_to_define = self.parse_gcard(mapping, value)
                    if gcard_to_define is True and mapping not in result['Fcard'].keys():
                        result['Gcard'].update({mapping: gcard})
        return result

    def get_unresolved_cardinalities(self, feature, namespace):
        """
        Function to get a list of cardinalities that are not specified yet.

        INPUTS
        feature (type = dict): top-level feature to get cardinalities.
        namespace (type = dict): entire namespace.

        RETURN
        List of not specified cardinalities
        """
        result = {'Fcard': {}, 'Gcard': {}}
        for key, value in namespace.items():
            if key.split('.')[0] == feature and self.are_cardinalities_specified_in_constraints(key) is True:
                mappings_f = self.name_builder(key, namespace, "Fcard")
                mappings_g = self.name_builder(key, namespace, "Gcard")
                for mapping in mappings_f:
                    fcard, fcard_to_define = self.parse_fcard(mapping, value)
                    if fcard_to_define is True:
                        result['Fcard'].update({mapping: fcard})
                for mapping in mappings_g:
                    gcard, gcard_to_define = self.parse_gcard(mapping, value)
                    if gcard_to_define is True and mapping not in result['Fcard'].keys():
                        result['Gcard'].update({mapping: gcard})
        if result == {'Fcard': {}, 'Gcard': {}}:
            result_filtered = None
        else:
            result_filtered = {'Fcard': {}, 'Gcard': {}}
            for card_type in ['Fcard', 'Gcard']:
                for key, value in result[card_type].items():
                    other_keys = list(result['Fcard'].keys()) + list(result['Gcard'].keys())
                    other_keys.remove(key)
                    if all(x not in key for x in other_keys):
                        result_filtered[card_type].update({key: value})
        return result_filtered

    def parse_fcard(self, feature, cards):
        """
        Function to get a list of cardinalities that are not specified yet.

        INPUTS
        feature (type = dict): top-level feature to get cardinalities.
        namespace (type = dict): entire namespace.

        RETURN
        List of not specified cardinalities
        """
        card_to_define = False
        if feature in cards['Fcard'].keys():
            card_value = cards['Fcard'][feature]
        elif feature not in cards['Fcard'].keys() and feature.split('_')[0] in cards['Fcard'].keys():
            return None, False
        else:
            card_value = cards['Fcard']['Original']
        try:
            int(card_value)
        except Exception:
            if (not isinstance(card_value, int) and not isinstance(card_value, list)):
                card_to_define = True
        return card_value, card_to_define

    def parse_gcard(self, feature, cards):
        """
        Function to parse an initial group cardinality value.

        INPUTS
        feature (type = dict): top-level feature to get cardinalities.
        cards (type = dict): cardinalities of a feature.

        RETURN
        card_value (type = dict): transformed cardinality value.
        card_to_define (type = dict): flag defines that the cardinality value was transformed successfully.
        """
        card_to_define = False
        if feature in cards['Gcard'].keys():
            card_value = cards['Gcard'][feature]
        else:
            card_value = cards['Gcard']['Original']
        if card_value in ['or', 'mux', 'xor']\
                or isinstance(card_value, int)\
                or re.match(r'^\d+$', str(card_value)):
            card_to_define = True
        elif isinstance(card_value, str):
            card_to_define = True
            strspl = card_value.split(',')
            for lexem in strspl:
                if not (re.match(r'(\d+\.\.)+\d+', lexem) or re.match(r'^\d+$', lexem)):
                    card_to_define = False
        return card_value, card_to_define

    def get_unresolved_features(self, feature, namespace):
        """
        Function to get a list of features that are not specified yet.

        INPUTS
        feature (type = dict): top-level feature to get features.
        namespace (type = dict): entire namespace.

        RETURN
        List of not specified features
        """
        result = {}
        for key, value in namespace.items():
            if key.split('.')[0] == feature and self.are_cardinalities_specified_in_constraints(key) is True:
                if value['Type'] is not None and \
                        value['Value']['Original'] is None and \
                        len((value['Value'].keys())) == 1:
                    result.update({key: value['Type']})
        if result == {}:
            result = None
        else:
            for key in list(result.keys()):
                names = self.name_builder(key, namespace)
                if isinstance(names, list) and len(names) >= 1:
                    for name in names:
                        result.update({name: result[key]})
                    if len(names) > 1 or (len(names) == 1 and names[0] != key):
                        result.pop(key, None)
                elif isinstance(names, list) and len(names) == 0:
                    result.pop(key, None)
        if result is not None:
            if result == {}:
                result = None
        return result

    def define_layer(self, top_level_feature):
        """
        Function to define a sub-step for top level feature.

        INPUTS
        top_level_feature (type = str): top-level feature to define a sub-step.

        RETURN
        sublayer (type = dict/str): sub-step.
        """
        namespace = self.namespace[top_level_feature]['Features']

        sublayer = self.get_unresolved_cardinalities(top_level_feature, namespace)

        logging.info(f'Top-level feature {top_level_feature} cardinalities to configure: {sublayer}')
        if sublayer is None:
            sublayer = self.get_unresolved_features(top_level_feature, namespace)
            logging.info(f'Top-level feature {top_level_feature} features to configure: {sublayer}')
            if sublayer is None and self.namespace[top_level_feature]['Validated'] is False:
                sublayer = 'Empty stage'
        return sublayer

    def cross_tree_dependencies_handler(self):
        """
        Function to define all cross-tree dependencies.
        """
        logging.info('Detecting cross-tree constraints.')
        self.cross_tree_dependencies = []

        for tlf, tlf_value in self.namespace.items():
            if tlf_value['Features'][tlf]['Abstract'] is None:
                for constraint in tlf_value['Constraints'].values():
                    self.obj_id = None
                    self.constraint = constraint
                    self.constraint_expression = \
                        f'{self.description.splitlines()[get_location(constraint["Constraint"])["line"] - 1].lstrip()}; '
                    self.constraint['Expression'] = self.constraint_expression
                    self.tlf = tlf
                    self.rf = constraint['RelatedFeature']
                    constraint['Constraint'].name.cross_tree_check(api=self)
                    self.define_conditions_set(constraint)
        logging.info('Processing cross-tree dependencies: Starting')
        self.cross_tree_dependencies.sort()
        self.cross_tree = list(k for k, _ in itertools.groupby(self.cross_tree_dependencies))
        self.tmp = True
        logging.info('Processing cross-tree dependencies: Done')

    def define_conditions_set(self, constraint):
        """
        Function to define a truth table for specified constraint.

        INPUTS
        constraint (type = ExpressionElement): constraint object.
        """
        base = []
        self.requirements.update({constraint['Expression']: []})
        for feature_type in ['Features', 'FeaturesToAssign']:
            for value in constraint[feature_type].values():
                base = [*base, *value]
        base_filtered = []
        for feature in base:
            for prec, values in constraint['Pattern'].items():
                if feature in values and prec not in self.boolean:
                    base_filtered.append(feature)
        base_conditions = list(itertools.product([False, True],
                                                    repeat=len(base)))
        base = [fruit for fruit in base if fruit not in base_filtered]
        for conditions_set in base_conditions:
            combination = {}
            for index, var in enumerate(base):
                if constraint['HigherOperation'] in self.boolean:
                    combination.update({var: conditions_set[index]})
                else:
                    combination.update({var: True})
            for feature in base_filtered:
                if feature not in combination.keys():
                    combination.update({feature: True})
            if combination not in constraint['TruthTable']:
                self.truth_table = combination
                self.mode = 'Validate'
                res = constraint['Constraint'].name.parse()
                if res is True:
                    constraint['TruthTable'].append(combination)
                    self.requirements[constraint['Expression']].append(combination)
                self.mode = None
        unique = [dict(t) for t in {tuple(d.items()) for d in constraint['TruthTable']}]
        constraint['TruthTable'] = unique

    def define_sequence_for_deps(self, dependencies):
        """
        Function to define a sequence of execution by topological sorting.

        INPUTS
        dependencies (type = list): list of dependencies.

        RETURN
        cycles (type = dict): dict of cycles and elements it contains.
        res (type = list): sequence of dependencies elements to execute.
        """
        # Create networkx graph object
        G = nx.DiGraph(dependencies)
        index = 0
        remove_dependencies = []
        cycles = {}
        # Find all cycles in graph. Create list of cycle dependencies.
        for cycle in nx.simple_cycles(G):
            index += 1
            cycles.update({f'cycle{index}': cycle})
            logging.debug(f'Cycle cycle{index} contain elements: {cycle}')
            for dep in dependencies:
                if dep[0] in cycle and dep[1] not in cycle:
                    dep[0] = f'cycle{index}'
                elif dep[0] not in cycle and dep[1] in cycle:
                    dep[1] = f'cycle{index}'
                elif dep[0] in cycle and dep[1] in cycle:
                    remove_dependencies.append(dep)
        for dep in remove_dependencies:
            try:
                dependencies.remove(dep)
            except ValueError:
                logging.debug(f'Dependency {dep} already removed.')
        # Perform topological sort for dependencies.
        res = self.topological_sort(dependencies)
        res.reverse()
        return cycles, res

    def topological_sort(self, dependency_pairs):
        """
        Subfunction to define sequence of features to validate. The analogue of directed graph path.

        INPUTSe
        dependency_pairs: list of cross-tree dependencies pairs.

        RETURN
        ordered (type = list): sequence of independent features to validate.
        cyclic (type = list): list of cyclic features.
        """
        logging.info('Topological sorting: Starting')
        num_heads = defaultdict(int)
        tails = defaultdict(list)
        for h, t in dependency_pairs:
            num_heads[t] += 1
            tails[h].append(t)

        ordered = [h for h in tails if h not in num_heads]
        for h in ordered:
            for t in tails[h]:
                num_heads[t] -= 1
                if not num_heads[t]:
                    ordered.append(t)
        logging.info('Topological sorting: Done')
        return ordered

    def staging(self, cross_tree_dependencies: list):
        """
        Function to define sequence of features to validate.

        INPUTS
        cross_tree_dependencies: list of cross-tree dependencies.

        RETURN
        ret_val (type = list): sequence of features to validate.
        """
        logging.info('Performing staging algorithm: Starting')
        # Define cross-tree and independent features
        all_features = list(self.namespace.keys())
        features_from, features_to = ([] for _ in range(2))
        for dep in cross_tree_dependencies:
            features_from.append(dep[0])
            features_to.append(dep[1])
        independent_features = [x for x in all_features if x not in features_from
                                and x not in features_to
                                and self.namespace[x]['Features'][x]['Abstract'] is None]

        self.cycles, res = self.define_sequence_for_deps(cross_tree_dependencies)
        independent_features.reverse()
        result = res + independent_features if res is not None else independent_features

        # Add independent cycles
        index = 0
        for cycle in self.cycles:
            index += 1
            if f'cycle{index}' not in result:
                result.append(f'cycle{index}')
        logging.info(f'There are {len(res)} stages for cross-tree dependencies: {res}')
        logging.info(f'Cycled features: {self.cycles}')
        logging.info(f'Additional independent features: {independent_features}')
        logging.info(f'Final result: {result}')
        logging.info('Performing staging algorithm: Done')
        return result

    def cardinality_solver(self, feature, card_value: int, originals: dict):
        """
        Function to check, is target value allowed by cardinality record ot not.

        INPUTS
        feature (type = feature): feature to check cardinality value (get it`s cardinality record).
        card_type (type = str): feature or group cardinality.
        card_value (type = int): cardinality value to check.

        RETURN
        True (type = bool): if check was successfull;
        Raise Exception if not.
        """
        card_type = feature.split('.')[0]
        original_name = feature.split('.', 1)[1]
        original_card = originals[card_type][original_name]
        if card_type == 'Fcard':
            x = card_value
        elif card_type == 'Gcard' and isinstance(card_value, str):
            x = 1
        elif card_type == 'Gcard' and isinstance(card_value, list):
            x = len(card_value)
        else:
            raise Exception('Wrong cardinality value')
        res = []
        # Transform special cardinality values to simple constraint. Fullfill match groups.
        if original_card == '*':
            res.append(['x>=0'])
        elif original_card in ['+', 'or']:
            res.append('x>=1')
        elif original_card in ['?', 'mux']:
            res.append(['x>=0', 'x<=1'])
        elif original_card == 'xor':
            res.append('x==1')
        elif type(original_card) == int or re.match(r'^\d+$', original_card):
            res.append(f'x=={original_card}')
        else:
            strspl = original_card.split(',')
            for lexem in strspl:
                if re.match(r'(\d+\.\.)+(\d+|\*)', lexem):
                    lexspl = lexem.split('..')
                    res.append([f'x>={lexspl[0]}', f'x<={lexspl[1]}'] if lexspl[1] != '*' else [f'x>={lexspl[0]}'])
                else:
                    res.append(f'x=={lexem}')
        match_group_res = []

        # Check all match groups
        for match_group in res:
            if type(match_group) == list:
                subres = []
                for match in match_group:
                    subres.append(pd.eval(match))
                match_group_res.append(all(subres))
            else:
                match_group_res.append(pd.eval(match_group))
        result = any(match_group_res)

        if result is True:
            logging.debug(f'Result: {x} lies in interval {original_card}')
            return True
        else:
            logging.debug(f'Result: {x} not lies in interval {original_card}')
            return Exception(f'Result: {x} not lies in interval {original_card}')

    def initialize_product(self, description: dict):
        """
        Performs initial model preprocessing.

        INPUTS
        description: model description from web interface or file.

        RETURN
        stages (type = list): sequence of feature to perform constraint solving.
        """
        self.debug_mode = False
        self.reset()
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
        self.namespace = self.feature_initializer.initialize_namespace(self.model)
        self.cross_tree_dependencies_handler()
        stages = self.staging(self.cross_tree)
        self.feature_analyzer.analyze_feature_model(stages)
        for a, feature in self.namespace.items():
            for sequence_number in feature['ConstraintsValidationOrder']:
                print('_______________')
                print(f'Feature: {a}({feature["Constraints"][sequence_number]["RelatedFeature"]}) constraint {sequence_number}: {feature["Constraints"][sequence_number]["Expression"]}')
                print(feature['Constraints'][sequence_number]['FeaturesToAssign'])
                print(feature['Constraints'][sequence_number]['Features'])
                print(feature['Constraints'][sequence_number]['Pattern'])
        return stages
        # Export both metamodel and model in .dot format for class diagram construction.
        # metamodel_export(mm, join(this_folder, 'output/metamodel.dot'))
        # model_export(model, join(this_folder, 'output/model.dot'))
