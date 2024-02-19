import copy
import json
import itertools
import logging
import pandas as pd
import pprint
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
                return feature_metadata['ActiveF'] and feature_metadata['ActiveG']
            except Exception:
                return True
        else:
            return feature_metadata

    def get_value(self, feature_metadata):
        if isinstance(feature_metadata, dict) and 'Value' in feature_metadata.keys():
            return feature_metadata['Value']
        elif isinstance(feature_metadata, list):
            res = []
            for subfeature in feature_metadata:
                if isinstance(subfeature, dict) and 'Value' in subfeature.keys():
                    res.append(subfeature['Value'])
                else:
                    return feature_metadata
            return res
        elif isinstance(feature_metadata, dict) and 'Value' not in feature_metadata.keys():
            filtered = {}
            for k, v in feature_metadata.items():
                if v['ActiveF'] is True and v['ActiveG'] is True:
                    filtered.update({k: v})
            return filtered
        else:
            return feature_metadata

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
        key, condition = self.get_value(self.op[1].parse()), self.op[2]
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
            if self.get_value(condition.parse()) is True:
                res.append(item)

        self.api.keyword = ''
        logging.debug(f'filter Result: {res}')
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
            self.api.keyword = 'ReplaceFeature1'
            self.op[1].cross_tree_check(reverse, api)
            self.api.keyword = 'ReplaceFeature'
            self.op[2].cross_tree_check(reverse, api)
            self.api.keyword = ''
        else:
            for part in self.op:
                if isinstance(part, ExpressionElement):
                    part.cross_tree_check(reverse, api)

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
        self.api.exception_flag = False
        # If 'IF' expression was true, ther perform THEN expression.
        if statement is True:
            self.get_value(self.op[2].parse())
        # If not, then perform ELSE expression if it exist. In the opposite case, do nothing.
        elif statement is False and len(self.op) > 3:
            self.get_value(self.op[3].parse())
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
            left, operation, right = self.get_value(l.parse()), op, self.get_value(r.parse())
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
        left, operation, right = self.boolify(self.op[0].parse()), self.op[1], self.boolify(self.op[2].parse())
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
        left = self.get_value(self.op[0].parse())
        self.api.keyword = ''
        right = self.get_value(self.op[2].parse())
        self.api.update_namespace({left: right})

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
        ret = self.get_value(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, r.parse()
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
        ret = self.get_value(self.op[0].parse())
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self.get_value(r.parse())
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
        operation, right = self.op[0], self.get_value(self.op[1].parse())
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
        operation, right = self.op[0], self.get_value(self.op[1].parse())
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
        right = self.get_value(self.op[2].parse())
        self.api.keyword = ''
        left = self.get_value(self.op[1].parse())
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
            self.api.unique_key = self.get_value(self.op[1].parse())
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
        left, operation, right = self.get_value(self.op[0].parse()), self.op[1], self.get_value(self.op[2].parse())

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
        left, operation, right = self.get_value(self.op[0].parse()), self.op[1], self.get_value(self.op[2].parse())

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
        left, operation, right = self.get_value(self.op[0].parse()), self.op[1], self.get_value(self.op[2].parse())

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
        left, operation, right = self.get_value(self.op[0].parse()), self.op[1], self.get_value(self.op[2].parse())

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
            return self.get_value(op.parse())
        elif isinstance(op, str) and op not in keywords and self.src is False:
            op = self.parse_string()
            if isinstance(op, list):
                return op
            fop = op.replace('Fcard.', '').replace('Gcard.', '').replace('fcard.', '').replace('gcard.', '')
            if (self.api.keyword == 'Update' and self.is_feature is True) or self.is_fname is True:
                for mapping in self.mappings:
                    if fop == self.api.get_original_name(mapping):
                        op = f'{self.ftype}.{mapping}' if self.ftype in ('Fcard', 'Gcard') else mapping
                        break
            elif self.api.keyword == 'AllFeatures':
                op = self.api.get_feature_childrens(op, own_only_flag=False)
            elif self.api.keyword == 'ChildNamespace' or self.is_childs is True:
                for mapping in self.mappings:
                    if fop == self.api.get_original_name(mapping):
                        op = mapping
                        break
                op = self.api.get_feature_childrens(op)

            elif self.is_feature is True and self.is_childs is False:
                if 'ReplaceFeature' in self.api.keyword:
                    mappings = [op]
                else:
                    mappings = self.mappings
                try:
                    for mapping in mappings:
                        if fop == self.api.get_original_name(mapping):
                            op = f'{self.ftype}.{mapping}' if self.ftype in ('Fcard', 'Gcard') else mapping
                            break
                    op = self.api.get_feature(op)
                    if self.ftype == 'Gcard':
                        op['Gcard'] = op['Gcard'].split('.')[-1]
                    op['Value'] = self.autoconvert(op[self.ftype]) if isinstance(op[self.ftype], str) else op[self.ftype]
                except KeyError:
                    if 'ReplaceFeature' in self.api.keyword:
                        op = None
                    else:
                        msg = f'No such feature {op}'
                        raise Exception(self.get_error_message(msg))
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
        self.is_fname = False
        self.ftype = 'Value'
        if '"' in op or "'" in op:
            op = op.replace("'", '').replace('"', '')
            self.is_feature = False
        else:
            if self.api.keyword == 'ReplaceFeature':
                op = f'{self.api.replace_feature}.{op}'
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
                split = op.split('.')
                if 'self' in split:
                    split[split.index('self')] = self.api.rf
                elif 'parent' in split:
                    a = re.findall('parent', op)
                    split[split.index('parent')] = '.'.join(self.api.rf.split('.')[:len(self.api.rf.split('.')) - len(a)])
                    split = [i for i in split if i != 'parent']
                elif 'tlf' in split:
                    split[split.index('tlf')] = self.api.rf.split('.')[0]
                op_type = split[0] if split[0] in ['fname', 'childs'] else None
                if op_type == 'childs':
                    self.is_childs = True
                    op = '.'.join(split[1:])
                    check = True
                elif op_type == 'fname':
                    self.is_fname = True
                    op = '.'.join(split[1:])
                else:
                    if split[0] in ['fcard', 'gcard', 'Fcard', 'Gcard']:
                        self.ftype = split[0].capitalize()
                        if for_mapping is False:
                            split[0] = self.ftype
                        else:
                            split = split[1:]
                    op = '.'.join(split)
                    check = True
            else:
                if op == 'self':
                    op = self.api.rf
                    check = True
                else:
                    op = self.autoconvert(op)
            self.is_feature = check
        if self.is_feature is True:
            for part in op.split('.'):
                if part in keywords:
                    raise Exception(f'Feature name {op} contains forbidden keyword: {part}. Please change feature name.')
        return op

    def constraint_sequence_check(self, reverse):
        """
        Function to define constraint validation sequence depending on cross-tree features.

        INPUTS
        reverse (type = bool): the flag that defines features to write value instead of default read.
        """
        if self.api.keyword == 'ReplaceFeature':
            if reverse is True:
                data = self.api.constraint['Assign']
                repl = self.api.assign
            else:
                data = self.api.constraint['Read']
                repl = self.api.read
            for field_type in data.keys():
                rm = []
                for index, feature in enumerate(data[field_type]):
                    if feature in repl:
                        if f'{feature}.{self.op}' in self.api.namespace[self.api.tlf]['Features'].keys():
                            data[field_type][index] = f'{feature}.{self.op}'
                        else:
                            rm.append(index)
                for index in sorted(rm, reverse=True):
                    del data[field_type][index]
        else:
            op = self.parse_string()
            if self.is_feature is True:

                if self.api.keyword == 'AllFeatures':
                    res = []
                    op = self.api.get_feature_childrens(op, own_only_flag=False).keys()
                    for key in op:
                        if key.split('.')[-1] == self.api.unique_key:
                            res.append(key)
                    op = res
                elif self.is_childs is True:
                    op = self.api.get_feature_childrens(op)
                else:
                    op = [op]
                self.api.assign = []
                self.api.read = []
                for feature in op:
                    field_type = feature.split('.', 1)[0] if feature.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
                    feature = feature.split('.', 1)[1] if feature.split('.', 1)[0] in ('Fcard', 'Gcard') else feature
                    if reverse is True:
                        if self.api.keyword == 'ReplaceFeature1':
                            self.api.assign.append(feature)
                        self.api.constraint['Assign'][field_type].append(feature)
                    else:
                        if self.api.keyword == 'ReplaceFeature1':
                            self.api.read.append(feature)
                        self.api.constraint['Read'][field_type].append(feature)
                    if self.api.obj_id in [None, 'prec23']:
                        self.api.obj_id = self.__class__.__name__
                    if self.api.obj_id not in self.api.constraint['Pattern'].keys():
                        self.api.constraint['Pattern'].update({self.api.obj_id: []})
                    self.api.constraint['Pattern'][self.api.obj_id].append(feature)

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
        if isinstance(self.op, ExpressionElement):
            self.op.set_mappings(mappings)

    def get_mappings(self):
        result = {}
        self.tmp = True
        if self.is_feature is True:
            op = self.parse_string(for_mapping=True)
            res = self.api.get_feature(op, field_type=self.ftype, for_mapping=True)
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
        if type(op) is str:
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
                raise Exception(self.get_error_message(f'No such feature: {path}'))

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

    def restore_stage_snap(self, step=None):
        """
        Function to restore stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.

        RETURN
        Stage snapshot.
        """
        snap = copy.deepcopy(self.stage_snap[step] if step is not None else self.last_snap)
        for tlf, value in snap['Namespace'].items():
            self.namespace[tlf]['Features'] = copy.deepcopy(value)
        self.defined_features = copy.deepcopy(self.defined_features_backup)
        logging.info("Namespace was restored due to unvalidated constraint.")

    def save_stage_snap(self, step, data):
        """
        Function to read stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.
        data (type = dict): fields for this step
        """
        namespace = {}
        for tlf, value in self.namespace.items():
            namespace.update({tlf: copy.deepcopy(value['Features'])})
        self.last_snap = {
            'Namespace': copy.deepcopy(namespace),
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
        with open('./core/output/configuration.json', 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=4)

        # TODO: Pickling WFML for dynamicity
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
                abstract = False
                split = name.split('.')
                for index in range(1, len(split) + 1):
                    subname = self.get_original_name('.'.join(split[:index]))
                    if self.namespace[tlf]['Features'][subname]['Abstract'] is not None:
                        abstract = True
                if abstract is False:
                    for mapping, mvalue in feature['MappingsV'].items():
                        value = mvalue['Value']

                        if self.feature_active_flag(mapping, self.namespace[tlf]['Features'], False) is True:
                            path = mapping.split('.')
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
        self.defined_features = {
            'Fcard': [],
            'Gcard': [],
            'Value': []
        }
        self.defined_features_backup = copy.deepcopy(self.defined_features)
        self.step_to_define = {}
        self.original_card_from_c = {'Fcard': {}, 'Gcard': {}}
        self.exception_flag = False
        self.constraint = None
        self.tmp = False
        self.obj_id = None
        self.mode = None
        self.cache = {}
        self.cache_f = None
        self.unique_key = ''
        self.feature_analyzer = FeatureAnalyzer(self)
        self.feature_initializer = FeatureInitializer(self)
        self.boolean = ['prec23', 'prec22', 'prec21', 'prec20', 'prec19', 'prec18', 'prec14', 'term']
        self.var_attrc = ['Fcard']
        self.var_attrv = ['Value', 'Gcard']

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
        if name not in self.cache.keys():
            split = name.split('.')
            split = split[1:] if split[0] in ['fcard', 'gcard', 'Fcard', 'Gcard'] else split
            construct = []
            for part in split:
                construct.append(re.sub(r'_[0-9]+', '', part))
            original = '.'.join(construct)
            self.cache.update({name: original})
        else:
            original = self.cache[name]
        return original

    def validate_feature(self, tlf, cards):
        """
        Function to validate all feature's constraints.

        INPUTS
        tlf (type = str): the name of top-level feature to validate.

        RETURN
        True if all constraints are valid
        """
        if self.debug_mode is True:
            self.validate_constraints(tlf, cards)
        else:
            try:
                self.validate_constraints(tlf, cards)
            except Exception as e:
                logging.info(f'! Exception happened during constraint validation: {e}.')
                return e
        return True

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

    def update_namespace(self, data):
        """
        Function to update namespace with new values.

        INPUTS
        data (type = dict): a collection of feature name - feature value elements to update.

        """
        for key, value in data.items():
            field = key.split('.', 1)[0] if key.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
            mapping = key.split('.', 1)[1] if key.split('.', 1)[0] in ('Fcard', 'Gcard') else key
            fname = self.get_original_name(mapping)
            tlf = fname.split('.')[0]

            if field in self.var_attrc:
                suffix = 'C'
            elif field in self.var_attrv:
                suffix = 'V'
            else:
                suffix = ''
            if suffix == '':
                namespace = self.namespace[tlf]['Features'][fname]
            else:
                namespace = self.namespace[tlf]['Features'][fname][f'Mappings{suffix}'][mapping]
            namespace[field] = value

            if field in ['Fcard', 'Gcard'] and key != 'Initial':
                self.check_integrities(tlf)
                self.activation_flag_update(self.namespace[tlf]['Features'], field, value, mapping)
                if value in ['+', '*', '?'] and field == 'Fcard':
                    init_ns = self.namespace[tlf]['Features'][fname]['InitialC']
                    init_ns['Fcard'] = value
                    init_ns['ActiveF'] = True
                if value in ['or', 'xor'] and field == 'Gcard':
                    init_ns = self.namespace[tlf]['Features'][fname]['InitialV']
                    init_ns['Gcard'] = value

            defined_features = self.defined_features[field]
            if field not in defined_features:
                defined_features.append(field)
        self.defined_features_backup = copy.deepcopy(self.defined_features)

    def get_feature(self, fname):
        """
        Function to read the value of any feature in the namespace.

        INPUTS
        fname (type = str): feature's name.

        RETURN
        list of feature attributes: ActiveF, ActiveG, Value.
        """
        field = fname.split('.', 1)[0] if fname.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
        mapping = fname.split('.', 1)[1] if fname.split('.', 1)[0] in ('Fcard', 'Gcard') else fname
        original = self.get_original_name(mapping)
        tlf = original.split('.')[0]
        suffix = 'C' if field == 'Fcard' else 'V'
        res = self.namespace[tlf]['Features'][original][f'Mappings{suffix}'][mapping]
        return res

    def get_feature_input_type(self, fname):
        """
        Function to read the type of a feature (e.g., integer, string).

        INPUTS
        fname (type = str): feature's name.

        RETURN
        type of a feature.
        """
        mapping = fname.split('.', 1)[1] if fname.split('.', 1)[0] in ('Fcard', 'Gcard') else fname
        original = self.get_original_name(mapping)
        tlf = original.split('.')[0]
        res = self.namespace[tlf]['Features'][original]['Type']
        return res

    def get_feature_childrens(self, fname, own_only_flag=True):
        """
        Function to read the value of some feature's childrens.

        INPUTS
        fname (type = str): feature's name.
        own_only_flag (type = bool): flag to read values only one level lower in the hierarchy or not.

        RETURN
        dict with structure child name - child name attributes
        """
        res = {}
        original = self.get_original_name(fname)
        tlf = original.split('.')[0]
        namespace = self.namespace[tlf]['Features']
        for feature in namespace.values():
            for mapping, mvalue in feature['MappingsV'].items():
                is_child = (len(mapping.split('.')) - len(fname.split('.'))) == 1 if own_only_flag is True else (len(mapping.split('.')) - len(fname.split('.'))) >= 1
                if mapping.startswith(f'{fname}.') and is_child is True:
                    res.update({mapping: mvalue})
        return res

    def activation_flag_update(self, namespace, field, value, mapping=None):
        """
        Function to change activation flags according to cardinalities specified.

        INPUTS
        namespace (type = dict): tlf's namespace.
        field (type = str): type of a feature (fcard, gcard).
        value (type = Any): new cardinality value.
        mapping (type = str): feature mapping to whom new value is related).

        """
        filter_field = value if field == 'Gcard' else mapping
        if not isinstance(filter_field, list):
            filter_field = [filter_field]
        for feature, fvalue in namespace.items():
            for suffix in ['C', 'V']:
                for mapping, mvalue in fvalue[f'Mappings{suffix}'].items():
                    if field == 'Gcard':
                        if any(mapping.startswith(x.rsplit('.', 1)[0]) for x in filter_field):
                            if (suffix == 'V' and len(mapping.split('.')) >= len(filter_field[0].split('.'))) or (suffix == 'C' and len(mapping.split('.')) > len(filter_field[0].split('.'))): 
                                mvalue['ActiveG'] = False if all(x not in mapping for x in filter_field) else True
                    elif field == 'Fcard' and value in ['*', '?', '+'] and suffix == 'C':
                        mvalue['ActiveF'] = True
                    else:
                        mapping_sp = mapping.split('.')
                        mapping_sp[-1] = self.get_original_name(mapping_sp[-1])
                        mapping_or = '.'.join(mapping_sp)
                        if len(mapping.split('.')) >= len(filter_field[0].split('.')) and any(mapping_or in x for x in filter_field):
                            if value == 0 or not isinstance(value, int):
                                mvalue['ActiveF'] = False
                            elif value >= 1:
                                if mapping == feature and len(fvalue[f'Mappings{suffix}'].keys()) > 1:
                                    mvalue['ActiveF'] = False
                                if len(fvalue[f'Mappings{suffix}'].keys()) == 1:
                                    mvalue['ActiveF'] = True
                                for x in filter_field:
                                    if mapping in x:
                                        y = x
                                split = mapping.split(y)
                                if len(split) > 1 and split[1] != '':
                                    if split[1][0] == '_':
                                        index = int(mapping.split(y)[1][1])
                                        mvalue['ActiveF'] = False if index >= value else True

    def get_mappings_for_constraint(self, constraint_data):
        """
        Function to get the list of valid mappings of all features in this constraint.

        INPUTS
        constraint_data (type = dict): constraint's metadata dict.

        RETURN
        constraint_ready (type = bool): flag, do all features in this constraint have specified cardinalities?
        mappings (type = dict): mappings of all features
        deactivated (type = bool): was constraint-related feature deactivated due to cardinalities specified.
        """
        mappings = {'Mappings': {'Assign': {}, 'Read': {}}, 'MappingsFull': {'Assign': {}, 'Read': {}}}
        constraint_ready, deactivated = True, False
        tlf = self.get_original_name(constraint_data['RelatedFeature'].split('.')[0])
        namespace = self.namespace[tlf]['Features']
        rfmappings = self.get_filtered_values(self.map_feature_cache(constraint_data['RelatedFeature'], False), namespace, undefined=False)
        filtered_mappings = []
        if rfmappings is not None:
            for mapping in rfmappings['Value']:
                if mapping in self.cache_f['MappingsV']:
                    filtered_mappings.append(mapping)
        if len(filtered_mappings) > 0:
            for rfmapping in filtered_mappings:
                orig = rfmapping.split('.')

                for assign_type in ['Assign', 'Read']:
                    for ftype in constraint_data[assign_type].keys():
                        card_flag = True if ftype == 'Fcard' else False
                        mapping_type = 'MappingsC' if ftype == 'Fcard' else 'MappingsV'
                        for feature in constraint_data[assign_type][ftype]:
                            tlf = self.get_original_name(feature.split('.')[0])
                            namespace = self.namespace[tlf]['Features']

                            fmappings = {'Mappings': {}, 'MappingsFull': {}}
                            vmappings = self.get_filtered_values(self.map_feature_cache(feature, card_flag), namespace, undefined=False, card=card_flag)
                            if vmappings is None:
                                if assign_type == 'Read' and ftype == 'Value' or ftype == 'Gcard':
                                    constraint_ready = False
                                    logging.info('Constraint reads (gcard) values not available')
                                vmappings = {'Value': []}
                            fmappings.update({'Mappings': vmappings})
                            fmappings.update({'MappingsFull': {'Value': self.map_feature_cache(feature, card_flag)}})
                            for type in fmappings.keys():
                                filtered_mappings = []
                                if type == 'Mappings':
                                    for mapping in fmappings[type]['Value']:
                                        if mapping in self.cache_f[mapping_type]:
                                            filtered_mappings.append(mapping)
                                else:
                                    filtered_mappings = fmappings[type]['Value']
                                if filtered_mappings in [[], {'Assign': [], 'Read': []}] and (ftype != 'Fcard'):
                                    logging.info(f'New disabling : {filtered_mappings}   --   {assign_type} | {ftype}')
                                    constraint_ready = False
                                for mapping in filtered_mappings:
                                    split = mapping.split('.')
                                    for index in range(0, len(split)):
                                        fname = '.'.join(split[:index + 1])
                                        relf = '.'.join(orig[:index + 1])
                                        original = self.get_original_name(fname)
                                        orig_relf = self.get_original_name(relf)
                                        check = False if original == orig_relf and fname != relf else True
                                        if check is True:
                                            if original not in mappings[type][assign_type].keys():
                                                mappings[type][assign_type].update({original: []})
                                            if fname not in mappings[type][assign_type][original]:
                                                mappings[type][assign_type][original].append(fname)
                                            if index == len(split) - 1 and ftype == 'Value' and namespace[original]['MappingsV'][fname]['Value'] is None and assign_type == 'Read' and type == 'Mappings' and namespace[original]['Type'] is not None:
                                                logging.info(f'Feature {fname} is not ready (mapping: {mapping}).')
                                                constraint_ready = False
                                            for constraint in self.namespace[tlf]['Constraints'].values():
                                                if constraint['Validated'] is None:
                                                    if original in constraint['Assign']['Fcard']:
                                                        constraint_ready = False
                                                        logging.info(f'Fcard Feature {fname} will be defined in constraint')
                                        else:
                                            break

        else:
            constraint_ready = False
            deactivated = True
            logging.info('Constraint deactivated')
        return constraint_ready, mappings, deactivated

    def filter_mappings_for_constraint(self, constraint, mappings):
        """
        Function to filter mappings combinations to avoid mapping overlays.
        Example: there are feature a with cardinality 2 and features a.b and a.c with cardinalities 1.
        Mappings are a.b:[a1.b, a2.b], a.c:[a1.c, a2.c]
        Possible combinations are [(a1.b, a1.c), (a1.b, a2.c), (a2.b, a1.c), (a2.b, a2.c)]
        Filtered combinations are [(a1.b, a1.c), (a2.b, a2.c)]

        INPUTS
        mappings (type = dict): dict, that contains all the mappings (read/assign), (fcard/gcard/value).

        RETURN
        dict of filtered mappings with the same structure as input mappings.
        """
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
                if rm is False and comb != ():
                    filtered_combinations.append(comb)
            logging.info(f'Unfiltered combinations for constraint {assign_type} {constraint} ({counter})')
            logging.info(f'Filtered combinations for constraint {assign_type} {constraint} ({len(filtered_combinations)})')
            res[assign_type] = filtered_combinations
        return res

    def validate_constraint(self, constraint, value):
        """
        Function that performs constraint checks and validation.

        INPUTS
        constraint (type = str): constraint's expression.
        value (type = str): constraint's metadata.

        RETURN
        constraint_ready(type = bool): flag, was constraint validated
        """
        constraint_expression = f' \
                {self.description.splitlines()[get_location(value["Constraint"])["line"] - 1].lstrip()}; '
        self.rf = value['RelatedFeature']
        logging.info(f'Constraint preprocessing for feature {self.rf}: {constraint_expression}')
        constraint_ready, mappings, deactivated = self.get_mappings_for_constraint(value)
        mtype = 'Mappings'
        if value['HigherOperation'] in self.boolean and all(x in self.boolean for x in value['Operations']) and deactivated is False:
            if all(x in self.cache_f['MappingsV'] for x in value['Read']['Value']):
                constraint_ready = True
                mtype = 'MappingsFull'
            else:
                constraint_ready = False
        if constraint_ready is True:
            self.tlf = self.get_original_name(value['RelatedFeature'].split('.')[0])
            self.exception_flag = False
            self.keyword = ''
            logging.info(f'Constraint validation for feature {self.rf}: {constraint_expression}')
            res = self.filter_mappings_for_constraint(constraint, mappings[mtype])
            filtered_combinations = []
            if len(res['Assign']) > 0:
                if len(res['Assign']) != len(res['Read']) and len(res['Read']) > 1:
                    raise Exception(f'Len of assign mappings ({len(res["Assign"])}) is not equal to len read mappings ({len(res["Read"])})')
                elif len(res['Assign']) != len(res['Read']) and res['Read'] == []:
                    filtered_combinations = res['Assign']
                elif len(res['Assign']) != len(res['Read']) and len(res['Read']) == 1:
                    for index in range(0, len(res['Assign'])):
                        filtered_combinations.append(res['Assign'][index] + res['Read'][0])
                else:
                    for index in range(0, len(res['Assign'])):
                        filtered_combinations.append(res['Assign'][index] + res['Read'][index])
            else:
                filtered_combinations = res['Read']
            constraint_obj = value['Constraint'].name
            done = False
            for comb in filtered_combinations:
                up = []
                for feature in comb:
                    original = self.get_original_name(feature)
                    for assign_type in ['Read', 'Assign']:
                        for features in value[assign_type].values():
                            if original in features and feature not in up:
                                up.append(feature)
                done = True
                self.iterable['UnvalidatedFeatures'] = comb
                constraint_obj.set_mappings(comb)
                constraint_obj.parse()
            if done is False:
                constraint_obj.set_mappings([])
                constraint_obj.parse()
        else:
            logging.info(f'Constraint {constraint} is not ready to validate')
        return constraint_ready

    def validate_constraints(self, tlf, cards):
        """
        Function to validate all constraints of a defined top-level feature.

        INPUTS
        tlf (type = str): top-level feature's name.

        """
        self.cache_f = self.get_features_ready()
        constraints = {}
        constraints.update({'Dependent': self.namespace[tlf]['ConstraintsValidationOrder']})
        constraints.update({'Independent': self.namespace[tlf]['IndependentConstraints']})
        # TODO top-level constraints
        # constraints.update({'TLF': self.namespace['TopLevelConstraints']})
        validation_codes = []
        for constraints_type, constraints_set in constraints.items():
            for constraint in constraints_set:
                constraint_metadata = self.namespace[tlf]['Constraints'][constraint]
                complex_constraint = False
                for assign_type in ['Assign', 'Read']:
                    for type in constraint_metadata[assign_type].keys():
                        if any(x in constraint_metadata[assign_type][type] for x in ['prec50', 'prec24']):
                            complex_constraint = True
                if constraint_metadata['Validated'] is False and not(cards is True and complex_constraint is True):
                    validation_code = self.validate_constraint(constraint, constraint_metadata)
                    if validation_code is False and constraints_type == 'Dependent':
                        break
                    elif validation_code is True:
                        validation_codes.append(constraint)
        for constraints_type, constraints_set in constraints.items():
            for constraint in constraints_set:
                if constraint in validation_codes:
                    constraint_metadata = self.namespace[tlf]['Constraints'][constraint]
                    constraint_metadata['Validated'] = True

    def map_feature_cache(self, fname, cardinalities=True):
        """
        Function to get all mappings for a feature.

        INPUTS
        fname (type = str): feature's name.
        cardinalities (type = bool), flag to return fcard mappings or value mappings

        RETURN
        list of all mappings.
        """
        split = fname.split('.')
        tlf = split[0]
        original = self.get_original_name(fname)
        suffix = 'C' if cardinalities is True else 'V'
        res = list(self.namespace[tlf]['Features'][original][f'Mappings{suffix}'].keys())
        if len(res) > 1:
            res.remove(original)
        return res

    def map_feature(self, fname, cardinalities=True):
        """
        Function to define all mappings for a feature.

        INPUTS
        fname (type = str): feature's name.
        cardinalities (type = bool), flag to return fcard mappings or value mappings

        RETURN
        list of all mappings
        """
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
                        repeats = 0
                    else:
                        repeats = value['Fcard']
                    if names != []:
                        prev_names = names
                    else:
                        prev_names = [key]
                    for prev_name in prev_names:
                        if (prev_name in key and len(fnamespace[f'MappingsC']) > 1) or len(fnamespace[f'MappingsC']) == 1 or (cardinalities is True and index == len(split)):
                            for i in range(0, repeats):
                                full_name = prev_name if names == [] else f'{prev_name}.{split[index - 1]}'
                                names_temp.append(f'{full_name}_{i}' if repeats > 1 or (cardinalities is False and f"{full_name}_{i}" in fnamespace[f'MappingsV'].keys()) else full_name)
            names = list(dict.fromkeys(names_temp))
        return names

    def preprocess_step(self, tlf):
        result = {}
        if tlf in self.cycles.keys():
            for cycle_part in self.cycles[tlf]:
                result.update(self.preprocess_step_helper(cycle_part))
        else:
            result = self.preprocess_step_helper(tlf)
        return result

    def preprocess_step_helper(self, tlf):
        """
        Function to define the next step features for the current stage (top-level feature).

        INPUTS
        tlf (type = str): top-level feature's name.

        RETURN
        dict of structure fname - ftype
        """

        fcards, values = self.check_integrities(tlf)
        undefined_values, undefined_values = {}, {}
        undefined_cards = self.get_undefined_cards(fcards, values, tlf)
        if undefined_cards is None:
            undefined_values = self.get_filtered_values(values, self.namespace[tlf]['Features'])
        self.step_to_define.update({'Cards': undefined_cards, 'Values': undefined_values})
        logging.info(f'Stage: {tlf}, step: {self.step_to_define}')
        return undefined_cards if undefined_cards is not None else undefined_values

    def check_integrities(self, tlf):
        """
        Function to check the consistency of all namespace features.

        INPUTS
        tlf (type = str): top-level feature's name.

        RETURN
        fcards (type = list): list of all consistent fcards for tlf.
        values (type = list): list of all consistent values for tlf.
        """
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
                        if value[f'Mappings{suffix}'][feature]['ActiveF'] is True:
                            value[f'Mappings{suffix}'][feature]['ActiveF'] = False
                        value[f'Mappings{suffix}'].update({key: copy.deepcopy(value[f'Initial{suffix}'])})
                result = result + check
        return result

    def get_features_ready(self):
        """
        Function to get all features with defined cardinalities.

        INPUTS
        tlf (type = str): top-level feature's name.

        RETURN
        ret (type = dict): lists of all consistent features for tlf.
        """
        ret = {
            'MappingsV': [],
            'MappingsC': []
        }
        for tlf in self.namespace.keys():
            fcards, values = self.check_integrities(tlf)
            undefined_cards = self.get_undefined_cards(fcards, values, tlf)
            if undefined_cards is not None:
                fcards, gcards = undefined_cards['Fcard'], undefined_cards['Gcard']
            else:
                fcards, gcards = [], []

            for mapping_type in ['MappingsV', 'MappingsC']:
                res = []
                for feature, value in self.namespace[tlf]['Features'].items():
                    for mapping in value[mapping_type].keys():
                        flag = True
                        for card in fcards:
                            if card in mapping:
                                flag = False
                        for card in gcards:
                            if (card in mapping and card != mapping and mapping_type == 'MappingsC') or (card in mapping and mapping_type == 'MappingsV'):
                                flag = False
                        if flag is True and mapping not in res:
                            res.append(mapping)
                ret[mapping_type].extend(res)
        return ret

    def get_undefined_cards(self, listc, listv, tlf, filter=True):
        """
        Function to get all undefined cardinalities for the top-level feature.

        INPUTS
        listc (type = list): list of all consistent fcards for tlf.
        listv (type = list): list of all consistent values for tlf.
        tlf (type = str): top-level feature's name
        filter (type = bool): flag, do we filter cardinalities to define step.
        Example: we have feature a with cardinality !(one or more) and feature a.b with the same cardinality.
        If the filter flag is true, we will get only feature a as a result
        Because now we can't define the cardinality of feature a.b correctly
        If we define fcard.a = 2, then for feature a.b, we will need to define 2 cardinalities: a1.b and a2.b

        RETURN
        dict of all undefined cardinalities
        """
        result = {'Fcard': [], 'Gcard': []}
        namespace = self.namespace[tlf]['Features']
        fcards = self.get_undefined_fcards(listc, namespace)
        gcards = self.get_undefined_gcards(listv, namespace)
        if filter is True:
            for card_type in result.keys():
                card_type_list = fcards if card_type == 'Fcard' else gcards
                another_type_list = fcards if card_type == 'Gcard' else gcards
                for celement in card_type_list:
                    flag = True
                    for aelement in another_type_list:
                        if aelement in celement or self.get_original_name(aelement) in celement:
                            flag = False
                        if card_type == 'Fcard' and aelement in celement and (len(celement.split('.')) - len(aelement.split('.')) == 1):
                            result[card_type].append(celement)
                        elif card_type == 'Gcard' and celement in aelement and len(aelement.split('.')) - len(celement.split('.')) == 1:
                            flag = False
                    for aelement in card_type_list:
                        if (aelement in celement and aelement != celement) or (self.get_original_name(aelement) in celement and self.get_original_name(aelement) != celement and self.get_original_name(aelement) != self.get_original_name(celement)):
                            if len(aelement.split('.')) != len(celement.split('.')):
                                flag = False
                    if flag is True and celement not in result[card_type]:
                        result[card_type].append(celement)
        else:
            result.update({'Fcard': fcards, 'Gcard': gcards})
        return result if result != {'Fcard': [], 'Gcard': []} else None

    def feature_active_flag(self, fname, namespace, card):
        """
        Function to check the active state of the feature.

        INPUTS
        fname (type = str): feature's name.
        namespace (type = dict): namespace of corresponding top-level feature
        card (type = bool): flag to check activation for fcards

        RETURN
        bool, is feature active
        """
        suffix = 'C' if card is True else 'V'
        #suffix = 'V'
        shift = 0 if card is True else 0
        split = fname.split('.')
        feature_active_flag = True
        for index in range(0, len(split) - shift):
            split_c = fname.split('.')
            if card is True:
                split_c[index] = self.get_original_name(split_c[index])
            name = '.'.join(split_c[:index + 1])
            original = self.get_original_name(name)
            feature_active_flag = (namespace[original][f'Mappings{suffix}'][name]['ActiveF'] and namespace[original][f'Mappings{suffix}'][name]['ActiveG'])
            if feature_active_flag is False:
                break
        return feature_active_flag

    def get_undefined_fcards(self, list, namespace):
        """
        Function to get all undefined feature cardinalities for a top-level feature.

        INPUTS
        list (type = list): list of all consistent fcards for tlf.
        namespace (type = dict): namespace of corresponding top-level feature

        RETURN
        result (type = list): list of all undefined feature cardinalities.
        """
        result = []
        for feature in list:
            original = self.get_original_name(feature)
            feature_active_flag = self.feature_active_flag(feature, namespace, True)
            fcard_value = namespace[original]['MappingsC'][feature]['Fcard']
            if not isinstance(fcard_value, int) and feature_active_flag is True:
                result.append(feature)
        return result

    def get_undefined_gcards(self, list, namespace):
        """
        Function to get all undefined group cardinalities for a top-level feature.

        INPUTS
        list (type = list): list of all consistent values for tlf.
        namespace (type = dict): namespace of corresponding top-level feature

        RETURN
        result (type = list): list of all undefined group cardinalities.
        """
        result = []
        for feature in list:
            gcard_to_define = False
            original = self.get_original_name(feature)
            feature_active_flag = self.feature_active_flag(feature, namespace, False)
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

    def get_filtered_values(self, list, namespace, undefined=True, card=False):
        """
        Function filter mappings for every feature from the list.

        INPUTS
        list (type = list): list of all consistent values for tlf.
        namespace (type = dict): namespace of corresponding top-level feature
        undefined (type = bool): flag, is a feature still undefined
        card (type = bool): flag to filter mappings for fcards

        RETURN

        result (type = dict): list of all filtered mappings.
        """
        result = {'Value': []}
        for feature in list:
            original = self.get_original_name(feature)
            feature_active_flag = self.feature_active_flag(feature, namespace, card)
            mappings = 'MappingsV' if card is False else 'MappingsC'
            ftype = 'Fcard' if card is True else 'Value'
            feature_value = namespace[original][mappings][feature][ftype]
            feature_type = namespace[original]['Type']
            if feature_active_flag is True:
                if card is False and ((feature_value is None and undefined is True and feature_type not in [None, 'predefined']) or undefined is False):
                    result['Value'].append(feature)
                elif card is True:
                    result['Value'].append(feature)
        return result if result != {'Value': []} else None

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
        for feature_type in ['Read', 'Assign']:
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
            raise Exception(f'Cycled features are currently disabled. Pleace check cycle(s) {list(self.cycles.items())}')
            index += 1
            if f'cycle{index}' not in result:
                result.append(f'cycle{index}')
        logging.info(f'There are {len(res)} stages for cross-tree dependencies: {res}')
        logging.info(f'Cycled features: {self.cycles}')
        logging.info(f'Additional independent features: {independent_features}')
        logging.info(f'Final result: {result}')
        logging.info('Performing staging algorithm: Done')
        return result

    def cardinality_solver(self, feature, card_value: int):
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
        suffix = 'C' if card_type == 'Fcard' else 'V'
        original_name = self.get_original_name(feature)
        tlf = original_name.split('.')[0]
        original_card = self.namespace[tlf]['Features'][original_name][f'Initial{suffix}'][card_type]
        if original_card is None:
            return True
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
                logging.debug('_______________')
                logging.debug(f'Feature: {a}({feature["Constraints"][sequence_number]["RelatedFeature"]}) constraint {sequence_number}: {feature["Constraints"][sequence_number]["Expression"]}')
                logging.debug(feature['Constraints'][sequence_number]['Assign'])
                logging.debug(feature['Constraints'][sequence_number]['Read'])
                logging.debug(feature['Constraints'][sequence_number]['Pattern'])
                logging.debug(feature['Constraints'][sequence_number]['Operations'])
            for sequence_number in feature['IndependentConstraints']:
                logging.debug('------------------')
                logging.debug(f'Feature: {a}({feature["Constraints"][sequence_number]["RelatedFeature"]}) constraint {sequence_number}: {feature["Constraints"][sequence_number]["Expression"]}')
                logging.debug(feature['Constraints'][sequence_number]['Assign'])
                logging.debug(feature['Constraints'][sequence_number]['Read'])
                logging.debug(feature['Constraints'][sequence_number]['Pattern'])
                logging.debug(feature['Constraints'][sequence_number]['Operations'])
        return stages
        # Export both metamodel and model in .dot format for class diagram construction.
        # metamodel_export(mm, join(this_folder, 'output/metamodel.dot'))
        # model_export(model, join(this_folder, 'output/model.dot'))
