import copy
import json
import itertools
import logging
from unittest.mock import NonCallableMagicMock
import numexpr as ne
import pandas as pd
import re
import numpy as np
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
            'or', 'product', 'some', 'sum', 'then', 'xor', '_', 'fcard', 'gcard', 'waffle.error']

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
        ol = self._tx_position_end - self._tx_position
        msg = ''.join((f'{message}.\n',
                       f'Constraint expression: {self.constraint_expression}\n'
                       f'Error position: Line {get_location(self)["line"]},',
                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol}\n'))
        return msg

    def parse(self):
        if len(self.op) == 1:
            ret = self.op[0].parse()
        else:
            if self.api.exception_flag is False:
                self.api.exception_flag = True
                self.exception = True
            else:
                self.exception = False
            ret = self.value
            self.api.exception_flag = False
        return ret

    def update(self):
        return self.op[0].update()

    def check_exception(self, res: bool, err_msg: str):
        if res is False and self.exception is True:
            raise Exception(self.get_error_message(err_msg))

    def cross_tree_check(self, reverse: bool = False, api=None):
        self.src = False
        self.api = api
        self.constraint_expression = api.constraint_expression
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.cross_tree_check(reverse, api)

    def get_mappings(self):
        result = {}
        for part in self.op:
            if isinstance(part, ExpressionElement):
                sub = part.get_mappings()
                for key, value in sub.items():
                    result.update({key: value})
        return result

    def set_mappings(self, mappings):
        self.mappings = mappings
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.set_mappings(mappings)

    def check_cardinalities(self):
        # TODO: Update cardinality rules for each prec. class (currently active for prec12 only)
        if len(self.op) > 1:
            res = self.get_mappings()
            for feature, mappings in res.items():
                if len(mappings) > 1:
                    msg = f'Cardinality value of {feature} should be equal 1 (currently {len(mappings)})'
                    raise Exception(self.get_error_message(msg))
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.check_cardinalities()


class prec24(ExpressionElement):
    card_mode = 'Full'
    @property
    def value(self):
        logging.debug(f'Level 24 Operation filter x where y.')
        key, condition = self.op[1].parse(), self.op[2]
        return self.filter(condition, key)

    def filter(self, condition, key):
        res = []
        old_path = self.get_wfml_data('Path')
        for item in key:
            self.update_wfml_data('Path', f'{old_path}.{item}')
            if condition.parse() is True:
                res.append(item)
        self.update_wfml_data('Path', old_path)
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
        statement = self.op[1].parse()

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

        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
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

        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        ret = not(left) or right

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

        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        ret = left or right

        self.check_exception(ret, f'Expression ({left} {operation} {right})')
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

        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        ret = bool(left) ^ bool(right)

        self.check_exception(ret, f'Expression ({left} {operation} {right})')
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

        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        ret = left and right

        self.check_exception(ret, f'Expression ({left} {operation} {right})')
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

        operation, right = self.op[0], self.op[1].parse()
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

        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        logging.debug(f'Level 12 comparison {operation} operation')
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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        if operation == 'requires':
            if left is not None and right is None:
                raise Exception(f'Required feature {right} does not exist')
        elif operation == 'excludes':
            if left is not None and right is not None:
                raise Exception(f'features {left} excludes {right}, so one of them should not exist.')
        return True

class prec10(ExpressionElement):
    @property
    def value(self):
        """
        prec10 class performs assignment operation.

        RETURN
        ret (variable type): previous level object if no prec10 operations are not presented in constraint
                            operation result in opposite case.
        """
        self.api.upd_flag = True
        left = self.op[0].parse()
        self.api.upd_flag = False
        right = self.op[2].parse()
        self.api.update_namespace({left: right}, True)

        return True

    def cross_tree_check(self, reverse: bool = False, api=None):
        self.src = False
        self.api = api
        self.constraint_expression = api.constraint_expression
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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        logging.debug(f'Level 9 Math operation {operation} ')
        ret = ne.evaluate(f'{left}{operation}{right}')
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
        left, operation, right = self.op[0].parse(), self.op[1], self.op[2].parse()
        logging.debug(f'Level 8 Math operation {operation} ')
        ret = ne.evaluate(f'{left}{operation}{right}')
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
        left, right = self.op[1].parse(), self.op[2].parse()
        logging.debug(f'Level 5.0 Operation unique x in y.')
        ret = self.find_unique(right, left)

        return ret

    def find_unique(self, input, key, res=None):
        if res is None:
            res = []
        for k, v in input.items():
            if k == key:
                if type(v) is dict and 'value' in v.keys() and v['value'] not in res:
                    res.append(v['value'])
                elif type(v) is not dict and v not in res:
                    res.append(v)
            if type(v) is dict:
                self.find_unique(v, key, res)
        logging.debug(f'find_unique Result: {res}')
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
        if type(op) is str and op not in keywords and self.src is False:
            op = self.parse_string()
        return op

    def parse_string(self, for_mapping=False):
        op = self.op
        if f'{self.api.rf}.{op}' in self.api.namespace[self.api.tlf]['Features'].keys():
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
                op = self.api.get_feature_childrens('.'.join(split[1:]))
            elif op_type == 'fname':
                op = '.'.join(split[1:])
            else:
                if split[0] in ['fcard', 'gcard']:
                    if for_mapping is False:
                        split[0] = split[0].capitalize()
                    else:
                        split = split[1:]
                feature_name = '.'.join(split)
                if self.api.upd_flag is False:
                    feature_type = self.api.get_feature(feature_name, self.tmp, 'Type')
                    op = self.api.get_feature(feature_name, self.tmp)
                    if isinstance(op, dict):
                        for key, value in copy.copy(op).items():
                            if key in self.mappings:
                                op = value
                        if for_mapping is True and feature_type == 'predefined':
                            op = {feature_name: None}
                else:
                    op = feature_name

        return op

    def parse(self):
        self.tmp = True
        return self.value

    def check_cardinalities(self):
        pass

    def set_mappings(self, mappings):
        self.mappings = mappings

    def get_mappings(self):
        result = {}
        self.tmp = True
        if type(self.op) is str and self.op not in keywords:
            res = self.parse_string(True)
            if type(res) is dict:
                res = list(copy.copy(res.keys)())
                if 'Original' in res:
                    res.remove('Original')
                result.update({self.op: res})
        return result

    def cross_tree_check(self, reverse: bool = False, api=None):
        self.src = False
        self.mappings = []
        self.api = api
        op = self.op
        self.tmp = False
        self.constraint_expression = api.constraint_expression
        if type(op) is str and op not in keywords and re.match(r'(\w+\.)+\w+', op):
            if 'self' in op.split('.', 2) or 'parent' in op.split('.', 2):
                return
            forbidden_flag = False
            path = op.split('.', 1)

            # Check for cardinality keyword and remove it.
            if path[0] in ['fcard', 'gcard', 'fname', 'childs']:
                path = path[1].split('.', 1)

            # Forbid to add to cross-tree features own features written in full-path form.
            if path[0] == self.api.tlf:
                forbidden_flag = True
            try:
                api.namespace[path[0]]['Features'][f'{path[0]}.{path[1]}']
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


class Waffle():

    def get_stage_snap(self, step):
        return self.stage_snap[step]

    def save_stage_snap(self, step, data):
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

        with open('./core/output/configuration.json', 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=4)

        # TODO: Pickling WFML for future true dynamicity
        # self.pickle_wfml_data()
        return res

    def get_json(self):
        return open('./core/output/configuration.json', 'r')

    def dot_to_json(self):
        output = {}

        for tlf in self.namespace.keys():
            for feature in self.namespace[tlf]['Features'].values():
                for mapping, value in feature['Value'].items():
                    if mapping != 'Original':
                        path = mapping.split('.')
                        target = reduce(lambda d, k: d.setdefault(k, {}), path[:-1], output)
                        target[path[-1]] = value
        return output

    def reset(self):
        self.namespace, self.cycles, self.stage_snap, self.last_snap = {}, {}, {}, {}
        self.description, self.model, self.tlf, self.rf = '', '', '', ''
        self.cross_tree_dependencies = []
        self.exception_flag, self.upd_flag = False, False
        self.feature_analyzer = FeatureAnalyzer()
        self.feature_initializer = FeatureInitializer()

        self.stages = {
            "Generated": [],
            "Original": []
        }
        self.iterable = {
            "Stage": 0,
            "UnvalidatedFeatures": []
        }

    def get_original_name(self, name):
        split = name.split('.')
        split = split[1:] if split[0] in ['fcard', 'gcard', 'Fcard', 'Gcard'] else split
        construct = []
        for part in split:
            construct.append(re.sub(r'_[0-9]+', '', part))
        return '.'.join(construct)

    def update_namespace(self, data, tmp=False):
        for key, value in data.items():
            field_type = key.split('.', 1)[0] if key.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
            feature = key.split('.', 1)[1] if key.split('.', 1)[0] in ('Fcard', 'Gcard') else key
            original_feature = re.sub(r'_[0-9]+', '', feature.replace('Fcard.', '').replace('Gcard.', ''))
            tlf = original_feature.split('.', 1)[0]
            if tmp is True:
                self.last_snap['Namespace'][tlf]['Features'][original_feature][field_type].update({feature: value})
            else:
                self.namespace[tlf]['Features'][original_feature][field_type].update({feature: value})

    def get_feature(self, data, tmp=False, field_type=None):

        feature = data.split('.', 1)[1] if data.split('.', 1)[0] in ('Fcard', 'Gcard') else data
        tlf = feature.split('.', 1)[0]
        if tmp is True:
            features_data = self.last_snap['Namespace'][tlf]['Features']
        else:
            features_data = self.namespace[tlf]['Features']
        if field_type is None:
            field_type = data.split('.', 1)[0] if data.split('.', 1)[0] in ('Fcard', 'Gcard') else 'Value'
        if features_data[feature]['Type'] is None:
            try:
                check = self.name_builder(feature, features_data)
                if isinstance(check, list) and len(check) == 0:
                    return False
                else:
                    return True
            except Exception:
                return True
        else:
            return features_data[feature][field_type]

    def validate_feature(self, tlf):
        debug_mode = False
        if debug_mode is True:
            self.validation_pipeline(tlf)
        else:
            try:
                self.validation_pipeline(tlf)
            except Exception as e:
                logging.info(f'! Exception happened during constraint validation: {e}.')
                return e
        return True

    def validation_pipeline(self, tlf):
        for constraint in self.namespace[tlf]['Constraints'].values():
            check = self.name_builder(constraint['RelatedFeature'], self.namespace[tlf]['Features'])
            if isinstance(check, list) and len(check) > 0:
                constraint_expression = f'{self.description.splitlines()[get_location(constraint["Constraint"])["line"] - 1].lstrip()}; '
                logging.info(f'Constraint validation for feature {self.tlf}: {constraint_expression}')
                self.tlf = tlf
                self.rf = constraint['RelatedFeature']
                self.exception_flag = False
                self.upd_flag = False
                constraint['Constraint'].name.check_cardinalities()
                constraint['Constraint'].name.set_mappings([])
                mappings = constraint['Constraint'].name.get_mappings()
                self.map_and_parse(mappings, constraint['Constraint'].name)

    def map_and_parse(self, mappings, constraint):
        done = False
        combinations = itertools.product(*mappings.values())
        for comb in combinations:
            done = True
            self.iterable['UnvalidatedFeatures'] = comb
            constraint.set_mappings(comb)
            constraint.parse()
        if done is False:
            constraint.set_mappings([])
            constraint.parse()

    def get_error_message(self, message):
        ol = self._tx_position_end - self._tx_position
        msg = ''.join((f'{message}.\n',
                       f'Error position: Line {get_location(self)["line"]},',
                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol}\n'))
        return msg

    def name_builder(self, feature, namespace, cardinality_type=None):
        feature_name = ''
        feature_list = {}
        feature_split = feature.split('.')
        if len(feature_split) == 1:
            features = []
            fcard = namespace[feature]['Fcard']
            if isinstance(fcard['Original'], str):
                features.append(feature)
            else:
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
                if cardinality_type != 'Gcard':
                    gcard = namespace[parent_feature]['Gcard']
                    features = self.filter_gcards(gcard, features)

            feature_list.update({part: features})
        return feature_list[feature_split[-1]]

    def filter_gcards(self, gcard, features):
        gcard_features = []

        for key, value in gcard.items():
            if key != 'Original':
                for raw_feature in features:
                    if len(raw_feature.split('.')[-1].split('_')) > 1:
                        feature = raw_feature.rsplit("_", 1)[0]
                    else:
                        feature = raw_feature
                    if feature == f'{key}.{value.split(".")[-1]}':
                        gcard_features.append(raw_feature)
        if len(gcard.keys()) > 1:
            features = gcard_features
        return features

    def get_unresolved_cardinalities(self, feature, namespace):
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

        sublayer = self.define_next_sublayer(fcards, gcards, namespace)
        return sublayer

    def get_unresolved_features(self, feature, namespace):
        result = {}
        for key, value in namespace.items():
            if key.split('.')[0] == feature:
                if value['Type'] not in [None, 'predefined'] and \
                        value['Value']['Original'] is None and \
                        len((value['Value'].keys())) == 1:
                    result.update({key: value['Type']})
        if result == {}:
            result = None
        else:
            for key in list(result.keys()):
                names = self.name_builder(key, namespace)
                if isinstance(names, list) and len(names) > 1:
                    for name in names:
                        result.update({name: result[key]})
                    result.pop(key, None)
                elif isinstance(names, list) and len(names) == 0:
                    result.pop(key, None)
        if result is not None:
            if result == {}:
                result = None
        return result

    def define_next_sublayer(self, fcards, gcards, namespace):
        result = {'Fcard': {}, 'Gcard': {}}
        cardinalities = np.unique(fcards + gcards)
        for card in cardinalities:
            card_split = card.split('.')
            find = ''
            for part in card_split:
                find = f'{find}.{part}' if find != '' else part
                if find in fcards:
                    result['Fcard'].update({find: namespace[find]['Fcard']})
                    break
                elif find in gcards:
                    result['Gcard'].update({find: namespace[find]['Gcard']})
                    break
        if result['Fcard'] == {} and result['Gcard'] == {}:
            result = None
        else:
            for cardinality_type in ['Fcard', 'Gcard']:
                for key in list(result[cardinality_type].keys()):
                    names = self.name_builder(key, namespace, cardinality_type)
                    if isinstance(names, list) and len(names) > 1:
                        for name in names:
                            result[cardinality_type].update({name: result[cardinality_type][key]})
                        result[cardinality_type].pop(key, None)
                    elif isinstance(names, list) and len(names) == 0:
                        result[cardinality_type].pop(key, None)
        if result is not None:
            if result['Fcard'] == {} and result['Gcard'] == {}:
                result = None
        return result

    def define_layer(self, top_level_feature):
        namespace = self.namespace[top_level_feature]['Features']

        sublayer = self.get_unresolved_cardinalities(top_level_feature, namespace)

        logging.info(f'Top-level feature {top_level_feature} cardinalities to configure: {sublayer}')
        if sublayer is None:
            sublayer = self.get_unresolved_features(top_level_feature, namespace)
            logging.info(f'Top-level feature {top_level_feature} features to configure: {sublayer}')
        return sublayer

    def update_feature(self, feature, new_value, top_level_features):
        update_type = new_value.keys()[0]
        top_level_features[feature][update_type] = new_value[update_type]
        return top_level_features

    def get_feature_childrens(self, feature):
        split = feature.split('.')
        tlf = self.get_original_name(split[0])
        childrens = []
        for subfeature in self.last_snap['Namespace'][tlf]['Features'].keys():
            if len(subfeature.split('.')) == len(split) + 1:
                childrens.append(subfeature)
        return childrens

    def cross_tree_dependencies_handler(self):
        logging.info('Detecting cross-tree constraints.')
        self.cross_tree_dependencies = []

        for tlf, tlf_value in self.namespace.items():
            for constraint in tlf_value['Constraints'].values():
                self.constraint_expression = f'{self.description.splitlines()[get_location(constraint["Constraint"])["line"] - 1].lstrip()}; '
                self.tlf = tlf
                self.rf = constraint['RelatedFeature']
                constraint['Constraint'].name.cross_tree_check(api=self)
        logging.info('Processing cross-tree dependencies: Starting')
        self.cross_tree_dependencies.sort()
        self.cross_tree = list(k for k, _ in itertools.groupby(self.cross_tree_dependencies))
        logging.info('Processing cross-tree dependencies: Done')

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
        features_from, features_to = ([] for i in range(2))

        for dep in cross_tree_dependencies:
            features_from.append(dep[0])
            features_to.append(dep[1])

        independent_features = [x for x in all_features if x not in features_from
                                and x not in features_to
                                and self.namespace[x]['Features'][x]['Abstract'] is None]

        # Create networkx graph object
        G = nx.DiGraph(cross_tree_dependencies)
        index = 0
        remove_dependencies = []
        self.cycles = {}
        # Find all cycles in graph. Create list of cycle dependencies.
        for cycle in nx.simple_cycles(G):
            index += 1
            self.cycles.update({f'cycle{index}': cycle})
            logging.debug(f'Cycle cycle{index} contain elements: {cycle}')
            for dep in cross_tree_dependencies:
                if dep[0] in cycle and dep[1] not in cycle:
                    dep[0] = f'cycle{index}'
                elif dep[0] not in cycle and dep[1] in cycle:
                    dep[1] = f'cycle{index}'
                elif dep[0] in cycle and dep[1] in cycle:
                    remove_dependencies.append(dep)
        for dep in remove_dependencies:
            try:
                cross_tree_dependencies.remove(dep)
            except ValueError:
                logging.debug(f'Dependency {dep} already removed.')

        # Perform topological sort for dependencies.
        res = self.topological_sort(cross_tree_dependencies)
        res.reverse()
        independent_features.reverse()
        result = res + independent_features

        # Add independent cycles
        index = 0
        for cycle in nx.simple_cycles(G):
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
        original_name = self.get_original_name(feature)
        original_card = self.namespace[original_name.split('.')[0]]['Features'][original_name][card_type]['Original']
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
                if re.match(r'(\d+\.\.)+\d+', lexem):
                    lexspl = lexem.split('..')
                    res.append([f'x>={lexspl[0]}', f'x<={lexspl[1]}'])
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
        return stages
        # Export both metamodel and model in .dot format for class diagram construction.
        # metamodel_export(mm, join(this_folder, 'output/metamodel.dot'))
        # model_export(model, join(this_folder, 'output/model.dot'))
