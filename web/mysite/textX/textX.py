import ast
import copy
import json
import itertools
import logging
import pandas as pd
import re

from collections import defaultdict
from functools import reduce
import networkx as nx
from os.path import join, dirname
from textx import metamodel_from_file, get_location
from textx.export import metamodel_export, model_export

# Global variables.
global_namespace = {}
abstract_namespace = {}
current_namespace = {}
current_path = ''
cross_tree_clafers = []
cross_tree_clafers_full = []
cross_tree_list = []
cycles = {}
keywords = ['abstract', 'all', 'assert', 'disj', 'else', 'enum',
            'if', 'in', 'lone', 'max', 'maximize', 'min',
            'minimize', 'mux', 'no', 'not', 'one', 'opt',
            'or', 'product', 'some', 'sum', 'then', 'xor', '_', 'fcard', 'gcard']
exception_flag = False
cross_tree_check = False
current_cross_tree = None
unvalidated_params = []
abstract_clafers = []
abstract_dependencies = {}
mappings = {}
mapping_iter_sum = 1
mapping_iter = 0
mapping_current = []
cardinality_flag = None
cardinalities_list = {}

# Logging configuration.
logging.basicConfig(format='%(levelname)s: %(asctime)s %(message)s', level=logging.DEBUG, datefmt='%m/%d/%Y %I:%M:%S %p')

class Expression(object):
    def __init__(self, **kwargs):
        self.expression = kwargs.pop('expressions')

    @property
    def value(self):
        # Evaluate variables in the order of definition
        res = []
        for a in self.expression:
            res.append(a.value)
        return res


class ExpressionElement(object):
    def __init__(self, **kwargs):

        # textX will pass in parent attribute used for parent-child
        # relationships. We can use it if we want to.
        self.parent = kwargs.get('parent', None)

        # We have 'op' attribute in all grammar rules
        self.op = kwargs['op']

        super(ExpressionElement, self).__init__()

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
        global exception_flag, cardinality_flag
        self.exception_flag = False
        for operator, statement, true_exp in zip(self.op[0::4], self.op[1::4], self.op[2::4]):
            if operator == 'if' and cross_tree_check:
                statement.value
                true_exp.value
                if len(self.op) > 3:
                    else_exp = self.op[3]
                    else_exp.value
                ret = None

            elif operator == 'if':
                logging.debug("Level 23 IF THEN ELSE statement.")
                # Take exception flag if it was still not taken.
                if exception_flag is False:
                    logging.debug("Level 23 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                # Perform IF expression check.
                ret = statement.value

                # Release global exception flag to perform THEN or ELSE expression.
                if self.exception_flag is True:
                    exception_flag = False
                cardinality_flag = None

                # If 'IF' expression was true, ther perform THEN expression.
                if ret:
                    ret = true_exp.value
                # If not, then perform ELSE expression if it exist. In the opposite case, do nothing.
                elif not ret:
                    if len(self.op) > 3:
                        else_exp = self.op[3]
                        ret = else_exp.value
                    else:
                        return None

                # Raise exception if result is False and exception flag was taken by this operation.
                else:
                    if self.exception_flag is True:
                        ol = self._tx_position_end - self._tx_position
                        msg = ''.join(('Expression operation IF returned not boolean',
                                       ' was not satisfied.\n',
                                       f'Error position: Line {get_location(self)["line"]},',
                                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                       f' Filename {get_location(self)["filename"]}\n'))
                        raise Exception(msg)

        # Double check to release global exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

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
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<=>' and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == '<=>':
                logging.debug("Level 22 boolean IFF operation")
                # Take exception flag if it was still not taken.
                if exception_flag is False:
                    logging.debug("Level 22 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                ret = self.op[0].value
                ret = (ret % 2 == 0) == (ret % operand.value == 0)

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation IFF ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
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
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '=>' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '=>':
                logging.debug("Level 21 boolean IMPLIES operation")
                # Take exception flag if it was still not taken.
                if exception_flag is False:
                    logging.debug("Level 21 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                ret = self.op[0].value
                ret = not(ret) or operand.value

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation IMPLIES ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
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
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '||' and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == '||':
                logging.debug("Level 20 boolean OR operation")
                # Take exception flag if it was still not taken.
                if exception_flag is False:
                    logging.debug("Level 20 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                ret = self.op[0].value
                ret = ret or operand.value

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation OR ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
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
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'xor' and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == 'xor':
                # Take exception flag if it was still not taken.
                if exception_flag is False:
                    logging.debug("Level 19 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                logging.debug("Level 19 boolean XOR operation")
                ret = self.op[0].value
                ret = bool(ret) ^ bool(operand.value)

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation XOR ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
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
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '&&' and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == '&&':
                logging.debug("Level 18 boolean AND operation")

                # Take exception flag if it was still not taken.
                if exception_flag is False:
                    logging.debug("Level 18 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                ret = self.op[0].value
                ret = ret and operand.value

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation AND ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
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
        global exception_flag
        self.exception_flag = False
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation == '!' and cross_tree_check:
                operand.value

            # Take exception flag if it was still not taken.
            if operation == '!':
                if exception_flag is False:
                    logging.debug("Level 14 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True

                logging.debug("Level 14 boolean NO operation")
                ret = not(operand.value)

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    raise Exception(f'Expression operation {operation} {operand.value} was not satisfied.')

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value

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
        global mapping_current
        global exception_flag
        self.exception_flag = False
        ret = False
        if mapping_iter == 0:
            mapping_current = []
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            # Take exception flag if it was still not taken.
            if exception_flag is False:
                logging.debug("Level 13 Exception flag.")
                exception_flag = True
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

                if operation in ['no', 'none', 'lone', 'one', 'some'] and cross_tree_check:
                    self.exception_flag = False
                    operand.value

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
            exception_flag = False

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
        ret = self.op[0].value
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):

            # Take exception flag if it was still not taken.
            if operation in ['<', '>', '==', '>=', '<=', '!=', 'in', 'not in']:
                if exception_flag is False:
                    logging.debug("Level 12 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
                logging.debug(f'{ret} {operation} {operand.value}')

            if operation in ['<', '>', '==', '>=', '<=', '!=', 'in', 'not in'] and cross_tree_check:
                self.exception_flag = False
                self.op[0].value
                operand.value

            elif operation == '<':
                ret = ret < operand.value
                logging.debug("Level 12 comparison < operation")

            elif operation == '>':
                ret = ret > operand.value
                logging.debug("Level 12 comparison > operation")

            elif operation == '==':
                ret = ret == operand.value
                logging.debug("Level 12 comparison == operation")

            elif operation == '>=':
                ret = ret >= operand.value
                logging.debug("Level 12 comparison >= operation")

            elif operation == '<=':
                ret = ret <= operand.value
                logging.debug("Level 12 comparison <= operation")

            elif operation == '!=':
                ret = ret != operand.value
                logging.debug("Level 12 comparison != operation")

            elif operation == 'in':
                ret = ret in operand.value
                logging.debug("Level 12 comparison in operation")

            elif operation == 'not in':
                ret = ret not in operand.value

        # Raise exception if result is False and exception flag was taken by this operation.
        if ret is False and self.exception_flag is True:
            ol = self._tx_position_end - self._tx_position
            msg = ''.join((f'Expression operation ({self.op[0].value} {operation} {operand.value})',
                           ' was not satisfied.\n',
                           f'Error position: Line {get_location(self)["line"]},',
                           f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                           f' Filename {get_location(self)["filename"]}\n'))
            raise Exception(msg)

        # Release exception flag.
        if self.exception_flag is True:
            exception_flag = False

        # If there are no this level operations, just perform lover-lever operation.
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec11(ExpressionElement):
    @property
    def value(self):
        """
        prec11 class performs requires and excludes operations.

        RETURN
        ret (variable type): previous level object if no prec11 operations are not presented in constraint
                            operation result in opposite case.
        """
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation in ['requires', 'excludes'] and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == 'requires':
                flag_left = False
                flag_right = False
                for element in model.elements:
                    if element.name == ret:
                        flag_left = True
                    elif element.name == operand.value:
                        flag_right = True
                if flag_left is False:
                    raise Exception(f'Left clafer {ret} does not exist')
                elif flag_right is False:
                    raise Exception(f'Required clafer {operand.value} does not exist')

            elif operation == 'excludes':
                flag_left = False
                flag_right = False
                for element in model.elements:
                    if element.name == ret:
                        flag_left = True
                    elif element.name == operand.value:
                        flag_right = True
                if flag_left is True and flag_right is True:
                    raise Exception(f'Clafers {ret} and {operand.value} could not exist at the same time.')
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '=' and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == '=':
                check = self.op[0].update
                logging.debug(f"Level 10 assignment operation: {check} {operation} {right_value} {cardinality_flag}")

                # Assign to complex path variable.
                if re.match(r'(\w+\.)+\w+', check) and cardinality_flag is None:
                    path = check.split('.')
                    path.append('value')

                    # Double check Python literal structures values if they are presented in str object.
                    try:
                        assign = right_value if type(right_value) != str else ast.literal_eval(right_value)
                    except ValueError:
                        assign = right_value

                    # Try find and assign value to variable in local namespace.
                    try:
                        global current_namespace
                        ret = current_namespace
                        for section in path:
                            ret = ret[section]
                        current_namespace = self.update_nested_dict(current_namespace, path, assign)

                    # If previous was not succeed, then try to do the same in global namespace.
                    except Exception:
                        global global_namespace
                        ret = global_namespace
                        for section in path:
                            ret = ret[section]
                        global_namespace = self.update_nested_dict(global_namespace, path, assign)
                        ret = global_namespace
                        for section in path:
                            ret = ret[section]

                # If cardinality flag was set, then update cardinality value instead of variable in namespace.
                elif re.match(r'(\w+\.)+\w+', check) and cardinality_flag == 'fcard':
                    from wizard.views import card_update
                    card_update('fcard', {check: right_value})

                # If path to variable is simple, just assign value to variable in local namespace.
                else:
                    try:
                        current_namespace[check]['value'] = right_value if type(right_value) != str else ast.literal_eval(right_value)
                    except ValueError:
                        current_namespace[check]['value'] = right_value
            else:
                raise Exception(f'Parameter {ret} is not defined.')
        return ret

    def find_in_obj(self, obj, condition, path=None):
        ''' generator finds full path to nested dict key when key is at an unknown level
            borrowed from http://stackoverflow.com/a/31625583/5456148'''
        if path is None:
            path = []

        # In case this is a list
        if isinstance(obj, list):
            for index, value in enumerate(obj):
                new_path = list(path)
                new_path.append(index)
                for result in self.find_in_obj(value, condition, path=new_path):
                    yield result

        # In case this is a dictionary
        if isinstance(obj, dict):
            for key, value in obj.items():
                new_path = list(path)
                new_path.append(key)
                for result in self.find_in_obj(value, condition, path=new_path):
                    yield result

                if condition == key:
                    new_path = list(path)
                    new_path.append(key)
                    yield new_path

    def set_nested_value(self, nested_dict, path_list, value):
        ''' add or update a value in a nested dict using passed list as path
            borrowed from http://stackoverflow.com/a/11918901/5456148'''
        cur = nested_dict
        logging.debug(f'Full path: {path_list}')
        for path_item in path_list[:-1]:
            try:
                cur = cur[path_item]
            except KeyError:
                cur = cur[path_item] = {}

        cur[path_list[-1]] = value
        logging.debug(f'Value was set {path_list[-1]} {value}')
        return nested_dict

    def update_nested_dict(self, nested_dict, path, updateval):
        ''' finds and updates values in nested dicts with find_in_dict(), set_nested_value()'''
        return self.set_nested_value(
            nested_dict,
            path,
            updateval
        )


class prec9(ExpressionElement):
    @property
    def value(self):
        """
        prec9 class performs addition and subtraction operations.

        RETURN
        ret (variable type): previous level object if no prec9 operations are not presented in constraint
                            operation result in opposite case.
        """
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in ['+', '-'] and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '+':
                logging.debug(f"Level 9 addition operation: {ret} {operation} {right_value}")
                ret += right_value
            elif operation == '-':
                logging.debug(f"Level 9 subtraction operation: {ret} {operation} {right_value}")
                ret -= right_value
        return ret

    @property
    def update(self):
        return self.op[0].update

class prec8(ExpressionElement):
    @property
    def value(self):
        """
        prec8 class performs miltiplication, division and remainer operations.

        RETURN
        ret (variable type): previous level object if no prec8 operations are not presented in constraint
                            operation result in opposite case.
        """
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in ['*', '/', '%'] and cross_tree_check:
                self.op[0].value
                operand.value

            elif operation == '*':
                logging.debug(f"Level 8 multiplication operation: {ret} {operation} {right_value}")
                ret *= right_value

            elif operation == '/':
                logging.debug(f"Level 8 division operation: {ret} {operation} {right_value}")
                ret /= right_value

            elif operation == '%':
                logging.debug(f"Level 9 remainder operation: {ret} {operation} {right_value}")
                ret %= right_value
        return ret

    @property
    def update(self):
        return self.op[0].update

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
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation in ['min', 'max'] and cross_tree_check:
                operand.value

            elif operation == 'min':
                logging.debug(f"Level 8 min operation: {operation}")
                ret = min(operand.value)

            elif operation == 'max':
                logging.debug(f"Level 8 max operation: {operation}")
                ret = max(operand.value)
        if len(self.op) == 1:
            ret = self.op[0].value

        return ret

    @property
    def update(self):
        return self.op[0].update

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
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation in ['sum', 'product', '#'] and cross_tree_check:
                operand.value

            elif operation == 'sum':
                logging.debug(f"Level 7 sum operation: {operation}")
                ret = sum(operand.value)

            elif operation == 'product':
                logging.debug(f"Level 7 product operation: {operation}")
                ret = reduce((lambda x, y: x * y), operand.value)

            elif operation == '#':
                logging.debug(f"Level 7 count operation: {operation}")
                ret = len(operand.value)
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

    @property
    def update(self):
        return self.op[0].update

class prec5(ExpressionElement):
    @property
    def value(self):
        # TODO prec5 - domain operation
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<:':
                pass
        return ret

    @property
    def update(self):
        return self.op[0].update

class prec4(ExpressionElement):
    @property
    def value(self):
        # TODO prec4 - range operation
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == ':>':
                pass
        return ret

    @property
    def update(self):
        return self.op[0].update

class prec3(ExpressionElement):
    @property
    def value(self):
        """
        prec3 class performs lists union operation.

        RETURN
        ret (variable type): previous level object if no prec3 operation is not presented in constraint
                            merged lists in opposite case.
        """
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in [',', '++'] and cross_tree_check:
                self.op[0].value
                operand.value

            # Perform list union if such operation exist.
            elif operation == ',' or operation == '++':
                if type(ret) == list and type(right_value) == list:
                    ret = list(set(ret) | set(right_value))
                elif type(ret) != list:
                    raise Exception(f'Parameter {ret} is not list.')
                elif type(right_value) != list:
                    raise Exception(f'Parameter {right_value} is not list.')

        return ret

    @property
    def update(self):
        return self.op[0].update

class prec2(ExpressionElement):
    @property
    def value(self):
        """
        prec2 class performs lists difference operation.

        RETURN
        ret (variable type): previous level object if no prec2 operation is not presented in constraint
                            merged lists in opposite case.
        """
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '--' and cross_tree_check:
                self.op[0].value
                operand.value

            # Perform list difference if such operation exist.
            elif operation == '--' and type(ret) == list and type(right_value) == list:
                ret = list(set(ret) - set(right_value))
            elif operation == '--' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '--' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')
        return ret

    @property
    def update(self):
        return self.op[0].update

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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '**' and cross_tree_check:
                self.op[0].value
                operand.value

            # Perform list merge (without duplicates) if such operation exist.
            elif operation == '**' and type(ret) == list and type(right_value) == list:
                ret = list(set(ret) & set(right_value))
            elif operation == '**' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '**' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')

        return ret

    @property
    def update(self):
        return self.op[0].update

class prec0(ExpressionElement):
    @property
    def value(self):
        """
        prec0 class performs lists concatenation ('..') and merging ('&') operations.

        RETURN
        op (variable type): term object if no prec0 operations are not presented in constraint
                            concatenated/merged lists in opposite case.
        """
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in ['..', '&'] and cross_tree_check:
                self.op[0].value
                operand.value

            # Perform list concatenation (with duplicates) if such operation exist.
            if operation == '..' and type(ret) == list and type(right_value) == list:
                ret = ret + right_value
            elif operation == '..' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '..' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')

            # Perform list merge (without duplicates) if such operation exist.
            if operation == '&' and type(ret) == list and type(right_value) == list:
                ret = list(set(ret) & set(right_value))
            elif operation == '&' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '&' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')
        return ret

    @property
    def update(self):
        return self.op[0].update


class term(ExpressionElement):
    @property
    def value(self):
        """
        Function to check type of op value (variable, number, string, etc.) and return it.

        RETURN
        op (variable type): variable, number, string, etc.
        """
        op = self.op
        global unvalidated_params, mapping_iter_sum

        # Cross-tree section finds whether variable is assigned to parent clafer or not.
        if cross_tree_check:
            if type(op) is str and op not in keywords and re.match(r'(\w+\.)+\w+', op):
                forbidden_flag = False
                path = op.split('.')

                # Check for cardinality keyword and remove it.
                if path[0] == 'fcard' or path[0] == 'gcard':
                    path = path[1:]

                # Forbid to add to cross-tree clafers own clafers written in full-path form.
                if path[0] == current_path.split('.')[0]:
                    forbidden_flag = True
                try:
                    res = current_namespace
                    for section in path:
                        res = res[section]
                except Exception:
                    try:
                        res = global_namespace
                        for section in path:
                            res = res[section]
                        if forbidden_flag is False:
                            global cross_tree_clafers, cross_tree_clafers_full
                            cross_tree_clafers.append([current_cross_tree, path[0]])
                            cross_tree_clafers_full.append(op)
                    except Exception:
                        logging.debug('ok')
        else:
            # In case of int or float value, just return it
            if type(op) in {int, float}:
                logging.debug(f"Operation object: {op} with type {type(op)}")
                return op

            # In case of ExpressionElement object (another constraint), return its validated value.
            elif isinstance(op, ExpressionElement):
                logging.debug(f"Operation object: {op} with value {type(op)}")
                return op.value

            # In case of top-level variable in global namespace return its value.
            # TODO same logic as in local namespace section
            elif op in global_namespace and global_namespace[op] is not None:
                logging.debug("Variable in global namespace.")
                return global_namespace[op]['value']

            # In case of simple name variable (without delimiters) in local namespace return its value.
            elif op in current_namespace and current_namespace[op] is not None:
                # Check for existing mappings
                logging.debug("Variable in local namespace")
                check = current_path + '.' + op
                logging.debug(f'Check: {check}, current path {current_path}')

                # If check was success then change basic path on current mapping value.
                if check in mappings.keys():
                    global mapping_iter_sum
                    mapping_iter_sum = len(mappings[check])
                    new_op = mappings[check][mapping_iter].split('.')[-1]
                    if new_op not in current_namespace.keys() or new_op == op:
                        path = mappings[check][mapping_iter].split('.')
                        res = global_namespace
                        for section in path:
                            res = res[section]
                        unvalidated_params.append(mappings[check][mapping_iter])
                        return res['value']
                    elif new_op in current_namespace.keys():
                        unvalidated_params.append(new_op)
                        return current_namespace[op]['value']

                # Double check if local namespace variable has no value (check in global namespace).
                if len(current_path.split('.')) > 1:
                    unvalidated_params.append(check)
                    if current_namespace[op]['value'] is None:
                        try:
                            res = global_namespace
                            path = check.split('.')
                            for section in path:
                                res = res[section]
                            return res['value']
                        except KeyError:
                            raise Exception(f'Such variable {op} does not exist')
                else:
                    unvalidated_params.append(check)
                return current_namespace[op]['value']

            # In case of bool value, just return it.
            elif type(op) is bool:
                return op

            # In case of string value, launch additional checks.
            elif type(op) is str and op not in keywords:
                logging.debug(f"String object: {op}")

                # If string pattern match list object ('{a, b}'), transform it to python list object.
                if re.match(r'\{.+\}', op):
                    op = op.replace('{', '').replace('}', '').replace(' ', '')
                    logging.debug("List object")
                    op = op.split(',')
                    for index, element in enumerate(op):
                        try:
                            op[index] = int(element)
                        except ValueError:
                            try:
                                op[index] = float(element)
                            except ValueError:
                                if element in current_namespace and current_namespace[element] is not None:
                                    op[index] = current_namespace[element]
                    logging.debug(op)

                # If string pattern match path to variable (splitted with dot delimiters: 'a.b.c')
                elif re.match(r'(\w+\.)+\w+', op):
                    # Check for mappings
                    if op in mappings.keys() and op.split('.')[0] not in ['fcard', 'gcard']:
                        mapping_iter_sum = len(mappings[op])
                        op = mappings[op][mapping_iter]
                    path = op.split('.')

                    # Perform feature of group cardinality search if first part of string is a appropriate keyword.
                    if path[0] == 'fcard' or path[0] == 'gcard':
                        global cardinality_flag
                        cardinality_flag = path[0]
                        from wizard.views import get_card
                        card = get_card()
                        path = path[1:]

                        # Rebuild path string without keyword.
                        f_p = ''
                        for section in path:
                            if f_p == '':
                                f_p = section
                            else:
                                f_p = f_p + '.' + section

                        # Build full path (Cardinalities are presented as full path records).
                        full_path = f_p
                        try:
                            res = card[cardinality_flag][full_path]
                        except KeyError:
                            raise Exception(f'No such key {full_path} in {card[cardinality_flag]}')

                    elif path[0] == 'childs':
                        path = path[1:]
                        res = global_namespace
                        for section in path:
                            res = res[section]
                        res = list(res.keys())

                    # If no cardinalities keyword presented in path, then try to find variable using this path.
                    else:

                        # Firstly in local namespace.
                        try:
                            unvalidated_params.append(op)
                            res = current_namespace
                            for section in path:
                                res = res[section]
                            res = res['value']

                        # Then in global.
                        except Exception:
                            res = global_namespace
                            for section in path:
                                res = res[section]
                            res = res['value']
                    op = res
                    logging.debug(res)
                return op
            else:
                raise Exception('Unknown variable "{}" at position {}'
                                .format(op, self._tx_position))

    @property
    def update(self):
        """
        Function to check, whether variable is present in local/global namespace.

        RETURN
        op (type = str): path to required variable in the namespace.
        """
        op = self.op
        global mapping_iter_sum

        # Check local namespace.
        if op in current_namespace:
            logging.debug("Namespace update")
            check = current_path + '.' + op
            logging.debug(f'Check: {check}, current path {current_path}')
            if check in mappings.keys():
                mapping_iter_sum = len(mappings[check])
                new_op = mappings[check][mapping_iter].split('.')[-1]
                if new_op not in current_namespace.keys() or new_op == op:
                    path = mappings[check][mapping_iter].split('.')
                    res = global_namespace
                    for section in path:
                        res = res[section]
                op = mappings[check][mapping_iter]
            return op

        # Check global namespace. Also this section finds cardinalities.
        elif re.match(r'(\w+\.)+\w+', op):
            if op in mappings.keys():
                mapping_iter_sum = len(mappings[op])
                op = mappings[op][mapping_iter]
            path = op.split('.')
            if path[0] == 'fcard' or path[0] == 'gcard':
                global cardinality_flag
                cardinality_flag = path[0]
                path = path[1:]
                op = ''
                for elem in path:
                    if op == '':
                        op = elem
                    else:
                        op = op + '.' + elem
            else:
                try:
                    res = current_namespace
                    for section in path:
                        res = res[section]
                    res = res['value']
                except Exception:
                    logging.info(f'Local Namespace does not contain variable {op}')
                    res = global_namespace
                    for section in path:
                        res = res[section]
            logging.debug(f'Return {op} value')
            return op
        else:
            raise Exception(f'Global namespace does not contain variable {op}')


class textX_API():

    def cname(self, o):
        """
        Function to return class name of object.

        INPUTS
        o: object to check.

        RETURN
        (type = string): object`s class name.
        """
        return o.__class__.__name__

    def constraint(self, constraint):
        """
        Perform constraint execution.
        """
        exp = constraint.name
        exp.value

    def root_clafer(self, clafer, namespace=None):
        """
        ! This method is recursive.

        Function to define clafers.

        INPUTS
        clafer (type = clafer): clafer to define.
        namespace (type = dict): top-level clafer namespace to fullfill.

        RETURN
        namespace (type = dict): clafer`s namespace. Only for not top-level clafers.
        """
        if namespace is None:
            return_trigger = False
        else:
            return_trigger = True
        logging.debug(f"This is Clafer: {clafer.name}")
        logging.debug(f"Is it abstract: {clafer.abstract}")
        logging.debug(f"Its group cardinality: {clafer.gcard}")
        logging.debug(f"Its feature cardinality: {clafer.fcard}")
        if clafer.super is not None:
            logging.debug(f"It has super instance: {clafer.super.value}")
        else:
            logging.debug(f"It has super instance: {clafer.super}")
        logging.debug(f"It has reference: {clafer.reference}")
        logging.debug(f"It has init expression: {clafer.init}")
        group = {}

        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer" and child1.reference is None:
                    group = self.root_clafer(child1, group)
                elif self.cname(child1) == "Clafer" and child1.reference is not None:
                    group = self.property_clafer(child1, group)

        clafer.namespace = group
        clafer.super_direct = []
        clafer.super_indirect = []
        logging.debug(f"Clafer namespace: {clafer.namespace}")
        if return_trigger:
            namespace[clafer.name] = group
            return namespace

    def get_model_cardinalities(self):
        """
        Function to find all cardinalities.

        RETURN
        fcard (type = dict): dict of feature cardinalities values.
        gcard (type = dict): dict of group cardinalities values.
        """
        fcard = {}
        gcard = {}
        for element in model.elements:
            if self.cname(element) == "Clafer":
                fcard.update(self.clafer_fcard(element))
                gcard.update(self.clafer_gcard(element))
        return fcard, gcard

    def clafer_fcard(self, clafer, prefix=None):
        """
        ! This method is recursive.

        Function to find all feature cardinalities.

        INPUTS
        clafer (type = clafer): clafer to check its feature cardinality.
        prefix (type = str): prefix to create full path.

        RETURN
        fcard (type = dict): dict of feature cardinalities values.
        """
        fcard = {}
        if prefix:
            name = prefix + '.' + clafer.name
        else:
            name = clafer.name
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer":
                    fcard.update(self.clafer_fcard(child1, name))
        if clafer.fcard:
            fcard.update({name: clafer.fcard})
        return fcard

    def clafer_gcard(self, clafer, prefix=None):
        """
        ! This method is recursive.

        Function to find all group cardinalities.

        INPUTS
        clafer (type = clafer): clafer to check its group cardinality.
        prefix (type = str): prefix to create full path.

        RETURN
        gcard (type = dict): dict of group cardinalities values.
        """
        gcard = {}
        if prefix:
            name = prefix + '.' + clafer.name
        else:
            name = clafer.name
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer":
                    gcard.update(self.clafer_gcard(child1, name))
        if clafer.gcard:
            gcard.update({name: clafer.gcard})
        return gcard

    def cardinality_solver(self, clafer, card_type: str, card_value: int):
        """
        Function to check, is target value allowed by cardinality record ot not.

        INPUTS
        clafer (type = clafer): clafer to check cardinality value (get it`s cardinality record).
        card_type (type = str): feature or group cardinality.
        card_value (type = int): cardinality value to check.

        RETURN
        True (type = bool): if check was successfull;
        Raise Exception if not.
        """
        fcard, gcard = self.get_model_cardinalities()
        if card_type == 'fcard':
            card = fcard[clafer]
        else:
            card = gcard[clafer]
        x = card_value
        res = []

        # Transform special cardinality values to simple constraint. Fullfill match groups.
        if card == '*':
            res.append('x>=0')
        elif card == '+' or card == 'or':
            res.append('x>=1')
        elif card == '?' or card == 'mux':
            res.append(['x>=0', 'x<=1'])
        elif card == 'xor':
            res.append('x==1')
        elif type(card) == int or re.match(r'^\d+$', card):
            res.append(f'x=={card}')
        else:
            strspl = card.split(',')
            for lexem in strspl:
                if re.match(r'(\d+\.\.)+\d+', lexem):
                    lexspl = lexem.split('..')
                    subres = []
                    subres.append(f'x>={lexspl[0]}')
                    subres.append(f'x<={lexspl[1]}')
                    res.append(subres)
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
        if result:
            logging.debug(f'Result: {x} lies in interval {card}')
            return True
        else:
            return Exception(f'Result: {x} not lies in interval {card}')

    def get_abstract_clafers(self):
        global abstract_clafers
        return abstract_clafers

    def update_abstract_clafers(self):
        """
        Function to find all abstract clafers.
        """
        global abstract_clafers
        for element in model.elements:
            if self.cname(element) == "Clafer":
                for element in self.clafer_abstract(element):
                    abstract_clafers.append(element)

    def clafer_abstract(self, clafer, prefix=None):
        """
        ! This method is recursive.

        Function to find all abstract clafers.

        INPUTS
        clafer (type = clafer): top-level clafer to check for abstract.
        prefix (type = str): prefix to create full path.

        RETURN
        abstr_clafers (type = list): list of abstract clafers.
        """
        abstr_clafers = []
        if prefix:
            name = prefix + '.' + clafer.name
        else:
            name = clafer.name
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer":
                    res = self.clafer_abstract(child1, name)
                    abstr_clafers = abstr_clafers + res
        if clafer.abstract:
            abstr_clafers.append(name)
        return abstr_clafers

    def fullfill_abstract_dependencies(self):
        """
        Function to fullfill abstract clafer dependencies.
        This depencendies are presented as dict(abstract clafer: [list of clafers inherited from it])
        """
        global abstract_dependencies, model
        for clafer in abstract_clafers:
            res = []
            for element in model.elements:
                if self.cname(element) == "Clafer":
                    for elem in self.find_abstract(element, clafer):
                        res.append(elem)
            abstract_dependencies.update({clafer: res})
        logging.info(f'Abstract dependencies fullfiled: {abstract_dependencies}')

    def find_abstract(self, clafer, abstract, prefix=None):
        """
        ! This method is recursive.

        Function to find all clafers with concrete abstract clafer.

        INPUTS
        clafer (type = clafer): clafer to check for abstract.
        abstract (type = clafer): abstract clafer to check.

        RETURN
        abstr_clafers (type = list): list of clafers with concrete abstract clafer.
        """
        abstr_clafers = []
        if prefix:
            name = prefix + '.' + clafer.name
        else:
            name = clafer.name
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer":
                    res = self.find_abstract(child1, abstract, name)
                    abstr_clafers = abstr_clafers + res
        if abstract in clafer.super_direct or abstract in clafer.super_indirect:
            abstr_clafers.append(name)
        return abstr_clafers

    def get_abstract_dependencies(self):
        global abstract_dependencies
        return abstract_dependencies

    def get_clafer_type(self, clafer: str):
        """
        Function to find and return specified clafer type.

        INPUTS
        clafer: clafer name.

        RETURN
        type (type = str): clafer type if clafer is parametric.
        unspecified : if clafer is group.
        """
        global global_namespace
        path = clafer.split('.')
        gn_copy = global_namespace
        try:
            for section in path:
                gn_copy = gn_copy[section]
        except Exception as e:
            logging.info(f'An exception was occured {e}')

        if 'type' in gn_copy.keys():
            return gn_copy['type']
        else:
            return 'Group clafer'


    def topological_sort(self, dependency_pairs):
        """
        Subfunction to define sequence of clafers to validate. The analogue of directed graph path.

        INPUTS
        dependency_pairs: list of cross-tree dependencies pairs.

        RETURN
        ordered (type = list): sequence of independent clafers to validate.
        cyclic (type = list): list of cyclic clafers.
        """
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
        cyclic = [n for n, heads in num_heads.items() if heads]
        return ordered, cyclic


    def staging(self, cross_tree_dependencies: list):
        """
        Function to define sequence of clafers to validate.

        INPUTS
        cross_tree_dependencies: list of cross-tree dependencies.

        RETURN
        ret_val (type = list): sequence of clafers to validate.
        """
        global cycles, cross_tree_list

        # Define cross-tree and independent clafers
        ctl = []
        all_clafers = list(global_namespace.keys())
        cross_clafers = []
        for dep in cross_tree_dependencies:
            cross_clafers.append(dep[0])
            cross_clafers.append(dep[1])
            ctl.append(dep[1])
        cross_tree_list = list(dict.fromkeys(ctl))
        cross_clafers = list(dict.fromkeys(cross_clafers))
        s = set(cross_clafers)
        independent_clafers = [x for x in all_clafers if x not in s]

        # Create networkx graph object
        G = nx.DiGraph(cross_tree_dependencies)
        index = 0
        new_dep = []
        cycled = []

        # Find all cycles in graph
        for cycle in nx.simple_cycles(G):
            index += 1
            logging.debug(f'Cycle cycle{index} contain elements: {cycle}')
            cycles[f'cycle{index}'] = cycle
            for element in cycle:
                cycled.append(element)
                for dep in cross_tree_dependencies:
                    if element == dep[0] and dep[1] not in cycle:
                        new_dep.append([f'cycle{index}', dep[1]])
                    elif element == dep[1] and dep[0] not in cycle:
                        new_dep.append([dep[0], f'cycle{index}'])

        # Remove cycle dependencies duplicates
        new_k = []
        for elem in new_dep:
            if elem not in new_k:
                new_k.append(elem)
        new_dep = new_k
        new_dep1 = cross_tree_dependencies
        new_dep2 = []

        # Copy all dependencies not related to any cycle
        for dep in new_dep1:
            flag = False
            for element in cycled:
                if element in dep:
                    flag = True
            if flag is False:
                new_dep2.append(dep)

        # Add cardinalities
        fcard, gcard = self.get_model_cardinalities()
        fcardinalities = [{'fcard': fcard}]
        gcardinalities = [{'gcard': gcard}]

        # Combine cycle and not-cycle dependencies to form final list
        res = new_dep2 + new_dep
        res = self.topological_sort(res)
        result = res[0] + independent_clafers

        # Add independent cycles
        index = 0
        for cycle in nx.simple_cycles(G):
            index += 1
            if f'cycle{index}' not in result:
                result.append(f'cycle{index}')
        # result.reverse()
        ret_val = fcardinalities + gcardinalities + result
        logging.info(f'There are {len(res[0])} stages for cross-tree dependencies: {res[0]}')
        logging.info(f'Cycled clafers: {cycled}')
        logging.info(f'Additional independent clafers: {independent_clafers}')
        logging.info(f'Final result: {result}')
        return ret_val

    def recursive_items(self, dictionary: dict, prefix=None):
        """
        ! This method is recursive.

        Function to read values from dictionary.

        INPUTS
        dictionary: dictionary to read value from.
        prefix (type = str): prefix to create full path for nested clafers.

        RETURN
        (type = list): tuple of key-value records.
        """
        for key, value in dictionary.items():
            if type(value) is dict:
                if 'type' in value.keys() and 'value' in value.keys():
                    if not prefix:
                        yield (key, value)
                    else:
                        yield (prefix + "." + key, value)
                else:
                    if prefix:
                        prefix_upd = prefix + "." + key
                    else:
                        prefix_upd = key
                    yield from self.recursive_items(value, prefix=prefix_upd)
            else:
                if not prefix:
                    yield (key, value)
                else:
                    yield (prefix + "." + key, value)

    def update_namespace(self, new: dict):
        """
        Function to update global namespace records.

        INPUTS
        new: dict with values to update.
        """
        global global_namespace
        inner = global_namespace

        for k, v in new.items():
            if re.match(r'(\w+\.)+\w+', k):
                k = k.split('.')

            # Coppy top-level records if mapping exist.
            if k[0].split('_')[0] in inner.keys() and k[0] not in inner.keys():
                inner[k[0]] = copy.deepcopy(inner[k[0].split('_')[0]])

            for key, value in inner.items():
                # Update top-level key value
                if k == key:
                    if inner[k]['type'] == 'boolean':
                        v = json.loads(v.lower())
                    inner[k].update({'value': v})
                    break
                elif k[0] == key:
                    inner_copy = inner
                    for section in k[:-1]:
                        inner_copy = inner_copy[section]

                    # If fcard == 1.
                    if k[-1] in inner_copy.keys():
                        if inner_copy[k[-1]]['type'] == 'boolean':
                            v = json.loads(v.lower())
                        inner_copy[k[-1]].update({'value': v})

                    # If fcard != 1.
                    else:
                        original = k[-1].split('_')[0]
                        if 'type' in inner_copy[original].keys():
                            if inner_copy[original]['type'] == 'boolean':
                                v = json.loads(v.lower())
                            inner_copy[k[-1]] = {'value': v, 'type': inner_copy[original]['type']}
                        else:
                            inner_copy[k[-1]] = copy.deepcopy(v)

    def read_keys(self):
        """
        Function to read all keys in global namespace.

        RETURN
        keys (type = dict): dict(top-level key: all nested keys).
        """
        top_keys = global_namespace.keys()
        keys = {}
        for topkey in top_keys:
            logging.debug(topkey)
            subkey = []
            for key, value in self.recursive_items(global_namespace[topkey]):
                subkey.append({key: value})
            keys[topkey] = subkey
        return keys

    def read_certain_key(self, path: str, only_childs: bool):
        """
        ! This method is only used to read group cardinalities (including inherited from abstract clafers).

        Function to read values from global namespace.

        INPUTS
        path: path to read value from.
        only_childs: flag to return only direct childs.

        RETURN
        key (type = dict): read value.
        """
        abs_flag = False
        path_flag = True
        path_check = global_namespace
        check = ''
        logging.debug(f'Read path {path}')
        for part in path.split('.'):
            try:
                path_check = path_check[part]
            except KeyError:
                logging.debug(f'No such key in namespace {path}.')
                logging.debug(f'Global namespace: {global_namespace}')
                path_flag = False
            if check == '':
                check = part
            else:
                check = check + '.' + part
            for dep in abstract_dependencies.keys():
                if check.split('_')[0] in abstract_dependencies[dep]:
                    check = dep
            if check in abstract_clafers:
                abs_flag = True
        key = {}
        if path_flag is True:
            ns = global_namespace
            # logging.debug(f'Take Global namespace {ns}')
            p = path
        elif path_flag is False and abs_flag is True:
            ns = abstract_namespace
            p = check
            logging.debug(f'Take Abstract namespace {ns}')
        else:
            raise Exception(f'No such clafer exist {path}')
        subkey = []
        path_s = p.split('.')
        for elem in path_s:
            ns = ns[elem]
        if only_childs:
            for k in ns.keys():
                subkey.append(k)
        else:
            for k, v in self.recursive_items(ns):
                subkey.append({k: v})
        key[path] = subkey
        return key

    def get_cycle_keys(self):
        return cycles

    def get_namespace(self):
        return global_namespace

    def get_mappings(self):
        return mappings

    def write_to_keys(self, input_data=None):
        """
        Update global namespace with data from web interface.
        """
        for k, v in input_data.items():
            self.update_namespace(new={k: v})

    def group_clafer(self, clafer, namespace: dict):
        """
        ! This method is recursive.
        ! Group clafer is a clafer that does not refers to any type. This clafer could have childs.

        Function to update parent namespace with the group clafer.

        INPUTS
        clafer (type = textX.clafer): clafer to define.
        namespace: parent namespace.

        RETURN
        namespace (type = dict): parent namespace with this clafer record.
        """

        logging.debug(f"This is group Clafer: {clafer.name}")
        group = {}
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer" and child1.reference is None:
                    self.group_clafer(child1, group)
                elif self.cname(child1) == "Clafer" and child1.reference is not None:
                    self.property_clafer(child1, group)
        namespace[clafer.name] = group
        clafer.namespace = group
        return namespace

    def property_clafer(self, clafer, namespace: dict):
        """
        ! Property clafer is a clafer that refers to some type. This clafer has no childs.

        Function to update parent namespace with the property clafer.

        INPUTS
        clafer (type = textX.clafer): clafer to define.
        namespace: parent namespace.

        RETURN
        namespace (type = dict): parent namespace with this clafer record.
        """
        logging.debug(f"This is property Clafer: {clafer.name}")
        logging.debug(f"It has reference: {clafer.reference}")
        sub = {'value': None, 'type': clafer.reference.value}
        clafer.super_direct = []
        clafer.super_indirect = []
        namespace[clafer.name] = sub
        return namespace

    def root_clafer_constraints(self, clafer, isroot, gcard_check=True):
        """
        ! This method is recursive.

        Find and validate all clafer and his childs constraints.

        INPUTS
        clafer (type = textX.clafer): clafer to validation.
        isroot (type = bool): flag to reset current_path variable.
        Path is built according to clafer nested structure.
        gcard_check (type = bool): flag to perform gcard check.

        RETURN
        clafer.namespace (type = dict): clafer namespace after constraints validation.
        """
        logging.info(f'Clafer {clafer.name} constraint validation.')
        global global_namespace, current_namespace, unvalidated_params, current_path

        # According to isroot flag update current_path variable.
        if isroot is True:
            current_path = clafer.name
        else:
            local_path = current_path
            current_path = current_path + '.' + clafer.name

        # According to gcard_check flag perform gcard check (is this clafer is valid gcard choice).
        from wizard.views import check_gcard
        if gcard_check is False:
            check = check_gcard(current_path)
            logging.debug(f'GC_CHECK: {check}')
        else:
            check = True

        if check is True:
            current_namespace = clafer.namespace
            counter = 0
            for child in clafer.nested:
                for child1 in child.child:
                    unvalidated_params = []

                    # Perform constraint validation using clafer mappings if such are exist.
                    if self.cname(child1) == "Constraint":
                        counter += 1
                        global mapping_iter, mapping_iter_sum, cardinality_flag
                        cardinality_flag = None
                        mapping_iter = 0
                        mapping_iter_sum = 1
                        logging.debug(f'Constraint name: {child1.name}')
                        while mapping_iter < mapping_iter_sum:
                            unvalidated_params = []
                            child1.name.value
                            mapping_iter += 1
                        clafer.namespace = current_namespace
                        if isroot is True:
                            global_namespace[clafer.name] = current_namespace

                    # Perform constraint validation for nested clafers.
                    elif self.cname(child1) == 'Clafer' and isinstance(child1.reference, type(None)):
                        logging.info(f'CLAFR {clafer.namespace}')
                        clafer.namespace[child1.name].update(self.root_clafer_constraints(child1, False, gcard_check))
                        current_namespace = clafer.namespace

            current_namespace = {}
            logging.info(f'For clafer {clafer.name} there is/are {counter} constraint expression(s) evaluated.')
            logging.debug(f'Clafer namespace: {clafer.namespace}')

        # Reset current_path variable.
        if isroot is True:
            current_path = ''
        else:
            current_path = local_path
        return clafer.namespace

    def cardinalities_upd(self, card):
        global cardinalities_list
        cardinalities_list = card

    def get_card(self):
        global cardinalities_list
        return cardinalities_list

    def get_cross_tree_list(self):
        global cross_tree_list, cross_tree_clafers_full
        return cross_tree_list, cross_tree_clafers_full

    def super_clafer(self, clafer):
        """
        ! This method is recursive.

        Find and fullfill all super relations in the model.

        INPUTS
        clafer (type = textX.clafer): clafer to check for super relation.
        """
        if clafer.super is not None:
            for element in model.elements:
                if element.name == clafer.super.value:
                    super_copy = copy.deepcopy(element.namespace)
                    clafer.namespace.update(super_copy)
                    if len(element.nested) > 0:
                        # If clafer has no childs, just copy super clafer nested elements.
                        if clafer.nested == []:
                            clafer.nested = element.nested
                            repl = []
                            for child in element.nested:
                                for child1 in child.child:
                                    repl.append(child1)
                                child.child = repl
                        # If clafer has childs, merge both clafers nested elements.
                        else:
                            for child in clafer.nested:
                                for child1 in element.nested:
                                    for child2 in child1.child:
                                        if child2 not in child.child:
                                            logging.debug(f'Parent constraint {child2} was merged to {child}')
                                            child.child.append(child2)
                    # Append all direct and indirect super relations.
                    # Note, that direct relation is super relation of this clafer.
                    # While indirect relation is direct super relation of super clafer and so on.
                    clafer.super_direct.append(element.name)
                    if element.super_direct != []:
                        for rel in element.super_direct:
                            clafer.super_indirect.append(rel)
                        for rel in element.super_indirect:
                            clafer.super_indirect.append(rel)
                    logging.info(f'For clafer {clafer.name} super clafer namespace was merged')
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == "Clafer":
                    self.super_clafer(child1)

    def reset_exception_flag(self):
        global exception_flag
        exception_flag = False
        logging.debug(f'Global exception flag was reset: {exception_flag}')

    def get_unvalidated_params(self):
        global unvalidated_params
        return unvalidated_params

    def to_json(self):
        """
        ! This method will be removed.

        Create dict object with fullfilled values

        RETURN
        result (type = dict): copies of global namespace records or element namespace.
        """
        result = {}
        for element in model.elements:
            if self.cname(element) == "Clafer" and element.abstract is None:
                if element.reference is not None:
                    result[element.name] = global_namespace[element.name]
                else:
                    result[element.name] = element.namespace
        return result

    def mapping(self, original, copy):
        """
        ! This method is only used for clafers with cardinalities != 1

        Create new mapping instance. This mapping will be used for constraints validation.
        For example, fcard (a) = 2, then 2 clafers will be created -> a0, a1.
        Mapping presented as a dict: {a: [a0, a1]}
        For constraint [a > 5] two constraints will be validated instead this one:
        [a0 > 5]
        [a1 > 5]

        INPUTS
        original: original clafer name.
        copy: copy of original clafer name with added suffix _x, where x is sequentional mapping number.
        """
        global mappings
        if original not in mappings.keys():
            mappings.update({original: []})
        mappings[original].append(copy)
        mappings[original] = list(dict.fromkeys(mappings[original]))
        logging.debug(f'New mapping was added: {original}: {copy}')

    def update_global_namespace(self, key: str, value: int):
        """
        ! Method is used only to update filled on web interface cardinalities form.

        Update global namespace record.

        INPUTS
        key: cardinality identification name.
        value: cardinality value.
        """
        global global_namespace
        k_s = key.split('_')
        if k_s[0] == 'fcard' and len(k_s[1].split('.')) >= 1 and value > 1:
            ret = global_namespace
            path = k_s[1].split('.')
            for section in path[:-1]:
                ret = ret[section]
            logging.debug(f'Subkeys {ret.keys()}. Path {path[-1]}. Full {path}.')
            if path[-1] in ret.keys():
                for index in range(0, value):
                    ret.update({path[-1] + '_' + str(index): copy.deepcopy(ret[path[-1]])})
                    logging.info(f'Global namespace was mapped {index + 1} of {value} times for clafer {key}')

    def validate_clafer(self, clafer: str):
        """
        Perform clafer constraints validation.

        INPUTS
        clafer: name of clafer to validate constraints.

        RETURN:
        True (type = bool): if clafer was successfully validated;
        e (type = Exception): if not.
        """
        global exception_flag, mappings, current_path, unvalidated_params
        current_path = ''
        try:
            for element in model.elements:
                if self.cname(element) == "Constraint":
                    exception_flag = False
                    self.constraint(element)
            for element in model.elements:
                if self.cname(element) == "Clafer" and element.name == clafer:
                    exception_flag = False
                    self.root_clafer_constraints(element, True, False)
            current_path = ''
            unvalidated_params = []
            return True
        except Exception as e:
            logging.info(f'! Exception: {e}.')
            current_path = ''
            return e

    def reset_global_variables(self):
        """
        Clear all shared variables.
        """
        global global_namespace, current_namespace, current_path, cross_tree_clafers, cross_tree_list
        global cycles, exception_flag, cross_tree_check, current_cross_tree, unvalidated_params
        global abstract_clafers, abstract_dependencies, mappings, mapping_iter_sum
        global mapping_iter, cardinalities_list, abstract_namespace, cross_tree_clafers_full
        global_namespace = {}
        abstract_namespace = {}
        current_namespace = {}
        current_path = ''
        cross_tree_clafers = []
        cross_tree_clafers_full = []
        cross_tree_list = []
        cycles = {}
        exception_flag = False
        cross_tree_check = False
        current_cross_tree = None
        unvalidated_params = []
        abstract_clafers = []
        abstract_dependencies = {}
        mappings = {}
        mapping_iter_sum = 1
        mapping_iter = 0
        cardinalities_list = {}

    def clear_json_trash(self, dictionary: dict):
        """
        ! This method is recursive.

        Clear global namespace from unfilled fields.

        INPUTS
        dictionary: dict object to find unfilled fields.

        RETURN
        dictionary: (type = dict): cleaned input dictionary.
        """
        rm_keys = []
        for key, value in dictionary.items():
            if isinstance(value, dict) and 'value' not in value.keys():
                dictionary[key] = self.clear_json_trash(value)
                if dictionary[key] == {} or dictionary[key] is None:
                    rm_keys.append(key)
            elif isinstance(value, dict) and 'value' in value.keys():
                if value['value'] is None:
                    rm_keys.append(key)
                else:
                    dictionary[key] = value['value']
        for key in rm_keys:
            dictionary.pop(key, None)
        return dictionary

    def preprocess_json(self, dictionary: dict):
        """
        ! This method is recursive.

        Preprocess global namespace.

        INPUTS
        dictionary: dict object to find unfilled fields.

        RETURN
        dictionary: (type = dict): processed input dictionary.
        """
        for key, value in dictionary.items():
            if isinstance(value, dict) and 'value' not in value.keys():
                dictionary[key] = self.preprocess_json(value)
            elif isinstance(value, dict) and 'value' in value.keys():
                if value['type'] == 'array' or value['type'] == 'integerArray' or value['type'] == 'floatArray':
                    value['value'] = value['value'].split(',')
                if value['type'] == 'integerArray':
                    ret = []
                    for subvalue in value['value']:
                        ret.append(int(subvalue))
                    value['value'] = ret
                elif value['type'] == 'floatArray':
                    ret = []
                    for subvalue in value['value']:
                        ret.append(float(subvalue))
                    value['value'] = ret
        return dictionary

    def save_json(self):
        """
        Prepare and save final result.

        RETURN
        res (type = dict): final result
        """

        global global_namespace
        preprint = copy.deepcopy(global_namespace)
        preprocessed_preprint = self.clear_json_trash(preprint)
        res = self.preprocess_json(preprocessed_preprint)
        logging.info('Final result was successfully created.')
        logging.debug(f'Final Model {res}')

        with open('test.json', 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=4)
        return res

    def define_clafers(self):
        """
        Calls clafer definition function for all clafers in the model.
        """
        global model
        for element in model.elements:
            if self.cname(element) == "Clafer":
                self.root_clafer(element)
        logging.info('All clafers are successfully defined.')

    def define_super_relations(self):
        """
        Calls super relations definition function for all clafers in the modell.
        """
        global model
        for element in model.elements:
            if self.cname(element) == "Clafer":
                self.super_clafer(element)
        logging.info('For all clafers super relations are defined.')

    def initialize_global_namespace(self):
        """
        Create dict with the nested structure of model.
        """
        global model
        for element in model.elements:
            if self.cname(element) == "Clafer" and element.abstract is None:
                global_namespace[element.name] = element.namespace
        logging.info('Global namespace successfully fullfilled.')

    def cross_tree_check(self):
        """
        Find all cross-tree dependencies in model constraints.
        """
        global cross_tree_check, exception_flag, current_cross_tree
        cross_tree_check = True
        for element in model.elements:
            exception_flag = False
            if self.cname(element) == "Constraint":
                self.constraint(element)
        for element in model.elements:
            exception_flag = False
            if self.cname(element) == "Clafer" and element.abstract is None:
                current_cross_tree = element.name
                self.root_clafer_constraints(element, True)
        logging.info('Model was successfully checked for cross-tree dependencies.')

    def initialize_product(self, description: dict):
        """
        Performs initial model preprocessing.

        INPUTS
        description: model description from web interface or file.

        RETURN
        stages (type = list): sequence of clafer to perform constraint solving.
        """
        global model, cross_tree_check, cross_tree_clafers

        # Read language grammar and create textX metamodel object from it.
        this_folder = dirname(__file__)
        mm = metamodel_from_file(f'{this_folder}/grammar.tx',
                                 classes=[prec0, prec1, prec2, prec3,
                                          prec4, prec5, prec6, prec7, prec8,
                                          prec9, prec10, prec11, prec12, prec13,
                                          prec14, prec15, prec16, prec17,
                                          prec18, prec19, prec20, prec21, prec22, prec23, term],
                                 autokwd=True)

        # Reset shared info variables and create textX model object from description.
        self.reset_global_variables()
        model = mm.model_from_str(description)

        # Export both metamodel and model in .dot format for class diagram construction.
        metamodel_export(mm, join(this_folder, 'metamodel.dot'))
        model_export(model, join(this_folder, 'model.dot'))

        # Perform basic initialization
        self.define_clafers()
        self.define_super_relations()

        # Define all abstract clafers and dependencies to them.
        self.update_abstract_clafers()
        self.fullfill_abstract_dependencies()

        # Initialize global namespace and perform cross-tree check.
        self.initialize_global_namespace()
        self.cross_tree_check()

        # Define constraint solving sequence
        cross_tree_clafers.sort()
        res_cross_tree = list(k for k, _ in itertools.groupby(cross_tree_clafers))
        stages = self.staging(res_cross_tree)
        cross_tree_check = False
        return stages

    def solve_constraints(self):
        """
        ! This method is only used with automatic product filling (no web interface).

        Performs solving for all types of constraints.
        """
        global exception_flag
        for element in model.elements:
            if self.cname(element) == "Constraint":
                exception_flag = False
                self.constraint(element)
        for element in model.elements:
            if self.cname(element) == "Clafer" and element.abstract is None:
                exception_flag = False
                self.root_clafer_constraints(element, True)

        logging.info(json.dumps(self.to_json(model), sort_keys=True, indent=4))
        with open('test.json', 'w', encoding='utf-8') as f:
            json.dump(self.to_json(model), f, ensure_ascii=False, indent=4)


if __name__ == '__main__':
    pass
