import ast
import copy
import json
import itertools
import logging
import pandas as pd
import pickle
import pprint
import re

from collections import defaultdict
from deepdiff import DeepDiff
from functools import reduce
import networkx as nx
from os.path import join, dirname, abspath
from textx import metamodel_from_file, get_location
from textx.export import metamodel_export, model_export

# Global variables.
wfml_data = {}
initial_data = {}
keywords = ['abstract', 'all', 'assert', 'disj', 'else', 'enum',
            'if', 'in', 'lone', 'max', 'maximize', 'min',
            'minimize', 'mux', 'no', 'not', 'one', 'opt',
            'or', 'product', 'some', 'sum', 'then', 'xor', '_', 'fcard', 'gcard']

# Logging configuration.
logging.basicConfig(format='%(levelname)s: %(asctime)s %(message)s', level=logging.DEBUG, datefmt='%m/%d/%Y %I:%M:%S %p')


class ExpressionElement(object):
    def __init__(self, **kwargs):

        # textX will pass in parent attribute used for parent-child
        # relationships. We can use it if we want to.
        self.parent = kwargs.get('parent', None)

        # We have 'op' attribute in all grammar rules
        self.op = kwargs['op']

        super(ExpressionElement, self).__init__()

    def update_wfml_data(self, path: str, data, duplicates=True):
        global wfml_data
        full_path = path
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.')[:-1]:
                wfml_data_section = wfml_data_section[section]
            path = path.split('.')[-1]
        else:
            wfml_data_section = wfml_data

        if type(wfml_data_section[path]) is dict:
            wfml_data_section[path].update(data)
        elif type(wfml_data_section[path]) is list and duplicates is True:
            wfml_data_section[path].append(data)
        elif type(wfml_data_section[path]) is list and duplicates is False:
            if data not in wfml_data_section[path]:
                wfml_data_section[path].append(data)
        else:
            wfml_data_section[path] = data
        logging.debug(f'WFML data for {full_path} was updated. New value is {data}.')

    def reset_wfml_data(self, path: str):
        global wfml_data, initial_data
        full_path = path
        wfml_data_init = initial_data
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.')[:-1]:
                wfml_data_section = wfml_data_section[section]
                wfml_data_init = wfml_data_init[section]
            path = path.split('.')[-1]
        else:
            wfml_data_section = wfml_data

        wfml_data_section[path] = copy.deepcopy(wfml_data_init[path])
        logging.debug(f'WFML data for {full_path} was reset to {wfml_data_section[path]}.')
        logging.debug(f'{self.get_wfml_data(full_path)}')

    def get_wfml_data(self, path: str):
        global wfml_data
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.'):
                wfml_data_section = wfml_data_section[section]
        else:
            wfml_data_section = wfml_data[path]
        return wfml_data_section

    def mapping_check(self):
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.mapping_check()

    def cross_tree_check(self):
        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.cross_tree_check()

    def initial_super_reference_check(self):
        return self.op[0].initial_super_reference_check()

    def initial_type_reference_check(self):
        return self.op[0].initial_type_reference_check()

    @property
    def fcard_validation(self):
        ret = self.op[0].fcard_validation
        return ret

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
        self.exception_flag = False
        for operator, statement, true_exp in zip(self.op[0::4], self.op[1::4], self.op[2::4]):
            if operator == 'if':
                logging.debug("Level 23 IF THEN ELSE statement.")
                # Take exception flag if it was still not taken.
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 23 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
                    self.exception_flag = True

                # Perform IF expression check.
                ret = statement.value

                # Release global exception flag to perform THEN or ELSE expression.
                if self.exception_flag is True:
                    self.update_wfml_data('Flags.Exception', False)
                self.reset_wfml_data('Flags.Cardinality')

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
            self.update_wfml_data('Flags.Exception', False)

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
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<=>':
                logging.debug("Level 22 boolean IFF operation")
                # Take exception flag if it was still not taken.
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 22 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
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
            self.update_wfml_data('Flags.Exception', False)

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
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '=>':
                logging.debug("Level 21 boolean IMPLIES operation")
                # Take exception flag if it was still not taken.
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 21 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
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
            self.update_wfml_data('Flags.Exception', False)

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
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '||':
                logging.debug("Level 20 boolean OR operation")
                # Take exception flag if it was still not taken.
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 20 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
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
            self.update_wfml_data('Flags.Exception', False)

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
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'xor':
                # Take exception flag if it was still not taken.
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 19 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
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
            self.update_wfml_data('Flags.Exception', False)

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
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '&&':
                logging.debug("Level 18 boolean AND operation")

                # Take exception flag if it was still not taken.
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 18 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
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
            self.update_wfml_data('Flags.Exception', False)

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
        self.exception_flag = False
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            # Take exception flag if it was still not taken.
            if operation == '!':
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 14 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
                    self.exception_flag = True

                logging.debug("Level 14 boolean NO operation")
                ret = not(operand.value)

                # Raise exception if result is False and exception flag was taken by this operation.
                if not ret and self.exception_flag is True:
                    raise Exception(f'Expression operation {operation} {operand.value} was not satisfied.')

        # Release exception flag.
        if self.exception_flag is True:
            self.update_wfml_data('Flags.Exception', False)

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
        ret = self.op[0].value
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):

            # Take exception flag if it was still not taken.
            if operation in ['<', '>', '==', '>=', '<=', '!=', 'in', 'not in']:
                if self.get_wfml_data('Flags.Exception') is False:
                    logging.debug("Level 12 Exception flag.")
                    self.update_wfml_data('Flags.Exception', True)
                    self.exception_flag = True
                ret = self.op[0].value
                logging.debug(f'{ret} {operation} {operand.value}')

            if operation == '<':
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
            self.update_wfml_data('Flags.Exception', False)

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
            if operation == 'requires':
                flag_left = False
                flag_right = False
                for element in self.get_wfml_data('Model').elements:
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
                for element in self.get_wfml_data('Model').elements:
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
        if len(self.op) == 1:
            ret = self.op[0].value
        else:
            for operation, operand in zip(self.op[1::2], self.op[2::2]):
                self.update_wfml_data('Flags.Update', True)
                ret = self.op[0].value
                self.update_wfml_data('Flags.Update', False)
                right_value = operand.value
                if operation == '=':
                    cardinality_flag = self.get_wfml_data('Flags.Cardinality')
                    logging.debug(f"Level 10 assignment operation: {ret} {operation} {right_value} {cardinality_flag}")

                    # Assign to complex path variable.
                    if re.match(r'(\w+\.)+\w+', ret) and cardinality_flag is None:
                        path = ret.split('.')
                        path.append('value')

                        # Double check Python literal structures values if they are presented in str object.
                        try:
                            assign = right_value if type(right_value) != str else ast.literal_eval(right_value)
                        except ValueError:
                            assign = right_value

                        self.update_wfml_data('Namespace.' + path, {'value': assign})

                    # If cardinality flag was set, then update cardinality value instead of variable in namespace.
                    elif re.match(r'(\w+\.)+\w+', ret) and cardinality_flag == 'fcard':
                        self.update_wfml_data('Cardinalities.Feature', {ret.split('.', 1)[1]: right_value})

                else:
                    raise Exception(f'Parameter {ret} is not defined.')
        return ret

    def cross_tree_check(self):
        if len(self.op) > 1 and self.op[1] == '=':
            self.update_wfml_data('Flags.Update', True)

        for part in self.op:
            if isinstance(part, ExpressionElement):
                part.cross_tree_check()
            else:
                self.update_wfml_data('Flags.Update', False)
        self.update_wfml_data('Flags.Update', False)

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
            if operation == '+':
                logging.debug(f"Level 9 addition operation: {ret} {operation} {right_value}")
                ret += right_value
            elif operation == '-':
                logging.debug(f"Level 9 subtraction operation: {ret} {operation} {right_value}")
                ret -= right_value
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '*':
                logging.debug(f"Level 8 multiplication operation: {ret} {operation} {right_value}")
                ret *= right_value

            elif operation == '/':
                logging.debug(f"Level 8 division operation: {ret} {operation} {right_value}")
                ret /= right_value

            elif operation == '%':
                logging.debug(f"Level 9 remainder operation: {ret} {operation} {right_value}")
                ret %= right_value
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
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation == 'min':
                logging.debug(f"Level 8 min operation: {operation}")
                ret = min(operand.value)

            elif operation == 'max':
                logging.debug(f"Level 8 max operation: {operation}")
                ret = max(operand.value)
        if len(self.op) == 1:
            ret = self.op[0].value

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
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation == 'sum':
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value

            # Perform list union if such operation exist.
            if operation == ',' or operation == '++':
                if type(ret) == list and type(right_value) == list:
                    ret = list(set(ret) | set(right_value))
                elif type(ret) != list:
                    raise Exception(f'Parameter {ret} is not list.')
                elif type(right_value) != list:
                    raise Exception(f'Parameter {right_value} is not list.')

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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value

            # Perform list difference if such operation exist.
            if operation == '--' and type(ret) == list and type(right_value) == list:
                ret = list(set(ret) - set(right_value))
            elif operation == '--' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '--' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value

            # Perform list merge (without duplicates) if such operation exist.
            if operation == '**' and type(ret) == list and type(right_value) == list:
                ret = list(set(ret) & set(right_value))
            elif operation == '**' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '**' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')

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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value

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


class term(ExpressionElement):
    @property
    def value(self):
        """
        Function to check type of op value (variable, number, string, etc.) and return it.

        RETURN
        op (variable type): variable, number, string, etc.
        """
        op = self.op

        # In case of int or float value, just return it
        if type(op) in {int, float}:
            logging.debug(f"Operation object: {op} with type {type(op)}")
            return op

        # In case of ExpressionElement object (another constraint), return its validated value.
        elif isinstance(op, ExpressionElement):
            logging.debug(f"Operation object: {op} with value {type(op)}")
            return op.value

        # In case of top-level variable in global namespace return its value.
        elif op in self.get_wfml_data('Namespace').keys():
            logging.debug("Variable in global namespace.")
            return self.get_wfml_data('Namespace')[op]['value']

        # In case of bool value, just return it.
        elif type(op) is bool:
            return op

        # In case of string value, launch additional checks.
        elif type(op) is str and op not in keywords:
            logging.debug(f"String object: {op}")
            if op not in self.get_wfml_data('Namespace').keys() and not re.match(r'(\w+\.)+\w+', op):
                check = f'{self.get_wfml_data("Path")}.{op}'
                if check in self.get_wfml_data('Iterable.Mapping.Structure').keys():
                    check = self.map_variable(check)
                namespace = self.get_wfml_data('Namespace')
                try:
                    for part in check.split('.'):
                        namespace = namespace[part]
                    op = check
                except KeyError:
                    logging.debug('No such key exist.')
            # If string pattern match list object ('{a, b}'), transform it to python list object.
            if re.match(r'\{.+\}', op):
                op = op.replace('{', '').replace('}', '').replace(' ', '')
                logging.debug("List object")
                op = op.split(',')
                for index, element in enumerate(op):
                    op[index] = self.autoconvert(element)
                logging.debug(op)

            # If string pattern match path to variable (splitted with dot delimiters: 'a.b.c')
            elif re.match(r'(\w+\.)+\w+', op):
                # Check for mappings
                if op in self.get_wfml_data('Iterable.Mapping.Structure').keys():
                    op = self.map_variable()
                self.update_wfml_data('Iterable.UnvalidatedFeatures', op)
                path = op.split('.')

                # Perform feature of group cardinality search if first part of string is a appropriate keyword.
                if path[0] == 'fcard' or path[0] == 'gcard':
                    self.update_wfml_data('Flags.Cardinality', path[0])
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
                        cardinality_flag = self.get_wfml_data('Flags.Cardinality')
                        if cardinality_flag == 'fcard':
                            res = self.get_wfml_data('Cardinalities.Feature')[full_path]
                        elif cardinality_flag == 'gcard':
                            res = self.get_wfml_data('Cardinalities.Group')[full_path]
                    except KeyError:
                        raise Exception(f'No such cardinality exist {full_path} for type {cardinality_flag}')

                elif path[0] == 'childs':
                    path = path[1:]
                    res = self.get_wfml_data('Namespace')
                    for section in path:
                        res = res[section]
                    res = list(res.keys())

                # If no cardinalities keyword presented in path, then try to find variable using this path.
                else:
                    res = self.get_wfml_data('Namespace')
                    for section in path:
                        res = res[section]
                    res = res['value']
                if self.get_wfml_data('Flags.Update') is False:
                    op = res
            return op
        else:
            raise Exception('Unknown variable "{}" at position {}'
                            .format(op, self._tx_position))
        return self.op

    def map_variable(self, feature=None):
        if feature is None:
            feature = self.op
        threshold = self.get_wfml_data('Iterable.Mapping.Total')
        repeat = self.get_wfml_data('Iterable.Mapping.Current')
        mappings = self.get_wfml_data('Iterable.Mapping.Structure')
        for key, value in mappings.items():
            threshold = threshold / len(mappings[feature])
            suffix = repeat / threshold
            repeat = repeat % threshold
            if key == feature:
                break
        return f'{feature}_{str(int(suffix))}'

    def mapping_check(self):
        if isinstance(self.op, str) and not re.match(r'(\w+\.)+\w+', self.op):
            check = f'{self.get_wfml_data("Path")}.{self.op}'
            if check in self.get_wfml_data('Features.Mapped').keys():
                op = check
            else:
                op = self.op
        else:
            op = self.op
        if op in self.get_wfml_data('Dependencies.Mappings').keys():
            self.update_wfml_data('Iterable.Mapping.Total',
                                  self.get_wfml_data('Iterable.Mapping.Total') * len(
                                      self.get_wfml_data('Dependencies.Mappings')[op]))
            self.update_wfml_data('Iterable.Mapping.Structure',
                                  {op: self.get_wfml_data('Dependencies.Mappings')[op]})

    def initial_super_reference_check(self):
        if self.op in self.get_wfml_data('Namespace').keys():
            return self.op
        else:
            ol = self._tx_position_end - self._tx_position
            msg = ''.join((f'No such super feature exist in the model : {self.op}!\n',
                           f'Error position: Line {get_location(self)["line"]},',
                           f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                           f' Filename {get_location(self)["filename"]}\n'))
            raise Exception(msg)

    def initial_type_reference_check(self):
        allowed_types = ['integer', 'float', 'string', 'predefined', 'array', 'integerArray', 'floatArray']
        if self.op in allowed_types:
            return self.op
        else:
            ol = self._tx_position_end - self._tx_position
            msg = ''.join((f'Type {self.op} is not allowed to use!\n',
                           f'Allowed types: {allowed_types}.\n',
                           f'Error position: Line {get_location(self)["line"]},',
                           f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                           f' Filename {get_location(self)["filename"]}\n'))
            raise Exception(msg)

    def cross_tree_check(self):
        op = self.op
        if type(op) is str and op not in keywords and re.match(r'(\w+\.)+\w+', op):
            forbidden_flag = False
            path = op.split('.')

            # Check for cardinality keyword and remove it.
            if path[0] == 'fcard' or path[0] == 'gcard':
                path = path[1:]

            # Forbid to add to cross-tree features own features written in full-path form.
            if path[0] == self.get_wfml_data('Path').split('.')[0]:
                forbidden_flag = True

            try:
                res = self.get_wfml_data('Namespace')
                for section in path:
                    res = res[section]
                if forbidden_flag is False and self.get_wfml_data('Flags.Update') is False:
                    self.update_wfml_data('Dependencies.CrossTree', [self.get_wfml_data('Path').split('.')[0], path[0]], False)
                elif forbidden_flag is False and self.get_wfml_data('Flags.Update') is True:
                    self.update_wfml_data('Dependencies.CrossTree', [path[0], self.get_wfml_data('Path').split('.')[0]], False)
            except Exception:
                logging.debug('ok')

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

    def constraint_validation(self, constraint):
        """
        Perform constraint execution.
        """
        self.reset_wfml_data('Iterable.Mapping.Current')
        self.reset_wfml_data('Iterable.Mapping.Total')
        self.reset_wfml_data('Iterable.Mapping.Structure')
        self.reset_wfml_data('Flags.Cardinality')
        constraint.name.mapping_check()
        logging.debug(f'Constraint name: {constraint.name}')

        while self.get_wfml_data('Iterable.Mapping.Current') < self.get_wfml_data('Iterable.Mapping.Total'):
            self.reset_wfml_data('Iterable.UnvalidatedFeatures')
            if self.get_wfml_data('Flags.CrossTreeCheck') is True:
                constraint.name.cross_tree_check()
            else:
                constraint.name.value
            self.update_wfml_data('Iterable.Mapping.Current', self.get_wfml_data('Iterable.Mapping.Current') + 1)

        if self.get_wfml_data('Flags.Cardinality') == 'fcard':
            self.mapping()

    def validate_common_constraints(self):
        for element in self.get_wfml_data('Model').elements:
            if self.cname(element) == "Constraint":
                self.update_wfml_data('Flags.Exception', False)
                self.constraint_validation(element)

    def define_feature(self, feature, parent_namespace=None):
        """
        ! This method is recursive.

        Function to define features.

        INPUTS
        feature (type = feature): feature to define.
        parent_namespace (type = dict): parent feature namespace to fullfill.

        RETURN
        parent_namespace (type = dict): fullfilled parent namespace. Only for not top-level features.
        """
        feature.namespace = {}
        feature.super_direct = []
        feature.super_indirect = []

        for child in feature.nested:
            for child1 in child.child:
                if self.cname(child1) == 'Feature':
                    feature.namespace.update(self.define_feature(child1, feature.namespace))

        if feature.reference is not None:
            feature.namespace.update({'value': None, 'type': feature.reference.initial_type_reference_check()})

        if parent_namespace is not None:
            parent_namespace.update({feature.name: feature.namespace})
            logging.info(f'Subfeature {feature.name} was defined.')
            return parent_namespace
        else:
            self.update_wfml_data('Namespace', {feature.name: feature.namespace})
            logging.info(f'Top-level feature {feature.name} was defined.')

    def update_wfml_data(self, path: str, data, duplicates=True):
        global wfml_data
        full_path = path
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.')[:-1]:
                wfml_data_section = wfml_data_section[section]
            path = path.split('.')[-1]
        else:
            wfml_data_section = wfml_data

        if type(wfml_data_section[path]) is dict:
            wfml_data_section[path].update(data)
        elif type(wfml_data_section[path]) is list and duplicates is True:
            wfml_data_section[path].append(data)
        elif type(wfml_data_section[path]) is list and duplicates is False:
            if data not in wfml_data_section[path]:
                wfml_data_section[path].append(data)
        else:
            wfml_data_section[path] = data
        logging.debug(f'WFML data for {full_path} was updated. New value is {data}.')

    def clear_wfml_data(self, path: str):
        global wfml_data
        full_path = path
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.')[:-1]:
                wfml_data_section = wfml_data_section[section]
            path = path.split('.')[-1]
        else:
            wfml_data_section = wfml_data

        if isinstance(wfml_data_section[path], dict) or isinstance(wfml_data_section[path], list):
            wfml_data_section[path].clear()
        elif isinstance(wfml_data_section[path], str):
            wfml_data_section[path] = ''
        elif isinstance(wfml_data_section[path], int) or isinstance(wfml_data_section[path], float):
            wfml_data_section[path] = 0
        else:
            raise TypeError(f'Wrong type of {full_path}.')
        logging.debug(f'WFML data for {full_path} was cleared.')

    def reset_wfml_data(self, path: str):
        global wfml_data, initial_data
        full_path = path
        wfml_data_init = initial_data
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.')[:-1]:
                wfml_data_section = wfml_data_section[section]
                wfml_data_init = wfml_data_init[section]
            path = path.split('.')[-1]
        else:
            wfml_data_section = wfml_data

        wfml_data_section[path] = copy.deepcopy(wfml_data_init[path])
        logging.debug(f'WFML data for {full_path} was reset to {wfml_data_section[path]}.')
        logging.debug(f'{self.get_wfml_data(full_path)}')

    def pickle_wfml_data(self):
        global wfml_data
        pickle_data = dict(wfml_data)
        del pickle_data['Model']
        with open('configuration.pkl', 'wb') as output:
            for key in pickle_data.keys():
                pickle.dump({key: wfml_data[key]}, output, pickle.HIGHEST_PROTOCOL)

    def load_wfml_data(self, pickle_obj):
        global wfml_data
        objects = []
        while True:
            try:
                objects.append(pickle.load(pickle_obj))
            except EOFError:
                break
        wfml_data = objects

    def initial_snap(self):
        self.update_wfml_data('Stages.Cumulative.Namespace', {'-1': copy.deepcopy(self.get_wfml_data('Namespace'))})
        self.update_wfml_data('Stages.Cumulative.Cardinalities', {'-1': copy.deepcopy(self.get_wfml_data('Cardinalities'))})

    def get_wfml_data(self, path: str):
        global wfml_data
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.'):
                wfml_data_section = wfml_data_section[section]
        else:
            wfml_data_section = wfml_data[path]
        return wfml_data_section

    def map_wfml_data(self, path: str, record):
        global wfml_data
        wfml_data_section = wfml_data
        if re.match(r'(\w+\.)+\w+', path):
            for section in path.split('.'):
                wfml_data_section = wfml_data_section[section]
        else:
            wfml_data_section = wfml_data[path]

        if path == 'Namespace':
            self.map_namespace(wfml_data_section, path, record)
        elif path == 'Cardinalities.Group':
            self.map_gcard(wfml_data_section, path, record)
        else:
            raise AttributeError('Wrong mapping type.')
        logging.debug(f'WFML record {record} in path {path} was successfully mapped. {wfml_data_section}')

    def map_gcard(self, wfml_data_section, path: str, record):
        additional_keys = {}
        remove_keys = []
        flag = False
        for key in wfml_data_section.keys():
            name = ''
            for part in key.split('.'):
                if name == '':
                    name = part
                else:
                    name = f'{name}.{part}'
                if name == record:
                    flag = True
                    remove_keys.append(record)
                    break
            if flag is True:
                for mapping in self.get_wfml_data('Dependencies.Mappings')[record]:
                    additional_keys.update({mapping: self.get_wfml_data('CardinalitiesInitial.Group')[key]})
        for key in remove_keys:
            del wfml_data_section[key]
        self.update_wfml_data('Cardinalities.Group', additional_keys)
        self.update_wfml_data('CardinalitiesInitial.Group', additional_keys)
        self.update_wfml_data('Flags.ExtraStep', True)

    def map_namespace(self, wfml_data_section, path: str, record):
        wfml_data_section_init = self.get_wfml_data('NamespaceInitial')
        if len(record.split('.')) == 1:
            if (record in wfml_data_section.keys() or record in self.get_wfml_data('Features.Mapped')) and \
                    record in self.get_wfml_data('Dependencies.Mappings').keys():
                for mapping in self.get_wfml_data('Dependencies.Mappings')[record]:
                    wfml_data_section[mapping] = copy.deepcopy(wfml_data_section_init[record])
                del wfml_data_section[record]
        else:
            original = None
            for part in record.split('.')[:-1]:
                wfml_data_section_init = wfml_data_section_init[part]
            for mapping in self.get_wfml_data('Dependencies.Mappings')[record]:
                wfml_data_section_sub = wfml_data_section
                for part in mapping.split('.')[:-1]:
                    wfml_data_section_sub = wfml_data_section_sub[part]
                if original is None:
                    original = copy.deepcopy(wfml_data_section_init[record.split('.')[-1]])
                wfml_data_section_sub[mapping.split('.')[-1]] = copy.deepcopy(original)
            try:
                wfml_data_section_sub = wfml_data_section
                for part in record.split('.')[:-1]:
                    wfml_data_section_sub = wfml_data_section_sub[part]
                del wfml_data_section_sub[record.split('.')[-1]]
            except KeyError:
                pass

    def apply_group_cardinalities(self):
        for key, value in self.get_wfml_data('Cardinalities.Group').items():
            remove_keys = []
            sub_namespace = self.get_wfml_data('Namespace')
            for part in key.split('.'):
                sub_namespace = sub_namespace[part]
            for subkey in sub_namespace.keys():
                if subkey not in value and subkey not in remove_keys:
                    remove_keys.append(subkey)
            for subkey in remove_keys:
                del sub_namespace[subkey]

    def show_wfml_data(self):
        global wfml_data
        return wfml_data

    def get_model_cardinalities(self):
        """
        Function to find all cardinalities.

        RETURN
        fcard (type = dict): dict of feature cardinalities values.
        gcard (type = dict): dict of group cardinalities values.
        """
        fcard = {}
        gcard = {}
        for element in self.get_wfml_data('Model').elements:
            if self.cname(element) == 'Feature':
                fcard.update(self.clafer_fcard(element))
                gcard.update(self.clafer_gcard(element))
        self.update_wfml_data('CardinalitiesInitial.Feature', fcard)
        self.update_wfml_data('CardinalitiesInitial.Group', gcard)
        self.update_wfml_data('Cardinalities.Feature', fcard)
        self.update_wfml_data('Cardinalities.Group', gcard)

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
                if self.cname(child1) == 'Feature':
                    fcard.update(self.clafer_fcard(child1, name))
        if clafer.fcard:
            fcard.update({name: clafer.fcard})
        else:
            fcard.update({name: 1})
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
                if self.cname(child1) == 'Feature':
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
        fcard = self.get_wfml_data('Cardinalities.Feature')
        gcard = self.get_wfml_data('Cardinalities.Group')
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
            logging.debug(f'Result: {x} not lies in interval {card}')
            return Exception(f'Result: {x} not lies in interval {card}')

    def update_abstract_clafers(self):
        """
        Function to find all abstract features.
        """
        for element in self.get_wfml_data('Model').elements:
            if self.cname(element) == 'Feature':
                for feature in self.clafer_abstract(element):
                    self.update_wfml_data('Features.Abstract', {feature: 'Stub'})

    def snap_step_data(self, step):
        if step not in self.get_wfml_data('Stages.Cumulative').keys():
            self.update_wfml_data('Stages.Cumulative.Namespace', {step: {}})
            self.update_wfml_data('Stages.Cumulative.Cardinalities', {step: {}})
            self.update_wfml_data('Stages.Additional.Namespace', {step: {}})
            self.update_wfml_data('Stages.Additional.Cardinalities', {step: {}})
        self.update_wfml_data(f'Stages.Cumulative.Namespace.{step}', copy.deepcopy(self.get_wfml_data('Namespace')))
        self.update_wfml_data(f'Stages.Cumulative.Cardinalities.{step}', copy.deepcopy(self.get_wfml_data('Cardinalities')))
        self.update_wfml_data(f'Stages.Additional.Namespace.{step}',
                              DeepDiff(self.get_wfml_data(f'Stages.Cumulative.Namespace.{str(int(step) - 1)}'),
                                       self.get_wfml_data('Namespace')))
        self.update_wfml_data(f'Stages.Additional.Cardinalities.{step}',
                              DeepDiff(self.get_wfml_data(f'Stages.Cumulative.Cardinalities.{str(int(step) - 1)}'),
                                       self.get_wfml_data('Cardinalities')))

    def get_stage_snap(self, step):
        self.update_wfml_data('Namespace', copy.deepcopy(self.get_wfml_data(f'Stages.Cumulative.Namespace.{str(int(step) - 1)}')))
        self.update_wfml_data('Cardinalities', copy.deepcopy(self.get_wfml_data(f'Stages.Cumulative.Cardinalities.{str(int(step) - 1)}')))

        for key in self.get_wfml_data('Stages.Cumulative.Namespace').keys():
            if int(key) >= int(step):
                self.clear_wfml_data(f'Stages.Cumulative.Namespace.{str(key)}')
                self.clear_wfml_data(f'Stages.Additional.Namespace.{str(key)}')
                self.clear_wfml_data(f'Stages.Cumulative.Cardinalities.{str(key)}')
                self.clear_wfml_data(f'Stages.Additional.Cardinalities.{str(key)}')

    def clafer_abstract(self, clafer, prefix=None):
        """
        ! This method is recursive.

        Function to find all abstract features.

        INPUTS
        clafer (type = clafer): top-level clafer to check for abstract.
        prefix (type = str): prefix to create full path.

        RETURN
        abstr_clafers (type = list): list of abstract features.
        """
        abstr_clafers = []
        if prefix:
            name = prefix + '.' + clafer.name
        else:
            name = clafer.name
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == 'Feature':
                    res = self.clafer_abstract(child1, name)
                    abstr_clafers = abstr_clafers + res
        if clafer.abstract:
            abstr_clafers.append(name)
        return abstr_clafers

    def fullfill_abstract_dependencies(self):
        """
        Function to fullfill abstract clafer dependencies.
        This depencendies are presented as dict(abstract clafer: [list of features inherited from it])
        """
        for feature in self.get_wfml_data('Features.Abstract').keys():
            res = []
            for element in self.get_wfml_data('Model').elements:
                if self.cname(element) == 'Feature':
                    for elem in self.find_abstract(element, feature):
                        res.append(elem)
            self.update_wfml_data('Dependencies.Abstract', {feature: res})
        logging.info('Abstract dependencies fullfiled.')

    def find_abstract(self, clafer, abstract, prefix=None):
        """
        ! This method is recursive.

        Function to find all features with concrete abstract clafer.

        INPUTS
        clafer (type = clafer): clafer to check for abstract.
        abstract (type = clafer): abstract clafer to check.

        RETURN
        abstr_clafers (type = list): list of features with concrete abstract clafer.
        """
        abstr_clafers = []
        if prefix:
            name = prefix + '.' + clafer.name
        else:
            name = clafer.name
        for child in clafer.nested:
            for child1 in child.child:
                if self.cname(child1) == 'Feature':
                    res = self.find_abstract(child1, abstract, name)
                    abstr_clafers = abstr_clafers + res
        if abstract in clafer.super_direct or abstract in clafer.super_indirect:
            abstr_clafers.append(name)
        return abstr_clafers


    def get_clafer_type(self, clafer: str):
        """
        Function to find and return specified clafer type.

        INPUTS
        clafer: clafer name.

        RETURN
        type (type = str): clafer type if clafer is parametric.
        unspecified : if clafer is group.
        """
        self.get_wfml_data('Namespace')
        path = clafer.split('.')
        gn_copy = self.get_wfml_data('Namespace')
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
        Subfunction to define sequence of features to validate. The analogue of directed graph path.

        INPUTS
        dependency_pairs: list of cross-tree dependencies pairs.

        RETURN
        ordered (type = list): sequence of independent features to validate.
        cyclic (type = list): list of cyclic features.
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
        Function to define sequence of features to validate.

        INPUTS
        cross_tree_dependencies: list of cross-tree dependencies.

        RETURN
        ret_val (type = list): sequence of features to validate.
        """

        # Define cross-tree and independent features
        ctl = []
        all_clafers = list(self.get_wfml_data('Namespace').keys())
        cross_clafers = []
        for dep in cross_tree_dependencies:
            cross_clafers.append(dep[0])
            cross_clafers.append(dep[1])
            ctl.append(dep[1])

        cross_clafers = list(dict.fromkeys(cross_clafers))
        s = set(cross_clafers)
        a = self.get_wfml_data('Features.Abstract').keys()
        independent_clafers = [x for x in all_clafers if x not in s and x not in a]

        for element in self.get_wfml_data('Model').elements:
            for feature in independent_clafers:
                if element.name == feature and element.abstract is None:
                    self.update_wfml_data('Features.Independent', {feature: 'Stub'})
            for feature in s:
                if element.name == feature:
                    self.update_wfml_data('Features.CrossTree', {feature: 'Stub'})

        # Create networkx graph object
        G = nx.DiGraph(cross_tree_dependencies)
        index = 0
        remove_dependencies = []

        # Find all cycles in graph. Create list of cycle dependencies.
        for cycle in nx.simple_cycles(G):
            index += 1
            logging.debug(f'Cycle cycle{index} contain elements: {cycle}')
            self.update_wfml_data('Features.Cycles', {f'cycle{index}': cycle})
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

        self.reset_wfml_data('Dependencies.CrossTree')
        for dep in cross_tree_dependencies:
            self.update_wfml_data('Dependencies.CrossTree', dep)

        # Perform topological sort for dependencies.
        res = self.topological_sort(cross_tree_dependencies)
        res[0].reverse()
        result = res[0] + independent_clafers

        # Add independent cycles
        index = 0
        for cycle in nx.simple_cycles(G):
            index += 1
            if f'cycle{index}' not in result:
                result.append(f'cycle{index}')
        ret_val = ['FeatureCardinalities'] + ['GroupCardinalities'] + result
        logging.info(f'There are {len(res[0])} stages for cross-tree dependencies: {res[0]}')
        logging.info(f'Cycled features: {self.get_wfml_data("Features.Cycles")}')
        logging.info(f'Additional independent features: {independent_clafers}')
        logging.info(f'Final result: {result}')
        self.update_wfml_data('Stages.List', ret_val)
        return ret_val

    def recursive_items(self, dictionary: dict, prefix=None):
        """
        ! This method is recursive.

        Function to read values from dictionary.

        INPUTS
        dictionary: dictionary to read value from.
        prefix (type = str): prefix to create full path for nested features.

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
        self.get_wfml_data('Namespace')
        inner = self.get_wfml_data('Namespace')

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

    def read_certain_key(self, path: str, only_childs: bool):
        """
        ! This method is only used to read group cardinalities (including inherited from abstract features).

        Function to read values from global namespace.

        INPUTS
        path: path to read value from.
        only_childs: flag to return only direct childs.

        RETURN
        key (type = dict): read value.
        """
        key = {}

        if path in self.get_wfml_data('Dependencies.Mappings').keys():
            path = self.get_wfml_data('Dependencies.Mappings')[path]
        else:
            path = [path]
        for subpath in path:
            namespace = self.get_wfml_data('Namespace')
            for part in subpath.split('.'):
                namespace = namespace[part]
            subkey = {}

            if only_childs:
                for k, v in namespace.items():
                    subkey.update({k: v})
            else:
                for k, v in self.recursive_items(namespace):
                    subkey.update({k: v})
            key[subpath] = subkey
        return key

    def get_cycle_keys(self):
        return self.get_wfml_data('Features.Cycles')

    def get_namespace(self):
        return self.get_wfml_data('Namespace')

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
                if self.cname(child1) == 'Feature' and child1.reference is None:
                    self.group_clafer(child1, group)
                elif self.cname(child1) == 'Feature' and child1.reference is not None:
                    self.property_clafer(child1, group)
        namespace[clafer.name] = group
        clafer.namespace = group
        return namespace

    def feature_constraints_validation(self, clafer, isroot):
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

        # According to isroot flag update current_path variable.
        if isroot is True:
            self.update_wfml_data('Path', clafer.name)
        else:
            local_path = self.get_wfml_data('Path')
            self.update_wfml_data('Path', f'{local_path}.{clafer.name}')

        for child in clafer.nested:
            for child1 in child.child:
                constraints_validated = 0
                # Perform constraint validation using clafer mappings if such are exist.
                if self.cname(child1) == "Constraint":
                    self.reset_wfml_data('Iterable.Mapping.Current')
                    self.reset_wfml_data('Iterable.Mapping.Total')
                    self.reset_wfml_data('Iterable.Mapping.Structure')
                    self.reset_wfml_data('Flags.Cardinality')
                    child1.name.mapping_check()
                    logging.debug(f'Constraint name: {child1.name}')

                    while self.get_wfml_data('Iterable.Mapping.Current') < self.get_wfml_data('Iterable.Mapping.Total'):
                        self.reset_wfml_data('Iterable.UnvalidatedFeatures')
                        if self.get_wfml_data('Flags.CrossTreeCheck') is True:
                            child1.name.cross_tree_check()
                        else:
                            child1.name.value
                            constraints_validated += 1
                        self.update_wfml_data('Iterable.Mapping.Current', self.get_wfml_data('Iterable.Mapping.Current') + 1)

                    if self.get_wfml_data('Flags.Cardinality') == 'fcard':
                        self.mapping()

                # Perform constraint validation for nested features.
                elif self.cname(child1) == 'Clafer' and isinstance(child1.reference, type(None)):
                    logging.info(f'CLAFR {clafer.namespace}')
                    self.feature_constraints_validation(child1, False)
            logging.info(f'For clafer {clafer.name} there is/are {constraints_validated} constraint expression(s) validated.')

        # Reset current_path variable.
        if isroot is True:
            self.update_wfml_data('Path', '')
        else:
            self.update_wfml_data('Path', local_path)
        return clafer.namespace

    def cardinalities_update(self, data):
        for record in data:
            if record[0] == 'fcard':
                self.update_wfml_data('Cardinalities.Feature', record[1])
                self.mapping(record[1])
            elif record[0] == 'gcard':
                self.update_wfml_data('Cardinalities.Group', record[1])
            else:
                raise ValueError('Incorrect cardinality type.')

    def add_super_relations(self, clafer):
        """
        ! This method is recursive.

        Find and fullfill all super relations in the model.

        INPUTS
        clafer (type = textX.clafer): clafer to check for super relation.
        """
        if clafer.super is not None:
            for element in self.get_wfml_data('Model').elements:
                if element.name == clafer.super.initial_super_reference_check():
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
                        # If clafer has childs, merge both features nested elements.
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
                if self.cname(child1) == 'Feature':
                    self.add_super_relations(child1)

    def reset_exception_flag(self):
        self.update_wfml_data('Flags.Exception', False)
        logging.debug('Global exception flag was reset')

    def to_json(self):
        """
        ! This method will be removed.

        Create dict object with fullfilled values

        RETURN
        result (type = dict): copies of global namespace records or element namespace.
        """
        result = {}
        for element in self.get_wfml_data('Model').elements:
            if self.cname(element) == 'Feature' and element.abstract is None:
                if element.reference is not None:
                    result[element.name] = self.get_wfml_data('Namespace')[element.name]
                else:
                    result[element.name] = element.namespace
        return result

    def mapping(self):
        """
        ! This method is only used for features with cardinalities != 1

        Create new mapping instance. This mapping will be used for constraints validation.
        For example, fcard (a) = 2, then 2 features will be created -> a0, a1.
        Mapping presented as a dict: {a: [a0, a1]}
        For constraint [a > 5] two constraints will be validated instead this one:
        [a0 > 5]
        [a1 > 5]

        INPUTS
        original: original clafer name.
        copy: copy of original clafer name with added suffix _x, where x is sequentional mapping number.
        """
        for original in self.sort_fcards():
            if original not in self.get_wfml_data('Dependencies.Mappings').keys():
                copies = []
                full_feature_cardinality, structure = self.get_full_feature_cardinality(original)
                if isinstance(full_feature_cardinality, int) and full_feature_cardinality != 1:
                    for iteration in range(0, full_feature_cardinality):
                        copies.append(self.name_generation(original, structure, iteration))
                    self.update_wfml_data('Dependencies.Mappings', {original: copies})
                    logging.debug(f'New mapping was added: {original}: {copies}')
                    self.map_wfml_data('Namespace', original)
                    if original in self.get_wfml_data('Cardinalities.Group').keys():
                        self.map_wfml_data('Cardinalities.Group', original)
                    self.update_wfml_data('Features.Mapped', {original: len(copies)})
            else:
                full_feature_cardinality, structure = self.get_full_feature_cardinality(original)
                if isinstance(full_feature_cardinality, int) and full_feature_cardinality != 1:
                    if full_feature_cardinality != len(self.get_wfml_data('Dependencies.Mappings').keys()):
                        copies = []
                        for iteration in range(0, full_feature_cardinality):
                            copies.append(self.name_generation(original, structure, iteration))
                        self.update_wfml_data('Dependencies.Mappings', {original: copies})
                        self.map_wfml_data('Namespace', original)
                        if original in self.get_wfml_data('Cardinalities.Group').keys():
                            self.map_wfml_data('Cardinalities.Group', original)
                        logging.debug(f'Mapping was updated: {original}: {copies}')

    def update_global_namespace(self, key: str, value: int):
        """
        ! Method is used only to update filled on web interface cardinalities form.

        Update global namespace record.

        INPUTS
        key: cardinality identification name.
        value: cardinality value.
        """
        self.get_wfml_data('Namespace')
        k_s = key.split('_')
        if k_s[0] == 'fcard' and len(k_s[1].split('.')) >= 1 and value > 1:
            ret = self.get_wfml_data('Namespace')
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
        self.update_wfml_data('Path', '')
        try:
            for element in self.get_wfml_data('Model').elements:
                if self.cname(element) == 'Feature' and element.name == clafer:
                    self.update_wfml_data('Flags.Exception', False)
                    self.feature_constraints_validation(element, True)
            self.update_wfml_data('Path', '')
            return True
        except Exception as e:
            logging.info(f'! Exception: {e}.')
            self.update_wfml_data('Path', '')
            return e

    def reset_global_variables(self):
        """
        Clear all shared variables.
        """
        global wfml_data, initial_data
        directory = dirname(abspath(__file__))
        pattern = open(f'{directory}/shared_data_pattern.json')
        wfml_data = json.load(pattern)
        initial_data = copy.deepcopy(wfml_data)

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

        self.get_wfml_data('Namespace')
        preprint = copy.deepcopy(self.get_wfml_data('Namespace'))
        # preprocessed_preprint = self.clear_json_trash(preprint)
        res = self.preprocess_json(preprint)
        logging.info('Final result was successfully created.')
        logging.debug(f'Final Model {res}')

        with open('configuration.json', 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=4)

        self.pickle_wfml_data()
        return res

    def define_features(self):
        """
        Calls clafer definition function for all features in the model.
        """
        for element in self.get_wfml_data('Model').elements:
            if self.cname(element) == 'Feature':
                self.define_feature(element)
        logging.info('All features are successfully defined.')

    def define_super_relations(self):
        """
        Calls super relations definition function for all features in the modell.
        """
        for element in self.get_wfml_data('Model').elements:
            if self.cname(element) == 'Feature':
                self.add_super_relations(element)
        logging.info('For all features super relations are defined.')

    def cross_tree_check(self):
        """
        Find all cross-tree dependencies in model constraints.
        """
        self.update_wfml_data('Flags.CrossTreeCheck', True)

        for element in self.get_wfml_data('Model').elements:
            self.update_wfml_data('Flags.Exception', True)
            if self.cname(element) == 'Feature' and element.abstract is None:
                self.feature_constraints_validation(element, True)

        self.update_wfml_data('Flags.CrossTreeCheck', False)
        logging.info('Model was successfully checked for cross-tree dependencies.')

    def get_full_feature_cardinality(self, clafer: str):
        """
        Get complex feature cardinality of clafer. This includes cardinalities of all super direct
        and super indirect clafers.

        INPUTS
        clafer: clafer name

        RETURN
        ret (type = int): clafer complex feature cardinality;
        struct (type = dict): structure of complex cardinality (clafer name: cardinality)
        For example,
        a 2 {
            b 3
        }
        ret: 6
        struct: {a: 2, b: 3}
        """
        ret = 1
        struct = {}
        abstract_clafers = self.get_wfml_data('Dependencies.Abstract')
        name = ''

        # Check for abstract clafer.
        for part in clafer.split('.'):
            check = True
            if name == '':
                name = part
            else:
                name = f'{name}.{part}'
            if name in abstract_clafers.keys():
                check = False
            if name in clafer and check is True:
                if name not in abstract_clafers.keys():
                    struct.update({part: self.get_wfml_data('Cardinalities.Feature')[name]})
                    ret = ret * self.get_wfml_data('Cardinalities.Feature')[name]
        logging.debug(f'RET: {ret}, STRUCT: {struct}')
        return ret, struct

    def clear_abstract_features(self):
        namespace_rm_keys = []
        cardinalities_rm_keys = []
        for feature in self.get_wfml_data('Features.Abstract').keys():
            if feature in self.get_wfml_data('Namespace').keys():
                namespace_rm_keys.append(feature)
            for cardinality in self.get_wfml_data('Cardinalities.Group').keys():
                if feature == cardinality.split('.')[0]:
                    cardinalities_rm_keys.append(cardinality)

        for key in namespace_rm_keys:
            del self.get_wfml_data('Namespace')[key]

        for key in cardinalities_rm_keys:
            del self.get_wfml_data('Cardinalities.Group')[key]

    def name_generation(self, original_name: str, struct: dict, repeat: int, flag=True):
        """
        Generate name for clafer with cardinality > 1 according to complex cardinality structure.

        INPUTS
        original_name: original clafer name;
        struct: structure of complex cardinality (clafer name: cardinality);
        repeat: sequentional number of generated clafer.

        RETURN
        ret (type = str): generated name

        For example, 6 sequentilnal function execution with different repeat values will generate:
        a 2 {
            b 3
        }
        complex cardinality: 6
        original name: b
        struct: {a: 2, b: 3}
        repeat: 0..5
        result: a0.b0, a0.b1, a0.b2, a1.b0, a1.b1, a1.b2
        """
        from functools import reduce
        threshold = reduce((lambda x, y: x * y), struct.values())
        name = original_name.split('.')
        res = ''
        for part in name:
            if part in struct.keys() and struct[part] > 1:
                threshold = threshold / struct[part]
                suffix = repeat / threshold
                repeat = repeat % threshold
                name = part + '_' + str(int(suffix))
            else:
                name = part
            if res == '':
                res = name
            else:
                res = f'{res}.{name}'
        logging.debug(f'Original {original_name} -> generated: {res}')
        return res

    def sort_fcards(self):
        fcards = self.get_wfml_data('Cardinalities.Feature')
        x = {}
        for key, value in fcards.items():
            if isinstance(value, str) or (isinstance(value, int) and value != 1):
                x.update({key: len(key.split('.'))})
        sort = dict(sorted(x.items(), key=lambda item: item[1]))
        for key, value in fcards.items():
            if isinstance(value, str) or (isinstance(value, int) and value != 1):
                sort.update({key: value})
        return sort

    def initialize_product(self, description: dict):
        """
        Performs initial model preprocessing.

        INPUTS
        description: model description from web interface or file.

        RETURN
        stages (type = list): sequence of clafer to perform constraint solving.
        """

        # Read language grammar and create textX metamodel object from it.
        this_folder = dirname(__file__)
        mm = metamodel_from_file(join(this_folder, 'grammar.tx'),
                                 classes=[prec0, prec1, prec2, prec3,
                                          prec4, prec5, prec6, prec7, prec8,
                                          prec9, prec10, prec11, prec12, prec13,
                                          prec14, prec15, prec16, prec17,
                                          prec18, prec19, prec20, prec21, prec22, prec23, term],
                                 autokwd=True)

        # Reset shared info variables and create textX model object from description.
        self.reset_global_variables()
        model = mm.model_from_str(description)
        self.update_wfml_data('Model', model)
        self.update_wfml_data('ModelDescription', description)

        # Export both metamodel and model in .dot format for class diagram construction.
        metamodel_export(mm, join(this_folder, 'metamodel.dot'))
        model_export(model, join(this_folder, 'model.dot'))

        # Perform basic initialization
        self.define_features()
        self.define_super_relations()

        # Define all abstract features and dependencies to them.
        self.update_abstract_clafers()
        self.fullfill_abstract_dependencies()

        self.update_wfml_data('NamespaceInitial', copy.deepcopy(self.get_wfml_data('Namespace')))
        self.get_model_cardinalities()

        # Perform cross-tree dependencies check.
        self.cross_tree_check()

        # Define constraint solving sequence.
        cross_tree_clafers = self.get_wfml_data('Dependencies.CrossTree')
        cross_tree_clafers.sort()
        res_cross_tree = list(k for k, _ in itertools.groupby(cross_tree_clafers))
        stages = self.staging(res_cross_tree)

        self.mapping()
        self.clear_abstract_features()

        logging.debug(pprint.pprint(self.show_wfml_data()))
        self.initial_snap()
        return stages

    def solve_constraints(self):
        """
        ! This method is only used with automatic product filling (no web interface).

        Performs solving for all types of constraints.
        """
        logging.debug('Solving constraints...')
        print(self.get_wfml_data('Stages.List'))
        for stage in self.get_wfml_data('Stages.List')[0]:
            logging.debug(f'For stage {stage}')
            if stage != "FeatureCardinalities" and stage != "GroupCardinalities":
                cycles = api.get_cycle_keys()
                if stage in cycles.keys():
                    for element in cycles[stage]:
                        self.validate_clafer(element)
                else:
                    self.validate_clafer(stage)

        # self.save_json()

    def key_check(self, part, region, wrong_keys):
        logging.debug(f'Checking {part} for {region}.')
        for key, value in part.items():
            logging.debug(f'Checking {key}.')
            if len(key.split('.')) > 1:
                check_value = key.split('.')[-1]
            else:
                check_value = key
            if check_value not in region.keys():
                additional_check = False
                if len(check_value.split('_')) > 1 and isinstance(int(check_value.split('_')[1]), int):
                    additional_check = self.feature_cardinality_check(key)
                    if additional_check is not True:
                        wrong_keys.update({key: 'Wrong Feature Cardinality'})
                else:
                    additional_check = self.group_cardinality_check(key)
                    if additional_check is not True:
                        wrong_keys.update({key: 'Wrong Group Cardinality'})
                    else:
                        wrong_keys.update({key: 'No such key exist'})
            if isinstance(value, dict) and check_value in region.keys():
                for subkey, subvalue in value.items():
                    wrong_keys.update(self.key_check({f'{check_value}.{subkey}': subvalue}, region[check_value], wrong_keys))
        return wrong_keys

    def feature_cardinality_check(self, key):
        logging.debug(f'Checking feature cardinality for {key}.')
        base_feature = key.split('_')
        print(f'Base Feature: {base_feature}')
        base_subfeature = base_feature[0].split('.')
        print(f'Base SubFeature: {base_subfeature}')
        res = ''
        if len(base_subfeature) > 1:
            for subfeature in base_subfeature[:-1]:
                if res == '':
                    res = subfeature
                else:
                    res = f'{res}.{subfeature}'
            region = self.get_wfml_data(f'Namespace.{res}')
        else:
            region = self.get_wfml_data('Namespace')
        print(f'Region: {region.keys()}')
        counter = 0
        for feature in region.keys():
            if base_subfeature[-1] == feature.split('_')[0]:
                counter += 1
        logging.debug(f'Counter: {counter}')
        result = self.cardinality_solver(base_feature[0], 'fcard', counter)
        return result

    def group_cardinality_check(self, key):
        logging.debug(f'Checking group cardinality for {key}.')
        gcards = self.get_wfml_data('Cardinalities.Group')
        print(gcards)
        base_feature = key.split('.')
        logging.debug(f'Base Feature: {base_feature}')
        res = ''
        if len(base_feature) > 1:
            for subfeature in base_feature[:-1]:
                if res == '':
                    res = subfeature
                else:
                    res = f'{res}.{subfeature}'
            region = self.get_wfml_data(f'Namespace.{res}')
            counter = len(region.keys())
            if res in gcards.keys():
                key_cardinality = gcards[base_feature[0]]
                if key_cardinality == 'xor':
                    if counter != 1:
                        result = False
                    else:
                        result = True
                elif key_cardinality == 'or':
                    result = True
                else:
                    result = self.cardinality_solver(key, 'fcard', counter)
            else:
                result = True
        else:
            result = True
        return result

    def keys_check(self, configuration, region):
        keys = {}
        for key, value in configuration.items():
            keys = self.key_check({key: value}, region, keys)
        return keys

    def check_configuration(self, description, configuration):
        self.initialize_product(description)
        self.clear_wfml_data('Namespace')
        for key in configuration.keys():
            self.update_wfml_data('Namespace', {key: configuration[key]})

        self.solve_constraints()
        logging.debug(pprint.pprint(self.show_wfml_data()))
        keys = self.keys_check(configuration, self.get_wfml_data('NamespaceInitial'))

        print(keys)


if __name__ == '__main__':
    this_folder = dirname(__file__)
    print(this_folder)
    description = open(join(this_folder, 'configuration.tx')).read()
    print(description)
    with open(join(this_folder, 'configuration.json')) as json_file:
        configuration = json.load(json_file)
    api = textX_API()
    api.check_configuration(description, configuration)
    pass
