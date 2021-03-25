import ast
import copy
import json
import itertools
import pandas as pd
import re

from collections import defaultdict
from functools import reduce
import networkx as nx
from os.path import join, dirname
from textx import metamodel_from_file, metamodel_from_str, get_location
from textx.export import metamodel_export, model_export

# Global variable namespace
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
        global exception_flag, cardinality_flag
        self.exception_flag = False
        for operator, statement, true_exp in zip(self.op[0::4], self.op[1::4], self.op[2::4]):
            if operator == 'if' and cross_tree_check:
                statement.value
                true_exp.value
                if len(self.op) > 3:
                    else_exp = self.op[3::4]
                    else_exp.value
                ret = None
            elif operator == 'if':
                print("Level 23 IF THEN ELSE statement.")
                if exception_flag is False:
                    print("Level 23 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = statement.value
                if self.exception_flag is True:
                    exception_flag = False
                cardinality_flag = None
                if ret:
                    ret = true_exp.value
                elif not ret:
                    if len(self.op) > 3:
                        else_exp = self.op[3::4]
                        ret = else_exp.value
                    else:
                        return None
                else:
                    if self.exception_flag is True:
                        ol = self._tx_position_end - self._tx_position
                        msg = ''.join(('Expression operation IF returned not boolean',
                                       ' was not satisfied.\n',
                                       f'Error position: Line {get_location(self)["line"]},',
                                       f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                       f' Filename {get_location(self)["filename"]}\n'))
                        raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec22(ExpressionElement):
    @property
    def value(self):
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<=>' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '<=>':
                print("Level 22 boolean IFF operation")
                if exception_flag is False:
                    print("Level 22 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
                ret = (ret % 2 == 0) == (ret % operand.value == 0)
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation IFF ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec21(ExpressionElement):
    @property
    def value(self):
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '=>' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '=>':
                print("Level 21 boolean IMPLIES operation")
                if exception_flag is False:
                    print("Level 21 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
                ret = not(ret) or operand.value
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation IMPLIES ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec20(ExpressionElement):
    @property
    def value(self):
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '||' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '||':
                print("Level 20 boolean OR operation")
                if exception_flag is False:
                    print("Level 20 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
                ret = ret or operand.value
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation OR ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec19(ExpressionElement):
    @property
    def value(self):
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'xor' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == 'xor':
                if exception_flag is False:
                    print("Level 19 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                print("Level 19 boolean XOR operation")
                ret = self.op[0].value
                ret = bool(ret) ^ bool(operand.value)

                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation XOR ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec18(ExpressionElement):
    @property
    def value(self):
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '&&' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '&&':
                print("Level 18 boolean AND operation")
                if exception_flag is False:
                    print("Level 18 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
                ret = ret and operand.value
                if not ret and self.exception_flag is True:
                    ol = self._tx_position_end - self._tx_position
                    msg = ''.join((f'Expression operation AND ({self.op[0].value} {operation} {operand.value})',
                                   ' was not satisfied.\n',
                                   f'Error position: Line {get_location(self)["line"]},',
                                   f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                                   f' Filename {get_location(self)["filename"]}\n'))
                    raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec17(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'U' or operation == 'untill':
                pass
        return ret

class prec16(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'W' or operation == 'weakuntill':
                pass
        return ret

class prec15(ExpressionElement):
    @property
    def value(self):
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
        global exception_flag
        self.exception_flag = False
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation == '!' and cross_tree_check:
                operand.value
            if operation == '!':
                if exception_flag is False:
                    print("Level 14 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                print("Level 14 boolean NO operation")
                ret = not(operand.value)
                if not ret and self.exception_flag is True:
                    raise Exception(f'Expression operation {operation} {operand.value} was not satisfied.')
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value

        return ret

class prec13(ExpressionElement):
    @property
    def value(self):
        global mapping_current
        global exception_flag
        self.exception_flag = False
        ret = False
        if mapping_iter == 0:
            mapping_current = []
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if exception_flag is False:
                print("Level 13 Exception flag.")
                exception_flag = True
                self.exception_flag = True
            operand.value
            if mapping_iter < mapping_iter_sum and len(self.op) > 1:
                mapping_current.append(self.op[1].value)
                print(f'Mapping Current append {self.op[1].value} mapping iter {mapping_iter}')
            if mapping_iter == mapping_iter_sum - 1 and len(self.op) > 1:
                number = mapping_current.count(True)

                print(f'Check Operation {operation}. Values {mapping_current}')
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
                if ret is False and self.exception_flag is True:
                    raise Exception(f'Expression operation {operation} {mapping_current} was not satisfied.')
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret


class prec12(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):

            if operation in ['<', '>', '==', '>=', '<=', '!=', 'in', 'not in']:
                if exception_flag is False:
                    print("Level 12 Exception flag.")
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
                print(f'{ret} {operation} {operand.value}')
            if operation in ['<', '>', '==', '>=', '<=', '!=', 'in', 'not in'] and cross_tree_check:
                self.exception_flag = False
                self.op[0].value
                operand.value
            elif operation == '<':
                ret = ret < operand.value
                print("Level 12 comparison < operation")
            elif operation == '>':
                ret = ret > operand.value
                print("Level 12 comparison > operation")
            elif operation == '==':
                ret = ret == operand.value
                print("Level 12 comparison == operation")
            elif operation == '>=':
                ret = ret >= operand.value
                print("Level 12 comparison >= operation")
            elif operation == '<=':
                ret = ret <= operand.value
                print("Level 12 comparison <= operation")
            elif operation == '!=':
                ret = ret != operand.value
                print("Level 12 comparison != operation")
            elif operation == 'in':
                ret = ret in operand.value
                print("Level 12 comparison in operation")
            elif operation == 'not in':
                ret = ret not in operand.value
        if ret is False and self.exception_flag is True:
            ol = self._tx_position_end - self._tx_position
            msg = ''.join((f'Expression operation ({self.op[0].value} {operation} {operand.value})',
                           ' was not satisfied.\n',
                           f'Error position: Line {get_location(self)["line"]},',
                           f' Column {get_location(self)["col"]}-{get_location(self)["col"] + ol},',
                           f' Filename {get_location(self)["filename"]}\n'))
            raise Exception(msg)
        if self.exception_flag is True:
            exception_flag = False
        if len(self.op) == 1:
            ret = self.op[0].value
        return ret

class prec11(ExpressionElement):
    @property
    def value(self):
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '=' and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '=':
                check = self.op[0].update
                print(f"Level 10 assignment operation: {check} {operation} {right_value} {cardinality_flag}")
                if re.match(r'(\w+\.)+\w+', check) and cardinality_flag is None:
                    path = check.split('.')
                    path.append('value')
                    print('CHECK1')
                    try:
                        assign = right_value if type(right_value) != str else ast.literal_eval(right_value)
                    except ValueError:
                        assign = right_value
                    try:
                        print('CHECK2')
                        global current_namespace
                        ret = current_namespace
                        for section in path:
                            ret = ret[section]
                        print('Assigned to Current')
                        current_namespace = self.update_nested_dict(current_namespace, path, assign)
                    except Exception:
                        global global_namespace
                        print('CHECK3')
                        ret = global_namespace
                        for section in path:
                            ret = ret[section]
                        print(f'Assigned to Global {path} {assign}')
                        global_namespace = self.update_nested_dict(global_namespace, path, assign)
                        ret = global_namespace
                        for section in path:
                            ret = ret[section]
                            print(f'RET: {ret}')
                elif re.match(r'(\w+\.)+\w+', check) and cardinality_flag == 'fcard':
                    print('CHECK4')
                    from wizard.views import card_update
                    print(f'FCARDUPD: {ret} {right_value}')
                    card_update('fcard', {ret: right_value})
                else:
                    print('CHECK5')
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
        print(f'Full path: {path_list}')
        for path_item in path_list[:-1]:
            try:
                cur = cur[path_item]
            except KeyError:
                cur = cur[path_item] = {}

        cur[path_list[-1]] = value
        print(f'Value was set {path_list[-1]} {value}')
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in ['+', '-'] and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '+':
                print(f"Level 9 addition operation: {ret} {operation} {right_value}")
                ret += right_value
            elif operation == '-':
                print(f"Level 9 subtraction operation: {ret} {operation} {right_value}")
                ret -= right_value
        return ret

    @property
    def update(self):
        return self.op[0].update

class prec8(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in ['*', '/', '%'] and cross_tree_check:
                self.op[0].value
                operand.value
            elif operation == '*':
                print(f"Level 8 multiplication operation: {ret} {operation} {right_value}")
                ret *= right_value
            elif operation == '/':
                print(f"Level 8 division operation: {ret} {operation} {right_value}")
                ret /= right_value
            elif operation == '%':
                print(f"Level 9 remainder operation: {ret} {operation} {right_value}")
                ret %= right_value
        return ret

    @property
    def update(self):
        return self.op[0].update

class prec7(ExpressionElement):
    @property
    def value(self):
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation in ['min', 'max'] and cross_tree_check:
                operand.value
            elif operation == 'min':
                print(f"Level 8 min operation: {operation}")
                ret = min(operand.value)
            elif operation == 'max':
                print(f"Level 8 max operation: {operation}")
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
        for operation, operand in zip(self.op[0::2], self.op[1::2]):
            if operation in ['sum', 'product', '#'] and cross_tree_check:
                operand.value
            elif operation == 'sum':
                print(f"Level 7 sum operation: {operation}")
                ret = sum(operand.value)
            elif operation == 'product':
                print(f"Level 7 product operation: {operation}")
                ret = reduce((lambda x, y: x * y), operand.value)
            elif operation == '#':
                print(f"Level 7 count operation: {operation}")
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in [',', '++'] and cross_tree_check:
                self.op[0].value
                operand.value
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '--' and cross_tree_check:
                self.op[0].value
                operand.value
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '**' and cross_tree_check:
                self.op[0].value
                operand.value
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
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation in ['..', '&'] and cross_tree_check:
                self.op[0].value
                operand.value
            if operation == '..' and type(ret) == list and type(right_value) == list:
                ret = ret + right_value
            elif operation == '..' and type(ret) != list:
                raise Exception(f'Parameter {ret} is not list.')
            elif operation == '..' and type(right_value) != list:
                raise Exception(f'Parameter {right_value} is not list.')
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
        op = self.op
        global unvalidated_params, mapping_iter_sum
        if cross_tree_check:
            if type(op) is str and op not in keywords and re.match(r'(\w+\.)+\w+', op):
                path = op.split('.')
                try:
                    res = current_namespace
                    for section in path:
                        res = res[section]
                except Exception:
                    try:
                        res = global_namespace
                        for section in path:
                            res = res[section]
                        global cross_tree_clafers, cross_tree_clafers_full
                        cross_tree_clafers.append([current_cross_tree, path[0]])
                        cross_tree_clafers_full.append(op)
                    except Exception:
                        print('ok')
        else:
            if type(op) in {int, float}:
                print(f"Operation object: {op} with type {type(op)}")
                return op
            elif isinstance(op, ExpressionElement):
                print(f"Operation object: {op} with value {type(op)}")
                return op.value
            elif op in global_namespace and global_namespace[op] is not None:
                print("Namespace")
                return global_namespace[op]['value']
            elif op in current_namespace and current_namespace[op] is not None:
                print("Namespace")
                check = current_path + '.' + op
                print(f'Check: {check}, current path {current_path}')
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
                    unvalidated_params.append(op)
                return current_namespace[op]['value']
            elif type(op) is bool:
                return op
            elif type(op) is str and op not in keywords:
                print(f"String object: {op}")
                if re.match(r'\{.+\}', op):
                    op = op.replace('{', '').replace('}', '').replace(' ', '')
                    print("List object")
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
                    print(op)
                elif re.match(r'(\w+\.)+\w+', op):
                    if op in mappings.keys():
                        mapping_iter_sum = len(mappings[op])
                        op = mappings[op][mapping_iter]
                    path = op.split('.')
                    if path[0] == 'fcard' or path[0] == 'gcard':
                        global cardinality_flag
                        cardinality_flag = path[0]
                        from wizard.views import get_card
                        card = get_card()
                        path = path[1:]

                        f_p = ''
                        for section in path:
                            if f_p == '':
                                f_p = section
                            else:
                                f_p = f_p + '.' + section
                        full_path = current_path + '.' + f_p
                        if full_path in mappings.keys():
                            mapping_iter_sum = len(mappings[full_path])
                            full_path = mappings[full_path][mapping_iter]
                        print(f'FullPath {full_path}')
                        print(f'MappingKeys {mappings.keys()}')
                        print(f'Mapping Table {card}')
                        try:
                            res = card[cardinality_flag][full_path]
                        except KeyError:
                            raise Exception(f'No such key {full_path} in {card[cardinality_flag]}')
                    else:
                        try:
                            unvalidated_params.append(op)
                            res = current_namespace
                            print(f'namespace: {res}')
                            print(f'path: {path}')
                            for section in path:
                                res = res[section]
                            res = res['value']
                        except Exception:
                            res = global_namespace
                            for section in path:
                                res = res[section]
                            res = res['value']
                    op = res
                    print(res)
                return op
            else:
                raise Exception('Unknown variable "{}" at position {}'
                                .format(op, self._tx_position))

    @property
    def update(self):
        op = self.op
        global mapping_iter_sum
        if op in current_namespace:
            print("Namespace update")
            check = current_path + '.' + op
            print(f'Check: {check}, current path {current_path}')
            print(global_namespace)
            if check in mappings.keys():
                mapping_iter_sum = len(mappings[check])
                new_op = mappings[check][mapping_iter].split('.')[-1]
                if new_op not in current_namespace.keys() or new_op == op:
                    path = mappings[check][mapping_iter].split('.')
                    res = global_namespace
                    for section in path:
                        res = res[section]
                op = mappings[check][mapping_iter]
                print(f'OP {op}')
            return op
        elif re.match(r'(\w+\.)+\w+', op):
            if op in mappings.keys():
                mapping_iter_sum = len(mappings[op])
                op = mappings[op][mapping_iter]
            path = op.split('.')
            if path[0] == 'fcard' or path[0] == 'gcard':
                global cardinality_flag
                cardinality_flag = path[0]
                path = path[1:]
            print(f'PATH!!!!!!{path}')
            try:
                res = current_namespace
                for section in path:
                    res = res[section]
                res = res['value']
            except Exception:
                print(f'Local Namespace does not contain variable {op}')
                res = global_namespace
                for section in path:
                    res = res[section]
                res = res['value']
            if cardinality_flag is True:
                op = ''
                for elem in path:
                    if op == '':
                        op = elem
                    else:
                        op = op + '.' + elem
            print(f'Return {op} value')
            return op
        else:
            raise Exception(f'Global namespace does not contain variable {op}')

def cname(o):
    return o.__class__.__name__


def constraint(constraint):
    print("_____________________")
    exp = constraint.name
    print(exp.value)
    print(global_namespace)


def root_clafer(clafer, namespace=None):
    if namespace is None:
        return_trigger = False
    else:
        return_trigger = True
    print("______________________________")
    print(f"This is Clafer: {clafer.name}")
    print(f"Is it abstract: {clafer.abstract}")
    print(f"Its group cardinality: {clafer.gcard}")
    print(f"Its feature cardinality: {clafer.fcard}")
    if clafer.super is not None:
        print(f"It has super instance: {clafer.super.value}")
    else:
        print(f"It has super instance: {clafer.super}")
    print(f"It has reference: {clafer.reference}")
    print(f"It has init expression: {clafer.init}")
    group = {}

    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer" and child1.reference is None:
                group = root_clafer(child1, group)
            elif cname(child1) == "Clafer" and child1.reference is not None:
                group = property_clafer(child1, group)
    clafer.namespace = group
    clafer.super_direct = []
    clafer.super_indirect = []
    print(f"Clafer namespace: {clafer.namespace}")
    print("______________________________")
    if return_trigger:
        namespace[clafer.name] = group
        return namespace


def get_model_cardinalities():
    fcard = {}
    gcard = {}
    for element in model.elements:
        if cname(element) == "Clafer":
            fcard.update(clafer_fcard(element))
            gcard.update(clafer_gcard(element))
    return fcard, gcard

def clafer_fcard(clafer, prefix=None):
    fcard = {}
    if prefix:
        name = prefix + '.' + clafer.name
    else:
        name = clafer.name
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer":
                fcard.update(clafer_fcard(child1, name))
    if clafer.fcard:
        fcard.update({name: clafer.fcard})
    return fcard

def clafer_gcard(clafer, prefix=None):
    gcard = {}
    if prefix:
        name = prefix + '.' + clafer.name
    else:
        name = clafer.name
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer":
                gcard.update(clafer_gcard(child1, name))
    if clafer.gcard:
        gcard.update({name: clafer.gcard})
    return gcard

def cardinality_solver(clafer, card_type, card_value):
    fcard, gcard = get_model_cardinalities()
    if card_type == 'fcard':
        card = fcard[clafer]
    else:
        card = gcard[clafer]
    x = card_value
    res = []
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
        print(f'Result: {x} lies in interval {card}')
        return True
    else:
        return Exception(f'Result: {x} not lies in interval {card}')

def get_abstract_clafers():
    global abstract_clafers
    return abstract_clafers

def update_abstract_clafers():
    global abstract_clafers
    for element in model.elements:
        if cname(element) == "Clafer":
            for element in clafer_abstract(element):
                abstract_clafers.append(element)

def clafer_abstract(clafer, prefix=None):
    abstr_clafers = []
    if prefix:
        name = prefix + '.' + clafer.name
    else:
        name = clafer.name
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer":
                res = clafer_abstract(child1, name)
                abstr_clafers = abstr_clafers + res
    if clafer.abstract:
        abstr_clafers.append(name)
    return abstr_clafers

def fullfill_abstract_dependencies():
    global abstract_dependencies, model
    for clafer in abstract_clafers:
        res = []
        for element in model.elements:
            if cname(element) == "Clafer":
                for elem in find_abstract(element, clafer):
                    res.append(elem)
        abstract_dependencies.update({clafer: res})
    print(f'Abstract dependencies fullfiled: {abstract_dependencies}')

def find_abstract(clafer, abstract, prefix=None):
    abstr_clafers = []
    if prefix:
        name = prefix + '.' + clafer.name
    else:
        name = clafer.name
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer":
                res = find_abstract(child1, abstract, name)
                abstr_clafers = abstr_clafers + res
    print(clafer.abstract)
    print(f'SUPERDIRECT: {type(clafer)}')
    from pprint import pprint
    # pprint(vars(clafer))
    if abstract in clafer.super_direct or abstract in clafer.super_indirect:
        abstr_clafers.append(name)
    return abstr_clafers

def get_abstract_dependencies():
    global abstract_dependencies
    return abstract_dependencies

def topological_sort(dependency_pairs):
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


def staging(cross_tree_dependencies):
    global cycles, cross_tree_list

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
        print(f'Cycle cycle{index} contain elements: {cycle}')
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
    fcard, gcard = get_model_cardinalities()
    fcardinalities = [{'fcard': fcard}]
    gcardinalities = [{'gcard': gcard}]
    # Combine cycle and not-cycle dependencies to form final list
    res = new_dep2 + new_dep
    res = topological_sort(res)
    result = res[0] + independent_clafers
    # Add independent cycles
    index = 0
    for cycle in nx.simple_cycles(G):
        index += 1
        print("IS HERE?")
        if f'cycle{index}' not in result:
            print('YES')
            result.append(f'cycle{index}')
        else:
            print("NO")
    result.reverse()
    ret_val = fcardinalities + gcardinalities + result
    print(f'There are {len(res[0])} stages for cross-tree dependencies: {res[0]}')
    print(f'Cycled clafers: {cycled}')
    print(f'Additional independent clafers: {independent_clafers}')
    print(f'Final result: {result}')
    return ret_val

def recursive_items(dictionary, prefix=None):
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
                yield from recursive_items(value, prefix=prefix_upd)
        else:
            if not prefix:
                yield (key, value)
            else:
                yield (prefix + "." + key, value)

def update_namespace(new, inner=None, topkey=None):
    global global_namespace
    if not inner:
        if topkey:
            inner = global_namespace
        else:
            raise(Exception("NO TOPKEY PROVIDED"))

    for k, v in new.items():
        if re.match(r'(\w+\.)+\w+', k):
            k = k.split('.')
        if k[0].split('_')[0] in inner.keys() and topkey and k[0] not in inner.keys():
            inner[k[0]] = copy.deepcopy(inner[k[0].split('_')[0]])
        for key, value in inner.items():

            if k == key:
                if inner[k]['type'] == 'boolean':
                    v = json.loads(v.lower())
                inner[k].update({'value': v})
                break
            elif k[0] == key:
                inner_copy = inner
                for section in k[:-1]:
                    inner_copy = inner_copy[section]
                if k[-1] in inner_copy.keys():
                    if inner_copy[k[-1]]['type'] == 'boolean':
                        print(f'INS V {v}')
                        v = json.loads(v.lower())
                        print(f'TRA V {v}')
                    inner_copy[k[-1]].update({'value': v})
                    print(f'INSERTED {k} with value {v} into {key} and value {value}')
                else:
                    print(f'INNERCOPY: {inner_copy}')
                    original = k[-1].split('_')[0]
                    if 'type' in inner_copy[original].keys():
                        if inner_copy[original]['type'] == 'boolean':
                            v = json.loads(v.lower())
                        inner_copy[k[-1]] = {'value': v, 'type': inner_copy[original]['type']}
                    else:
                        inner_copy[k[-1]] = copy.deepcopy(v)


def read_keys():
    top_keys = global_namespace.keys()
    keys = {}
    for topkey in top_keys:
        print(topkey)
        subkey = []
        for key, value in recursive_items(global_namespace[topkey]):
            subkey.append({key: value})
        keys[topkey] = subkey
    return keys

def read_certain_key(path, only_childs):
    abs_flag = False
    path_flag = True
    path_check = global_namespace
    check = ''
    print(f'Read path {path}')
    for part in path.split('.'):
        try:
            path_check = path_check[part]
        except KeyError:
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
        print(f'Take Global namespace {ns}')
        p = path
    elif path_flag is False and abs_flag is True:
        ns = abstract_namespace
        p = check
        print(f'Take Abstract namespace {ns}')
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
        for k, v in recursive_items(ns):
            subkey.append({k: v})
    key[path] = subkey
    return key

def get_cycle_keys():
    return cycles

def get_namespace():
    return global_namespace

def get_mappings():
    return mappings

def write_to_keys(input_data=None):
    for k, v in input_data.items():
        update_namespace(new={k: v}, topkey=True)

def group_clafer(clafer, namespace):
    print("______________________________")
    print(f"This is group Clafer: {clafer.name}")
    group = {}
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer" and child1.reference is None:
                group_clafer(child1, group)
            elif cname(child1) == "Clafer" and child1.reference is not None:
                property_clafer(child1, group)
    namespace[clafer.name] = group
    clafer.namespace = group
    return namespace

def property_clafer(clafer, namespace):
    print("______________________________")
    print(f"This is property Clafer: {clafer.name}")
    print(f"It has reference: {clafer.reference}")
    sub = {'value': None, 'type': clafer.reference.value}
    clafer.super_direct = []
    clafer.super_indirect = []
    namespace[clafer.name] = sub
    return namespace
    print("______________________________")

def root_clafer_constraints(clafer, isroot, flag=True):
    print("______________________________")
    print(f'ROOT CLAFER {clafer.name} constraints')
    print(clafer.namespace)
    global global_namespace, current_namespace, unvalidated_params, current_path
    if isroot is True:
        current_path = clafer.name
    else:
        local_path = current_path
        current_path = current_path + '.' + clafer.name
    from wizard.views import check_gcard
    if flag is False:
        check = check_gcard(current_path)
        print(f'GC_CHECK: {check}')
    else:
        check = True
    if check is True:
        current_namespace = clafer.namespace
        counter = 0
        for child in clafer.nested:
            for child1 in child.child:
                unvalidated_params = []
                print(f'CNAME {cname(child1)} {child1.name}')
                if cname(child1) == "Constraint":
                    counter += 1
                    global mapping_iter, mapping_iter_sum, cardinality_flag
                    cardinality_flag = None
                    mapping_iter = 0
                    mapping_iter_sum = 1
                    print(f'CONSTRAINTNAME: {child1.name}')
                    while mapping_iter < mapping_iter_sum:
                        unvalidated_params = []
                        child1.name.value
                        mapping_iter += 1
                    clafer.namespace = current_namespace
                    if isroot is True:
                        global_namespace[clafer.name] = current_namespace
                elif cname(child1) == 'Clafer' and isinstance(child1.reference, type(None)):
                    clafer.namespace[child1.name].update(root_clafer_constraints(child1, False, flag))
                    current_namespace = clafer.namespace
        current_namespace = {}
        print(f'For clafer {clafer.name} there is/are {counter} constraint expression(s) evaluated.')
        print(f'Clafer namespace: {clafer.namespace}')
    if isroot is True:
        current_path = ''
    else:
        current_path = local_path
    return clafer.namespace

def cardinalities_upd(card):
    global cardinalities_list
    cardinalities_list = card

def get_card():
    global cardinalities_list
    return cardinalities_list

def get_cross_tree_list():
    global cross_tree_list, cross_tree_clafers_full
    return cross_tree_list, cross_tree_clafers_full

def super_clafer(model, clafer):
    if clafer.super is not None:
        for element in model.elements:
            if element.name == clafer.super.value:
                super_copy = copy.deepcopy(element.namespace)
                clafer.namespace.update(super_copy)
                if len(element.nested) > 0:
                    if clafer.nested == []:
                        clafer.nested = element.nested
                        repl = []
                        for child in element.nested:
                            for child1 in child.child:
                                repl.append(child1)
                            child.child = repl
                    else:
                        for child in clafer.nested:
                            for child1 in element.nested:
                                for child2 in child1.child:
                                    print(f'Child {child} Child1 {child1} Child2 {child2}')
                                    if child2 not in child.child:
                                        print(f'Parent constraint {child2} was merged to {child}')
                                        child.child.append(child2)
                clafer.super_direct.append(element.name)
                if element.super_direct:
                    for rel in element.super_direct:
                        clafer.super_indirect.append(rel)
                    for rel in element.super_indirect:
                        clafer.super_indirect.append(rel)
                print('___________________________________________')
                print(f'For clafer {clafer.name} super clafer namespace was merged')
                print(f'Namespace: {clafer.namespace}')
                print(f'SUPERDIRECT: {clafer.super_direct}')
                print(f'SUPERINDIRECT: {clafer.super_indirect}')
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Clafer":
                super_clafer(model, child1)

def group_cardinality(model, clafer):
    pass

def reset_exception_flag():
    global exception_flag
    exception_flag = False
    print(f'Global exception flag was reset: {exception_flag}')

def get_unvalidated_params():
    global unvalidated_params
    return unvalidated_params

def to_json(model):
    result = {}
    for element in model.elements:
        if cname(element) == "Clafer" and element.abstract is None:
            if element.reference is not None:
                result[element.name] = global_namespace[element.name]
            else:
                result[element.name] = element.namespace
    return result

def mapping(original, copy):
    global mappings
    print(f'NEW MAPPING {original} {copy}')
    if original not in mappings.keys():
        mappings.update({original: []})
    mappings[original].append(copy)
    mappings[original] = list(dict.fromkeys(mappings[original]))

def update_global_namespace(key, value):
    global global_namespace
    k_s = key.split('_')
    print(f'UPD NS KS {k_s}')
    if k_s[0] == 'fcard' and len(k_s[1].split('.')) > 1:
        ret = global_namespace
        for part in k_s[1].split('.'):
            ret = ret[part]
        for index in range(0, value):
            write_to_keys({k_s[1] + '_' + str(index): ret})




def validate_clafer(clafer):
    global exception_flag, mappings, current_path, unvalidated_params
    current_path = ''
    try:
        for element in model.elements:
            if cname(element) == "Constraint":
                exception_flag = False
                constraint(element)
        for element in model.elements:
            if cname(element) == "Clafer" and element.name == clafer:
                exception_flag = False
                root_clafer_constraints(element, True, False)
        current_path = ''
        unvalidated_params = []
        return True
    except Exception as e:
        print('EXCEPTION OCCURED')
        print(f'{e}')
        current_path = ''
        return e

def reset_global_variables():
    global global_namespace, current_namespace, current_path, cross_tree_clafers, cross_tree_list
    global cycles, exception_flag, cross_tree_check, current_cross_tree, unvalidated_params
    global abstract_clafers, abstract_dependencies, mappings, mapping_iter_sum
    global mapping_iter, cardinalities_list, abstract_namespace
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

def clear_json_trash(dictionary):
    flag = False
    cflag = False
    rm_keys = []
    for key, value in dictionary.items():
        if isinstance(value, dict) and 'value' not in value.keys():
            dictionary[key], c_flag = clear_json_trash(value)
            if dictionary[key] == {} or dictionary[key] is None:
                rm_keys.append(key)
        elif isinstance(value, dict) and 'value' in value.keys():
            if value['value'] is None:
                rm_keys.append(key)
            else:
                flag = True
                dictionary[key] = value['value']
    for key in rm_keys:
        dictionary.pop(key, None)
    if cflag is True:
        flag = True
    return dictionary, flag

def save_json():
    # preprint = to_json(model)
    global global_namespace
    preprint = copy.deepcopy(global_namespace)
    res, _ = clear_json_trash(preprint)
    print(f'PREPRINT {preprint}')
    print(f'FINALMODEL {res}')

    with open('test.json', 'w', encoding='utf-8') as f:
        json.dump(res, f, ensure_ascii=False, indent=4)
    return res


def main_stub(descr):
    a = """
Model: elements*=Element;

Element: Clafer | Goal | Constraint | Assertion;

Constraint: "[" name=prec23 "]";
Assertion: "assert" "[" name=prec23 "]";
Goal: 
    "<<"
    gtype=Goaltype
    name=prec23 
    ">>"
;

Goaltype: "min" | "max" | "minimize" | "maximize";
Clafer: 
    abstract=Abstract?
    gcard=Gcard?
    name=Name
    super=Super?
    reference=Reference?
    fcard=Fcard?
    init=Init?
    nested*=Nested?
;

Name: ID;
Abstract: "abstract";
Gcard: INT+[/\..|,/] | "xor" | "or" | "mux" | "opt" | Cardinterval;
Fcard: INT+[/\..|,/] | "?" | "*" | "+" | Cardinterval;
Super: ":" prec0;
Reference: "->" prec3 | "->>" prec3;
Init: "=" prec23 | ":=" prec23;
Nested: 
    "{"
    /\s*/
    child+=Element
    "}"
;
Cardinterval: INT ".." (INT | "*");

prec23:   (op='if')* op=prec22 ('then' op=prec22 ('else' op=prec22)?)*; 
prec22:   op=prec21  (op=op22   op=prec21)*;
prec21:   op=prec20  (op=op21   op=prec20)*;
prec20:   op=prec19  (op=op20   op=prec19)*;
prec19:   op=prec18  (op=op19   op=prec18)*;
prec18:   op=prec17  (op=op18   op=prec17)*;
prec17:   op=prec16  (op=op17   op=prec16)*;
prec16:   op=prec15  (op=op16   op=prec15)*;
prec15:   (op=op15)*  op=prec14;
prec14:   (op=op14)*  op=prec13;
prec13:   (op=op13)*  op=prec12;
prec12:   op=prec11  (op=op12   op=prec11)*;
prec11:   op=prec10  (op=op11   op=prec10)*;
prec10:   op=prec9  (op=op10   op=prec9)*;
prec9:   op=prec8  (op=op9   op=prec8)*;
prec8:   op=prec7  (op=op8   op=prec7)*;
prec7:   (op=op7)*  op=prec6;
prec6:   (op=op6)*  op=prec5;
prec5:   op=prec4  (op=op5   op=prec4)*;
prec4:   op=prec3  (op=op4   op=prec3)*;
prec3:   op=prec2  (op=op3   op=prec2)*;
prec2:   op=prec1  (op=op2   op=prec1)*;
prec1:   op=prec0  (op=op1   op=prec0)*;
prec0:   op=term   (op=op0   op=term)*;
term:    op=NUMBER | op = BOOL | op=ComplexName | op = ID | op = Quote | op = List | ('(' op=prec23 ')');


op22: '<=>'                                                     ;
op21: '=>'                                                      ;
op20: '||'                                                      ;
op19: 'xor'                                                     ;
op18: '&&'                                                      ;
op17: 'U' | 'until'                                             ;
op16: 'W' | 'weakuntil'                                         ;
op15: 'F' | 'eventually' | 'G' | 'globally' | 'X' | 'next'      ;
op14: '!'                                                       ;
op13:  Quant                                                    ;
op12: '<=' | '>=' | '==' | '<' | '>' | '!=' | 'in' | 'not in'   ;
op11: 'requires' | 'excludes'                                   ;
op10: '='                                                       ;
op9:  '+' | '-'                                                 ;
op8:  '*' | '/' | '%'                                           ;
op7:  'min' | 'max'                                             ;
op6:  'sum' | 'product' | '#'                                   ;
op5:  '<:'                                                      ;
op4:  ':>'                                                      ;
op3:  ',' | '++'                                                ;
op2:  '--'                                                      ;
op1:  '**'                                                      ;
op0:  '..' | '&'                                                ;

Quote: /'.+'/ | /".+"/;
List: /\{.+\}/;
ComplexName: /(\w+\.)+\w+/;

Quant: QuantNo | QuantNot | QuantLone | QuantOne | QuantSome;
QuantNo: "no";
QuantNot: "not";
QuantLone: "lone";
QuantOne: "one";
QuantSome: "some";

Comment:
  StringComment | BlockComment
;

StringComment: /\/\/.*$/;
BlockComment: /\/\*(\*(?!\/)|[^*])*\*\//;
"""
    this_folder = dirname(__file__)
    mm = metamodel_from_str(a, classes=[prec0, prec1, prec2, prec3,
                                                   prec4, prec5, prec6, prec7, prec8,
                                                   prec9, prec10, prec11, prec12, prec13,
                                                   prec14, prec15, prec16, prec17,
                                                   prec18, prec19, prec20, prec21, prec22, prec23, term],
                             autokwd=True)

    # Meta-model knows how to parse and instantiate models.
    global model, global_namespace, keywords, exception_flag, current_namespace, cross_tree_check
    global current_cross_tree, cross_tree_clafers, abstract_namespace
    reset_global_variables()
    model = mm.model_from_str(descr)
    metamodel_export(mm, join(this_folder, 'meta.dot'))
    model_export(model, join(this_folder, 'example.dot'))
    update_abstract_clafers()
    print(f'TYPE: {type(model.elements)}')
    for element in model.elements:
        if cname(element) == "Clafer":
            root_clafer(element)
    print("CLAFER DEFINITION DONE")
    for element in model.elements:
        if cname(element) == "Clafer":
            super_clafer(model, element)
    print("CLAFER SUPER RELATIONS DONE")
    fullfill_abstract_dependencies()
    for element in model.elements:
        if cname(element) == "Clafer" and element.abstract is None:
            global_namespace[element.name] = element.namespace
        elif cname(element) == "Clafer" and element.abstract is not None:
            abstract_namespace[element.name] = element.namespace
    print(f"GLOBAL NAMESPACE FULLFILLED: {global_namespace}")
    cross_tree_check = True
    for element in model.elements:
        exception_flag = False
        if cname(element) == "Constraint":
            constraint(element)
    for element in model.elements:
        exception_flag = False
        if cname(element) == "Clafer" and element.abstract is None:
            current_cross_tree = element.name
            root_clafer_constraints(element, True)
    print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
    print('Cross-tree clafers')
    cross_tree_clafers.sort()
    res_cross_tree = list(k for k, _ in itertools.groupby(cross_tree_clafers))
    # res_cross_tree = list(dict.fromkeys(cross_tree_clafers))
    print(res_cross_tree)
    print('__________________________')
    stages = staging(res_cross_tree)
    cross_tree_check = False
    return stages

def main(debug=False):
    this_folder = dirname(__file__)
    mm = metamodel_from_file('clafer.tx', classes=[prec0, prec1, prec2, prec3,
                                                   prec4, prec5, prec6, prec7, prec8,
                                                   prec9, prec10, prec11, prec12, prec13,
                                                   prec14, prec15, prec16, prec17,
                                                   prec18, prec19, prec20, prec21, prec22, prec23, term],
                             autokwd=True)
    metamodel_export(mm, join(this_folder, 'meta.dot'))

    # Meta-model knows how to parse and instantiate models.
    global model, global_namespace, keywords, exception_flag, current_namespace, cross_tree_check
    global current_cross_tree
    model = mm.model_from_file('test.cf')
    model_export(model, join(this_folder, 'example.dot'))
    for element in model.elements:
        if cname(element) == "Clafer":
            root_clafer(element)
    print("CLAFER DEFINITION DONE")
    for element in model.elements:
        if cname(element) == "Clafer" and element.super is not None:
            super_clafer(model, element)
    print("CLAFER SUPER RELATIONS DONE")
    for element in model.elements:
        if cname(element) == "Clafer" and element.abstract is None:
            global_namespace[element.name] = element.namespace
    print(f"GLOBAL NAMESPACE FULLFILLED: {global_namespace}")

    cross_tree_check = True
    for element in model.elements:
        exception_flag = False
        if cname(element) == "Constraint":
            constraint(element)
    for element in model.elements and element.abstract is None:
        exception_flag = False
        if cname(element) == "Clafer":
            current_cross_tree = element.name
            root_clafer_constraints(element, True)
    print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
    print('Cross-tree clafers')
    cross_tree_clafers.sort()
    res_cross_tree = list(k for k, _ in itertools.groupby(cross_tree_clafers))
    # res_cross_tree = list(dict.fromkeys(cross_tree_clafers))
    print(res_cross_tree)
    print('__________________________')
    stages = staging(res_cross_tree)
    cross_tree_check = False
    for element in model.elements:
        if cname(element) == "Constraint":
            exception_flag = False
            constraint(element)
    for element in model.elements:
        if cname(element) == "Clafer" and element.abstract is None:
            exception_flag = False
            root_clafer_constraints(element, True)

    print(json.dumps(to_json(model), sort_keys=True, indent=4))
    with open('test.json', 'w', encoding='utf-8') as f:
        json.dump(to_json(model), f, ensure_ascii=False, indent=4)


if __name__ == '__main__':
    main()
