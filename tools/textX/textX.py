import json

from os.path import join, dirname
from textx import metamodel_from_file, get_location
from textx.export import metamodel_export, model_export

# Global variable namespace
global_namespace = {}
keywords = ['abstract', 'all', 'assert', 'disj', 'else', 'enum',
            'if', 'in', 'lone', 'max', 'maximize', 'min',
            'minimize', 'mux', 'no', 'not', 'one', 'opt',
            'or', 'product', 'some', 'sum', 'then', 'xor']
exception_flag = False

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
        global exception_flag
        self.exception_flag = False

        for operator, statement, true_exp, else_exp in zip(self.op[0::4], self.op[1::4], self.op[2::4], self.op[3::4]):
            if operator == 'if':
                print("Level 23 IF THEN ELSE statement.")
                if exception_flag is False:
                    exception_flag = True
                    self.exception_flag = True
                ret = statement.value
                if self.exception_flag is True:
                    exception_flag = False
                if ret:
                    ret = true_exp.value
                elif not ret:
                    ret = else_exp.value
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
            if operation == '&&':
                print("Level 22 boolean IFF operation")
                if exception_flag is False:
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
            if operation == '=>':
                print("Level 21 boolean IMPLIES operation")
                if exception_flag is False:
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
            if operation == '||':
                print("Level 20 boolean OR operation")
                if exception_flag is False:
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
            if operation == 'xor':
                if exception_flag is False:
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
            if operation == '&&':
                print("Level 18 boolean AND operation")
                if exception_flag is False:
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
            if operation == '!':
                if exception_flag is False:
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
        ret = self.op[0].value
        global exception_flag
        self.exception_flag = False

        for operation, operand in zip(self.op[1::2], self.op[2::2]):

            if operation in ['<', '>', '==', '>=', '<=', '!=', 'in', 'not in']:
                if exception_flag is False:
                    exception_flag = True
                    self.exception_flag = True
                ret = self.op[0].value
            if operation == '<':
                ret = ret < operand.value
            elif operation == '>':
                ret = ret > operand.value
            elif operation == '==':
                ret = ret == operand.value
            elif operation == '>=':
                ret = ret <= operand.value
            elif operation == '<=':
                ret = ret >= operand.value
            elif operation == '!=':
                ret = ret != operand.value
            elif operation == 'in':
                ret = ret in operand.value
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


class prec12(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        if ret == 'no':
            pass
        elif ret == 'none':
            pass
        elif ret == 'lone':
            pass
        elif ret == 'one':
            pass
        elif ret == 'some':
            pass
        return ret

class prec11(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'requires':
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
            if operation == 'excludes':
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
            if operation == '=':
                check = self.op[0].update
                print(f"Level 0 assignment operation: {check} {operation} {right_value}")
                import ast
                import re
                if re.match(r'(\w+\.)+\w+', check):
                    path = check.split('.')
                    res = global_namespace
                    for index in range(0, len(path)):
                        if index < len(path) - 1:
                            res = res.get(path[index])
                        else:
                            check = path[index]
                    try:
                        res[check] = right_value if type(right_value) != str else ast.literal_eval(right_value)
                    except ValueError:
                        res[check] = right_value
                else:
                    try:
                        global_namespace[check] = right_value if type(right_value) != str else ast.literal_eval(right_value)
                    except ValueError:
                        global_namespace[check] = right_value
            else:
                raise Exception(f'Parameter {ret} is not defined.')
        return ret
class prec9(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '+':
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
            if operation == '*':
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
            if operation == 'min':
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
            if operation == 'sum':
                print(f"Level 7 sum operation: {operation}")
                ret = sum(operand.value)
            elif operation == 'product':
                print(f"Level 7 product operation: {operation}")
                from functools import reduce
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
            if operation == ',' or operation == '++':
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
            if operation == '--' and type(ret) == list and type(right_value) == list:
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
            if operation == '**' and type(ret) == list and type(right_value) == list:
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
        if type(op) in {int, float}:
            print(f"Operation object: {op} with type {type(op)}")
            return op
        elif isinstance(op, ExpressionElement):
            print(f"Operation object: {op} with value {type(op)}")
            return op.value
        elif op in global_namespace and global_namespace[op] is not None:
            print("Namespace")
            return global_namespace[op]
        elif type(op) is bool:
            return op
        elif type(op) is str and op not in keywords:
            print(f"String object: {op}")
            import re
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
                            if element in global_namespace and global_namespace[element] is not None:
                                op[index] = global_namespace[element]
                print(op)
            elif re.match(r'(\w+\.)+\w+', op):
                path = op.split('.')
                res = global_namespace
                for section in path:
                    res = res[section]
                op = res
            return op
        else:
            raise Exception('Unknown variable "{}" at position {}'
                            .format(op, self._tx_position))

    @property
    def update(self):
        import re
        op = self.op
        if op in global_namespace:
            print("Namespace update")
            return op
        elif re.match(r'(\w+\.)+\w+', op):
            path = op.split('.')
            res = global_namespace
            for section in path:
                res = res[section]
                return op
        else:
            raise Exception(f'Namespace does not contain variable {op}')

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
    print(f"Clafer namespace: {clafer.namespace}")
    print("______________________________")
    if return_trigger:
        namespace[clafer.name] = group
        return namespace


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
    namespace[clafer.name] = None
    return namespace
    print("______________________________")

def root_clafer_constraints(clafer):
    print("______________________________")
    counter = 0
    for child in clafer.nested:
        for child1 in child.child:
            if cname(child1) == "Constraint":
                counter += 1
                clafer.namespace = clafer_constraints(child1, clafer.namespace)
            elif cname(child1) == "Clafer" and child1.reference is None:
                root_clafer_constraints(child1)
    print(f'For clafer {clafer.name} there is/are {counter} constraint expression(s) evaluated.')
    print(f'Clafer namespace: {clafer.namespace}')

def clafer_constraints(constraint, namespace):
    print("_____________________")
    global global_namespace
    global_namespace = namespace
    print(global_namespace)
    exp = constraint.name
    print(exp.value)
    namespace = global_namespace
    print(namespace)
    return namespace
    print("_____________________")

def super_clafer(model, clafer):
    for element in model.elements:
        if element.name == clafer.super.value:
            clafer.namespace = {**clafer.namespace, **element.namespace}
            print('___________________________________________')
            print(f'For clafer {clafer.name} super clafer namespace was merged')
            print(f'Namespace: {clafer.namespace}')

def group_cardinality(model, clafer):
    pass

def to_json(model):
    result = {}
    for element in model.elements:
        if cname(element) == "Clafer" and element.abstract is None:
            if element.reference is not None:
                result[element.name] = global_namespace[element.name]
            else:
                result[element.name] = element.namespace
    return result

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
    global model, global_namespace, keywords, exception_flag
    model = mm.model_from_file('test.cf')
    model_export(model, join(this_folder, 'example.dot'))
    for element in model.elements:
        if cname(element) == "Clafer":
            if element.reference is not None:
                global_namespace[element.name] = None
            root_clafer(element)
    for element in model.elements:
        if cname(element) == "Clafer" and element.super is not None:
            super_clafer(model, element)
    for element in model.elements:
        if cname(element) == "Constraint":
            exception_flag = False
            constraint(element)
    global_namespace_copy = global_namespace

    for element in model.elements:
        if cname(element) == "Clafer":
            exception_flag = False
            root_clafer_constraints(element)
    global_namespace = global_namespace_copy

    print(json.dumps(to_json(model), sort_keys=True, indent=4))
    with open('test.json', 'w', encoding='utf-8') as f:
        json.dump(to_json(model), f, ensure_ascii=False, indent=4)


if __name__ == '__main__':
    main()
