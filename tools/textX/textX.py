import json

from os.path import join, dirname
from textx import metamodel_from_str
from textx.export import metamodel_export, model_export

# Global variable namespace
global_namespace = {}


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


class prec20(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<=>':
                pass
        return ret

class prec19(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '=>':
                pass
        return ret

class prec18(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '||':
                pass
        return ret

class prec17(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'xor':
                pass
        return ret

class prec16(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '&&':
                pass
        return ret

class prec15(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'U' or operation == 'untill':
                pass
        return ret

class prec14(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == 'W' or operation == 'weakuntill':
                pass
        return ret

class prec13(ExpressionElement):
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

class prec12(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        if ret == '!':
            pass
        return ret

class prec11(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<':
                pass
            elif operation == '>':
                pass
            elif operation == '==':
                pass
            elif operation == '>=':
                pass
            elif operation == '<=':
                pass
            elif operation == '!=':
                pass
            elif operation == 'in':
                pass
            elif operation == 'not in':
                pass
        return ret

class prec10(ExpressionElement):
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

class prec7(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        if ret == 'min':
            pass
        elif ret == 'max':
            pass
        return ret

class prec6(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        if ret == 'sum':
            pass
        elif ret == 'product':
            pass
        elif ret == '#':
            pass
        return ret

class prec5(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '<:':
                pass
        return ret

class prec4(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == ':>':
                pass
        return ret

class prec3(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == ',':
                pass
            elif operation == '++':
                pass
        return ret

class prec2(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '--':
                pass
        return ret

class prec1(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        global model
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            if operation == '**':
                pass
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

class prec0(ExpressionElement):
    @property
    def value(self):
        ret = self.op[0].value
        for operation, operand in zip(self.op[1::2], self.op[2::2]):
            right_value = operand.value
            if operation == '=' and ret in global_namespace:
                print(f"Level 0 assignment operation: {ret} {operation} {right_value}")
                global_namespace[ret] = right_value
            else:
                raise Exception(f'Parameter {ret} is not defined.')
            if operation == '.':
                pass
            if operation == '&':
                pass
        return ret


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
        elif type(op) is str:
            print(f"String object: {op}")
            return op
        else:
            raise Exception('Unknown variable "{}" at position {}'
                            .format(op, self._tx_position))

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

def to_json(model):
    result = {}
    for element in model.elements:
        if cname(element) == "Clafer" and element.abstract is None:
            result[element.name] = element.namespace
    return result

def main(debug=False):
    filecopy = open('clafer.tx', "r")
    grammar = filecopy.read()
    this_folder = dirname(__file__)
    filecopy = open('test.cf', "r")
    model_str = filecopy.read()
    mm = metamodel_from_str(grammar, classes=[Expression, prec0, prec1, prec2, prec3,
                                              prec4, prec5, prec6, prec7, prec8,
                                              prec9, prec10, prec11, prec12, prec13,
                                              prec14, prec15, prec16, prec17,
                                              prec18, prec19, prec20, term])
    metamodel_export(mm, join(this_folder, 'meta.dot'))

    # Meta-model knows how to parse and instantiate models.
    global model, global_namespace
    model = mm.model_from_str(model_str)
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
            constraint(element)
    for element in model.elements:
        if cname(element) == "Clafer":
            root_clafer_constraints(element)

    print(json.dumps(to_json(model), sort_keys=True, indent=4))
    with open('test.json', 'w', encoding='utf-8') as f:
        json.dump(to_json(model), f, ensure_ascii=False, indent=4)


if __name__ == '__main__':
    main()
