import logging

from core.expressions.expression_base import ExpressionElement


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
        left, operation, right = self._get_value(self.op[0]._parse(self.mapping_md, self.constr_md)),
        self.op[1],
        self._get_value(self.op[2]._parse(self.mapping_md, self.constr_md))

        # Perform list union if such operation exist.
        if operation == ',' or operation == '++':
            left_is_list = isinstance(left, list)
            right_is_list = isinstance(right, list)
            if left_is_list and right_is_list:
                ret = list(set(left) | set(right))
            elif not left_is_list:
                raise Exception(f'Parameter {left} is not a list.')
            elif not right_is_list:
                raise Exception(f'Parameter {right} is not a list.')
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
        left, operation, right = self._get_value(self.op[0]._parse(self.mapping_md, self.constr_md)),
        self.op[1],
        self._get_value(self.op[2]._parse(self.mapping_md, self.constr_md))

        # Perform list difference if such operation exist.
        if operation == '--':
            left_is_list = isinstance(left, list)
            right_is_list = isinstance(right, list)
            if left_is_list and right_is_list:
                ret = list(set(left) - set(right))
            elif not left_is_list:
                raise Exception(f'Parameter {left} is not a list.')
            elif not right_is_list:
                raise Exception(f'Parameter {right} is not a list.')
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
        left, operation, right = self._get_value(self.op[0]._parse(self.mapping_md, self.constr_md)),
        self.op[1],
        self._get_value(self.op[2]._parse(self.mapping_md, self.constr_md))

        # Perform list merge (without duplicates) if such operation exist.
        if operation == '--':
            left_is_list = isinstance(left, list)
            right_is_list = isinstance(right, list)
            if left_is_list and right_is_list:
                ret = list(set(left) & set(right))
            elif not left_is_list:
                raise Exception(f'Parameter {left} is not a list.')
            elif not right_is_list:
                raise Exception(f'Parameter {right} is not a list.')

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
        left, operation, right = self._get_value(self.op[0]._parse(self.mapping_md, self.constr_md)),
        self.op[1],
        self._get_value(self.op[2]._parse(self.mapping_md, self.constr_md))

        # Perform list concatenation/merge (with duplicates) if such operation exist.
        if operation in ['..', '&']:
            left_is_list = isinstance(left, list)
            right_is_list = isinstance(right, list)
            if left_is_list and right_is_list:
                ret = left + right if operation == '..' else list(set(left) & set(right))
            elif not left_is_list:
                raise Exception(f'Parameter {left} is not a list.')
            elif not right_is_list:
                raise Exception(f'Parameter {right} is not a list.')
        return ret
