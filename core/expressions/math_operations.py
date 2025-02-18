import logging

from functools import reduce

from core.expressions.expression_base import ExpressionElement


class prec10(ExpressionElement):
    @property
    def value(self):
        """
        prec10 class performs assignment operation.

        RETURN
        ret (variable type): previous level object if no prec10 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug("Level 10 assignment operation entry point")
        fname = self._get_value(self.res[0], 'Fname')
        field = self._get_value(self.res[0], 'Ftype')
        value = self._get_value(self.res[2])
        self.api.workspace.update_metadata(fname, field, value, self.constr_md['Expression'])

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
        logging.debug("Level 9 addition/subtraction operation entry point")
        ret = left = self._get_value(self.op[0]._parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, r._parse(self.mapping_md, self.constr_md)
            right = self._get_value(right)
            if operation == '+':
                ret += right
            elif operation == '-':
                ret -= right
            logging.debug(f"Level 9 {left} {operation} {right} result: {ret}")
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
        logging.debug("Level 8 multiplication/division/remainer operation entry point")
        ret = left = self._get_value(self.op[0]._parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self._get_value(r._parse(self.mapping_md, self.constr_md))
            if operation == '*':
                ret *= right
            elif operation == '/':
                ret /= right
            elif operation == '%':
                ret %= right
            logging.debug(f"Level 8 {left} {operation} {right} result: {ret}")
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
        logging.debug("Level 7 min/max/size operation entry point")
        # TODO debug checks for list type
        operation, right = self.op[0], self._get_value(self.op[1]._parse(self.mapping_md, self.constr_md))
        if operation == 'min':
            logging.debug("Level 8 min operation")
            ret = min(right)

        elif operation == 'max':
            logging.debug("Level 8 max operation")
            ret = max(right)

        elif operation == 'size':
            logging.debug("Level 8 size operation")
            ret = len(right)
        logging.debug(f"Level 7 {operation} {right} result: {ret}")
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
        logging.debug("Level 6 sum/product/count operation entry point")
        # TODO debug checks for list type
        operation, right = self.op[0], self._get_value(self.op[1]._parse(self.mapping_md, self.constr_md))
        if operation == 'sum':
            logging.debug(f"Level 7 sum operation: {operation}")
            ret = sum(right)

        elif operation == 'product':
            logging.debug(f"Level 7 product operation: {operation}")
            ret = reduce((lambda x, y: x * y), right)

        elif operation == '#':
            logging.debug(f"Level 7 count operation: {operation}")
            ret = len(right)
        logging.debug(f"Level 6 {operation} {right} result: {ret}")
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
        logging.debug("Level 50 unique x in y operation entry point")
        right = self.op[2]._parse(self.mapping_md, self.constr_md)['Fname']
        left = self._get_value(self.op[1]._parse(self.mapping_md, self.constr_md))

        a = self.api.workspace.get_feature_childrens(right, True)
        b = [x for x in a if x.rsplit('.')[-1] == left]
        values = []
        for feature in b:
            values.append(self.api.workspace.read_metadata(feature, 'Value'))
        ret = list(set(values))
        logging.debug(f"Level 5 unique {left} in {right} result: {ret}")
        return ret
