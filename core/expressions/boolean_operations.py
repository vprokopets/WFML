import logging

from core.expressions.expression_base import ExpressionElement

class prec24(ExpressionElement):
    @property
    def value(self):
        """
        prec24 class performs filter operation.

        RETURN
        ret (variable type): previous level object if no prec24 operations are not presented in constraint
                            operation result in opposite case.
        """
        logging.debug('Level 24 Operation filter x where y entry point.')
        key, condition = self._get_value(self.op[1]._parse(self.mapping_md, self.constr_md)), self.op[2]
        return self._filter(condition, key)

    def _filter(self, condition, key):
        """
        Function to filter features by constraint.

        INPUTS
        condition (type = ExpressionElement): constraint to check.
        key (type = dict): feature's namespace.

        RETURN
        res (type = list): list of filtered features.
        """
        logging.debug('Auxiliary filtering function (prec24)')
        res = []
        for k, v in self.constr_md['FilterStub'].items():
            for mapping, md in v.items():
                self.mapping_md['FilterFlag'] = {k: mapping}
                if self._get_value(condition._parse(self.mapping_md, self.constr_md)) is True:
                    res.append(md['initial'])
        self.mapping_md['FilterFlag'] = None
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

        logging.debug("Level 23 IF THEN ELSE statement entry point.")

        # Perform IF expression check.
        statement = self._get_value(self.op[1]._parse(self.mapping_md, self.constr_md))
        self.exception, self.mapping_md['ExceptionFlag'] = False, False
        # If 'IF' expression was true, ther perform THEN expression.
        if statement is True:
            logging.debug("Level 23 IF statement: True")
            self._get_value(self.op[2]._parse(self.mapping_md, self.constr_md))
        # If not, then perform ELSE expression if it exist. In the opposite case, do nothing.
        elif statement is False and len(self.op) > 3:
            logging.debug("Level 23 IF statement: Else")
            self._get_value(self.op[3]._parse(self.mapping_md, self.constr_md))
        else:
            logging.debug("Level 23 IF statement: False (no else)")
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

        logging.debug("Level 22 boolean IFF operation entry point")

        left, operation, right = self._boolify(self.op[0]._parse(self.mapping_md, self.constr_md)),
        self.op[1],
        self._boolify(self.op[2]._parse(self.mapping_md, self.constr_md))

        ret = left == right
        logging.debug(f"Level 20 {left} {operation} {right} result: {ret}")
        self._check_exception(ret, f'Expression ({left} {operation} {right})')
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
        logging.debug("Level 21 boolean IMPLIES operation entry point")

        left, operation, right = self._boolify(self.op[0]._parse(self.mapping_md, self.constr_md)),
        self.op[1],
        self._boolify(self.op[2]._parse(self.mapping_md, self.constr_md))

        ret = not left or right
        logging.debug(f"Level 21 {left} {operation} {right} result: {ret}")
        self._check_exception(ret, f'Expression ({left} {operation} {right})')
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
        logging.debug("Level 20 boolean OR operation entry point")

        left = self._boolify(self.op[0]._parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self._boolify(r._parse(self.mapping_md, self.constr_md))

            ret = left or right
            self._check_exception(ret, f'Expression ({left} {operation} {right})')
            left = ret
            logging.debug(f"Level 20 {left} {operation} {right} result: {ret}")
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
        logging.debug("Level 19 boolean XOR operation entry point")

        left = self._boolify(self.op[0]._parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self._boolify(r._parse(self.mapping_md, self.constr_md))
            ret = bool(left) ^ bool(right)
            self._check_exception(ret, f'Expression ({left} {operation} {right})')
            left = ret
            logging.debug(f"Level 19 {left} {operation} {right} result: {ret}")
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
        logging.debug("Level 18 boolean AND operation entry point")

        left = self._boolify(self.op[0]._parse(self.mapping_md, self.constr_md))
        for op, r in zip(self.op[1::2], self.op[2::2]):
            operation, right = op, self._boolify(r._parse(self.mapping_md, self.constr_md))
            ret = left and right
            self._check_exception(ret, f'Expression ({left} {operation} {right})')
            left = ret
            logging.debug(f"Level 18 {left} {operation} {right} result: {ret}")
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
        logging.debug("Level 14 boolean NOT operation entry point")

        operation, right = self.op[0], self._boolify(self.op[1]._parse(self.mapping_md, self.constr_md))
        ret = not right
        logging.debug(f"Level 14 {operation} {right} result: {ret}")

        self._check_exception(ret, f'Expression ({operation} {right})')
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
        # TODO update this function
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
                match_number = mapping_current.count(True)
                logging.debug(f'Check Operation {operation}. Values {mapping_current}')
                ret = self.comparison(operation, match_number)

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

    def comparison(self, operation, match_number):
        ret = False
        if operation == 'no' or operation == 'none':
            if match_number == 0:
                ret = True

        elif operation == 'lone':
            if match_number >= 1:
                ret = True

        elif operation == 'one':
            if match_number == 1:
                ret = True

        elif operation == 'some':
            if match_number > 1:
                ret = True
        # TODO Add ALL quantifier
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
        logging.debug("Level 12 boolean comparison operation entry point")
        for left_operand, op, right_operand in zip(self.res[0::2], self.res[1::2], self.res[2::2]):
            left, operation, right = self._get_value(left_operand), op, self._get_value(right_operand)
            logging.debug(f'Evaluating {left} {operation} {right}')
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
            logging.debug(f"Level 12 {left} {operation} {right} result: {ret}")
            self._check_exception(ret,
                                  f'Expression ({left} {operation} {list(right.keys()) if isinstance(right, dict) else right})')
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
        logging.debug("Level 11 requires/excludes operation entry point")
        left, operation, right = self._boolify(self.res[0]), self.res[1], self._boolify(self.res[2])
        if operation == 'requires':
            ret = not left or (left and right)
            logging.debug(f"Level 11 {left} {operation} {right} result: {ret}")
            self._check_exception(ret, 'Required feature does not exist')
        elif operation == 'excludes':
            ret = not (left and right)
            logging.debug(f"Level 11 {left} {operation} {right} result: {ret}")
            self._check_exception(ret, 'One of the features under excludes constraint should not exist')

        return ret
