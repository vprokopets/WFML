from language.lexer import lexer


class Lexer():

    def __init__(self):

        RESERVED = 'RESERVED'
        NUMBER = 'NUMBER'
        BOOLEAN = 'BOOLEAN'
        CLAFER = "CLAFER"
        CONSTRAINTS = 'CONSTRAINTS'
        COMPARISON = 'COMPARISON'
        ASSERTION = 'ASSERTION'
        REFERENCE = 'REFERENCE'
        OBJECTIVE = 'OBJECTIVE'
        EXPRESSION = 'EXPRESSION'
        ID = 'ID'
        NEWLINE = 'NEWLINE'
        TAB = 'TAB'
        TYPE = 'TYPE'

        self.token_expressions = [
            (r'\n+[ \t]*', NEWLINE),                # All newline, tab, space symbols till next meaning symbol
            (r'[ \t]+', TAB),                       # Tabulation, spaces
            (r'[\s \n]+', None),                    # Whitespaces characters
            (r'\/\*(\*(?!\/)|[^*])*\*\/', None),    # Group comments, begin with /*, placed on single/multi lines, ends with */
            (r'(#|//)[^\n]*', None),                # Comments, begin with # or //, placed on single line, ends with line break
            (r'assert \[.*\]', ASSERTION),          # Assertion expression placed between square brackets after keyword 'assert'
            (r'(integer|double|real|string)', TYPE),  # Type keywords
            (r'\[.*\]', CONSTRAINTS),               # Constraint expression placed between square brackets
            (r'(->|:)', REFERENCE),                 # Reference
            (r'<< (min|max) [^<<]*>>', OBJECTIVE),  # Objective
            (r'[0-9]+.[0-9]+|[0-9]+', NUMBER),      # Number
            (r'(<|>|<=|>=)', COMPARISON),           # Numeric comparison
            (r'(=|!=|in|not in)', COMPARISON),      # Overloaded comparison
            (r'(all|lone|one|some|no|not)', BOOLEAN),               # Boolean quantified expressions
            (r'(all disj|one disj|some disj|no disj)', BOOLEAN),    # Boolean quantified disjunction expressions
            (r'(if|then|else|<=>|=>|\|\||&&)', BOOLEAN),            # Boolean expressions
            (r'(or|xor|mux|opr)', BOOLEAN),                         # Boolean expressions
            (r'(\+{2}|\-{2}|\*{2}|,|\.{2})', EXPRESSION),                         # Set expressions
            (r'(int [0-9]+|double [0-9]+\.[0-9]+|real [0-9]+\.[0-9]+)', EXPRESSION),    # Numeric expression
            (r'(\+|\-|\*|/| % |sum|product|\?|\.)', EXPRESSION),                   # Numeric expression
            (r'".*"', EXPRESSION),                                                      # String expression
            (r'( :> | :< )', EXPRESSION),                                               # Relational expression
            (r'(this|parent|dref)', ID),            # Identifier
            (r'abstract', RESERVED),                # Keyword for abstract Clafer
            (r'enum', RESERVED),                    # Keyword for syntactic sugar
            (r'[A-Za-z.][A-Za-z0-9_.]*', CLAFER)            # Ewerything left is recognized as Clafers
        ]

    def split(self, text: str) -> list:
        return lexer.lex(text, self.token_expressions)
