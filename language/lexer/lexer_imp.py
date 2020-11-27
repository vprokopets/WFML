from language.lexer import lexer


class Lexer():

    def __init__(self):

        RESERVED = 'RESERVED'
        CARDINALITY = 'CARDINALITY'
        ID = 'ID'
        NEWLINE = 'NEWLINE'
        TAB = 'TAB'

        self.token_expressions = [
            (r'\n+[ \t]*', NEWLINE),   # All newline, tab, space symbols till next meaning symbol
            (r'[ \t]+', TAB),          # Tabulation, spaces
            (r'[\s \n]+', None),       # Whitespaces characters
            (r'/\*[^/\*]*\*/', None),  # Group comments
            (r'#[^\n]*', None),        # Comments
            (r'//[^\n]*', None),       # Comments
            (r'[0-9.. \*]+', CARDINALITY),
            (r'or', CARDINALITY),
            (r'xor', CARDINALITY),
            (r'mux', CARDINALITY),
            (r'\:=', RESERVED),
            (r'\(', RESERVED),
            (r'\)', RESERVED),
            (r';', RESERVED),
            (r'\+', RESERVED),
            (r'-', RESERVED),
            (r'\*', RESERVED),
            (r'/', RESERVED),
            (r'<=', RESERVED),
            (r'<', RESERVED),
            (r'>=', RESERVED),
            (r'>', RESERVED),
            (r'=', RESERVED),
            (r'!=', RESERVED),
            (r':', RESERVED),
            (r'parent', RESERVED),
            (r'and', RESERVED),
            (r'not', RESERVED),
            (r'if', RESERVED),
            (r'then', RESERVED),
            (r'else', RESERVED),
            (r'while', RESERVED),
            (r'do', RESERVED),
            (r'end', RESERVED),
            (r'\?', RESERVED),
            (r'[A-Za-z.][A-Za-z0-9_.]*', ID)
        ]

    def split(self, text: str) -> list:
        return lexer.lex(text, self.token_expressions)
