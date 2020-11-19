from language.lexer import lexer


class Lexer():

    def __init__(self):

        RESERVED = 'RESERVED'
        INT = 'INT'
        ID = 'ID'
        NEWLINE = 'NEWLINE'
        TAB = 'TAB'

        self.token_expressions = [
            (r'\n+[ \t]+', NEWLINE),
            (r'[ \t]+', TAB),
            (r'[\s \n]+', None),
            (r'#[^\n]*', None),
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
            (r'or', RESERVED),
            (r'not', RESERVED),
            (r'xor', RESERVED),
            (r'if', RESERVED),
            (r'then', RESERVED),
            (r'else', RESERVED),
            (r'while', RESERVED),
            (r'do', RESERVED),
            (r'end', RESERVED),
            (r'\?', RESERVED),
            (r'[0-9]+', INT),
            (r'[A-Za-z.][A-Za-z0-9_.]*', ID)
        ]

    def split(self, text: str) -> list:
        return lexer.lex(text, self.token_expressions)
