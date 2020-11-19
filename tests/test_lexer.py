from language.lexer.lexer_imp import Lexer
from tools.file_manager import FileManager

RESULT = [('telematics', 'ID'), ('System', 'ID'), ('\n', 'NEWLINE'), ('xor', 'RESERVED'), ('channel', 'ID'),
          ('\n', 'NEWLINE'), ('single', 'ID'), ('\n', 'NEWLINE'), ('dual', 'ID'), ('\n\n', 'NEWLINE'),
          ('extraDisplay', 'ID'), ('?', 'RESERVED'), ('\n\n', 'NEWLINE'), ('xor', 'RESERVED'), ('size', 'ID'),
          ('\n', 'NEWLINE'), ('small', 'ID'), ('\n', 'NEWLINE'), ('large', 'ID'), ('\n', 'NEWLINE')]

def test_lexer():
    lexer = Lexer()
    file_manager = FileManager()
    filecopy = file_manager.open_file(filepath="sample.clf")
    tokens = lexer.split(text=filecopy)
    assert tokens == RESULT
