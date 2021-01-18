from lark import Lark, tree
from lark.indenter import Indenter


class TreeIndenter(Indenter):
    NL_type = '_NL'
    OPEN_PAREN_types = []
    CLOSE_PAREN_types = []
    INDENT_type = '_INDENT'
    DEDENT_type = '_DEDENT'
    tab_len = 8


filecopy = open('clafer.lark', "r")
grammar = filecopy.read()
filecopy = open('test.cf', "r")
sentence = filecopy.read()
parser = Lark(grammar, start='model', parser='earley', lexer='standard', postlex=TreeIndenter())


def make_png(filename):
    tree.pydot__tree_to_png(parser.parse(sentence), filename)

def make_dot(filename):
    tree.pydot__tree_to_dot(parser.parse(sentence), filename)


if __name__ == '__main__':
    print(parser.parse(sentence))
    make_png('example.png')
    make_dot('example1.dot')
