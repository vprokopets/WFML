import threading
from language.lexer.lexer_imp import Lexer
from language.parser.parser import find_parent_relations, modulize_by_depth
from tools.file_manager import FileManager


class Main(threading.Thread):

    def __init__(self):
        super(Main, self).__init__()
        self.lexer = Lexer()
        self.file_manager = FileManager()

    def run(self):
        filecopy = self.file_manager.open_file(filepath="phone.clf")
        print(filecopy)
        tokens = self.lexer.split(text=filecopy)

        modules = find_parent_relations(tokens)
        moduliz = modulize_by_depth(tokens, 1)
        return tokens


def run():
    main = Main()
    main.start()
    main.join()


if __name__ == "__main__":
    run()
