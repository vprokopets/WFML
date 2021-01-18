import threading
from language.lexer.lexer_imp import Lexer
from language.parser.parser import Parser
from tools.file_manager import FileManager


class Main(threading.Thread):

    def __init__(self):
        super(Main, self).__init__()
        self.lexer = Lexer()
        self.parser = Parser()
        self.file_manager = FileManager()

    def run(self):
        filecopy = self.file_manager.open_file(filepath="constraints.clf")
        print(filecopy)
        tokens = self.lexer.split(text=filecopy)
        tokens = self.parser.preprocessing(tokens)
        for token in tokens:
            print(token)
        print('__________________________')
        return tokens


def run():
    main = Main()
    main.start()
    main.join()


if __name__ == "__main__":
    run()
