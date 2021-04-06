class FileManager():

    def __init__(self):
        self.flag = True
        pass

    def open_file(self, filepath: str) -> str:
        self.flag
        filecopy = open(filepath, "r")
        return filecopy.read()
