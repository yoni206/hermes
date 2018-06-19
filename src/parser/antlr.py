import sys
from antlr4 import *
from generated.SMTLIBv2Lexer import SMTLIBv2Lexer
from MySMTLIBv2Parser import *
from generated.SMTLIBv2Listener import SMTLIBv2Listener
from HermesListener import HermesListener
from generated.SMTLIBv2Visitor import SMTLIBv2Visitor
from HermesVisitor import HermesVisitor




def main(argv):
    #print(argv[1])
    input = FileStream(argv[1])
    #print(input)
    lexer = SMTLIBv2Lexer(input)
    #print(lexer.literalNames)
    stream = CommonTokenStream(lexer)
    #print(stream)
    parser = MySMTLIBv2Parser(stream)
    tree = parser.start()
    output = open("output.txt","w")

    str = ''
    hermesListener = HermesListener(str)
    walker = ParseTreeWalker()
    #print(tree)
    walker.walk(hermesListener, tree)

    output.close()
    print(hermesListener.str)
if __name__ == '__main__':
    main(sys.argv)
