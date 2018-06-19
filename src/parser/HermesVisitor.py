import sys
from antlr4 import *
from parser.generated.SMTLIBv2Parser import SMTLIBv2Parser
from parser.generated.SMTLIBv2Visitor import SMTLIBv2Visitor

class HermesVisitor(SMTLIBv2Visitor) :
    def __init__(self, output):
        self.output = output
        self.output.write('hey')

    def exitCommand(self, ctx:SMTLIBv2Parser.CommandContext):
        #try:
        print(ctx.ParOpen())
        #except AttributeError:
        #print('error')
        #self.output.write(ctx.symbol)
