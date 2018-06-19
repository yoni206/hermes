import sys
from antlr4 import *
from parser.MySMTLIBv2Parser import *
from parser.generated.SMTLIBv2Listener import SMTLIBv2Listener

class HermesListener(SMTLIBv2Listener) :

    # a mapping from SMTLIB command names to corresponding methods in Context
    # Objects.
    # TODO fill in everything
    commandsMap = {
        'assert': 'cmd_assert',
        'check-sat': 'cmd_checkSat',
        'check-sat-assuming': 'cmd_checkSatAssuming',
        'declare-const': 'cmd_declareConst',
        'declare-datatypes': 'cmd_declareDatatypes',
        'declare-datatype': 'cmd_declareDatatype',
        'declare-fun': 'cmd_declareFun',
        'declare-sort': 'cmd_declareSort',
        'define-fun': 'cmd_defineFun',
        'define-fun-rec': 'cmd_defineFunRec'
    }

    def __init__(self, str):
        self.str = str

    def exitCommand(self, ctx:MySMTLIBv2Parser.CommandContext):
        self.str += ctx.getText() + '\n'
        #print(ctx.getText())
        #if self.isContextOfCommand(ctx, 'declare-fun'):
        #    print('**********************')
        #    range = ctx.sort()[-1]
        #    for child in ctx.symbol():
        #        print(child.simpleSymbol().getText())
        #    if range.identifier().getText() == 'Set':
        #        print('Set of ', range.sort()[-1].getText())
        #    #print(ctx.start.text)
        #    print(ctx.getTokens(10))
        #print('***************************')
        #a = ctx.start.line
        #b = ctx.stop.line
        #print('a = ', a)
        #print('b = ', b)
        #if ctx.attribute() is not None:
        #    for child in ctx.attribute():
        #        print(child.keyword().simpleSymbol().getText())
        #        if child.attribute_value() is not None:
        #            print('   ', child.attribute_value().getText())


    def isContextOfCommand(self, ctx:MySMTLIBv2Parser.CommandContext, cmdStr):
        return getattr(ctx,self.commandsMap[cmdStr])() is not None;
