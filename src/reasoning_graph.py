import base64
import sys
import argparse
import pprint
from transcendental import SIN, COS, ExtendedFormulaManager
from transcendental import ExtendedHRPrinter, ExtendedHRSerializer
from transcendental import ExtendedEnvironment
from enum import Enum
from sexpdata import loads, dumps, car, cdr
from trivalogic import TriValLogic, Values
from portfolio_solver import SolverResult, PortfolioSolver, StrategyFactory
from model_checking_solver import NuSmvSolver, ModelCheckingSolver

pp = pprint.PrettyPrinter(indent=4)

class SExp:
    COMMENT = ";"
    def __init__(self, data):
        self.data = data

class STRING_CONSTANTS:
    NODE = "node"
    EDGE = "edge"
    SMTLIB = "smt25"
    ENTAILMENT = "entailment"
    AND = "and"
    DONE = "done"
    START = "start"
    SIMPLE = "simple"
    GRAPH = "graph"
    BASE = "base"
    KB = "kb"
    G = "g"
    VALID = "valid"
    COUNTER_MODEL = "cmodel"
    BOOLX = "boolX"
    EVALUATE = "evaluate"
    IN = "in"
    OUT = "out"
    ATTRIBUTE_TYPE = ":type"
    ATTRIBUTE_ENCODING = ":encoding"
    ATTRIBUTE_CONTENT = ":content"
    BASE64 = "base64"
    PLAIN = "plain"
    MODEL_CHECKING = "model_checking"
    NUSMV = "nusmv"
    MODEL = "model"
    PROPERTY = "property"
    HOLDS = "holds"
    COUNTER_EXAMPLE = "cexample" 


class EdgeType(Enum):
    SIMPLE = 1
    SMTLIB = 2
    BOOLX = 3
    EVALUATE = 4
    NUSMV = 6

    def from_string(str):
        if str == STRING_CONSTANTS.SIMPLE:
            return EdgeType.SIMPLE
        elif str == STRING_CONSTANTS.SMTLIB:
            return EdgeType.SMTLIB
        elif str == STRING_CONSTANTS.BOOLX:
            return EdgeType.BOOLX
        elif str == STRING_CONSTANTS.EVALUATE:
            return EdgeType.EVALUATE
        elif str == STRING_CONSTANTS.NUSMV:
            return EdgeType.NUSMV
        else:
            print("no such edge type:", str)
            assert(False)

    def to_string(e):
        if e == EdgeType.SIMPLE:
            return "simple"
        elif e == EdgeType.SMTLIB:
            return "smtlib"
        elif e == EdgeType.BOOLX:
            return "boolX"
        elif e == EdgeType.EVALUATE:
            return "evaluate"
        else:
            assert(False)

class Edge:
    def __init__(self, name, src, dest):
        self.name = name
        self.src = src
        self.dest = dest


    def get_type(self):
        raise NotImplementedError("get_type() must be overriden by sub-classes")

    #def __repr__(self):
    #    return str(self.__dict__)

    def __str__(self):
        return " ".join(["(edge ", EdgeType.to_string(self.get_type()), self.name, self.src.name,
                    self.dest.name, ")"])

    def str(self):
        return self.__str__()

class SimpleEdge(Edge):
    def __init__(self, name, src, dest):
        super().__init__(name, src, dest)

    def get_type(self):
        return EdgeType.SIMPLE

class NuSmvEdge(Edge):
    def __init__(self, name, src, dest, blob, encoding):
        super().__init__(name, src, dest)
        self.blob = blob
        self.encoding = encoding

    def get_type(self):
        return EdgeType.NUSMV

class SmtLibEdge(Edge):
    def __init__(self, name, src, dest, smtlib, encoding):
        super().__init__(name, src, dest)
        self.smtlib = smtlib
        self.encoding = encoding

    def decode_smtlib(self):
        return decode(self.smtlib, self.encoding)[1:-1]

    def get_type(self):
        return EdgeType.SMTLIB

class BoolXEdge(Edge):
    def __init__(self, name, src, dest, boolx):
        super().__init__(name, src, dest)
        self.boolx = boolx

    def get_type(self):
        return EdgeType.BOOLX

    def __str__(self):
        raise NotImplementedError("must be overriden")

class UnsolvedBoolXEdge(BoolXEdge):
    def __str__(self):
        return " ".join(["(edge ", EdgeType.to_string(self.get_type()), self.name, self.src.name,
                     self.dest.name, self.boolx,  ")"])

class SolvedBoolXEdge(BoolXEdge):
    def __str__(self):
        return " ".join(["(edge ", self.name, self.src.name,
                     self.dest.name, Values.to_string(self.boolx),  ")"])

class EvaluateEdge(Edge):
    def __init__(self, name, src, dest, wanted_values):
        super().__init__(name, src, dest)
        self.wanted_values = wanted_values

    def get_type(self):
        return EdgeType.EVALUATE

    def __str__(self):
        raise NotImplementedError("must be overriden")

class UnsolvedEvaluateEdge(EvaluateEdge):
    def __str__(self):
        return " ".join(["(edge ", EdgeType.to_string(self.get_type()), self.name, self.src.name,
                     self.dest.name,  ")"])

class SolvedEvaluateEdge(EvaluateEdge):
    def __init__(self, name, src, dest, wanted_values, solution):
        super().__init__(name, src, dest, wanted_values)
        self.solution = solution

    def get_values_in_output_format(self):
        result = "("
        for value in self.solution:
            result =  "".join([result, "(", str(value), ") "])
        result += ")"
        return result

    def __str__(self):
        return " ".join(["(edge ", self.name, self.src.name,
                     self.dest.name , ")"])

class NodeType(Enum):
    ENTAILMENT = 1
    AND = 2
    DONE = 3
    START = 4
    MODEL_CHECKING = 5

    def from_string(str):
        result = ""
        if str == STRING_CONSTANTS.ENTAILMENT:
            result = NodeType.ENTAILMENT
        elif str == STRING_CONSTANTS.AND:
            result = NodeType.AND
        elif str == STRING_CONSTANTS.DONE:
            result = NodeType.DONE
        elif str == STRING_CONSTANTS.START:
            result = NodeType.START
        elif str == STRING_CONSTANTS.MODEL_CHECKING:
            result = NodeType.MODEL_CHECKING
        else:
            assert(False)
        return result

    def to_string(node_type):
        if node_type == NodeType.ENTAILMENT:
            return STRING_CONSTANTS.ENTAILMENT
        elif node_type == NodeType.AND:
            return STRING_CONSTANTS.AND
        elif node_type == NodeType.DONE:
            return STRING_CONSTANTS.DONE
        elif node_type == NodeType.START:
            return STRING_CONSTANTS.START
        elif node_type == NodeType.MODEL_CHECKING:
            return STRING_CONSTANTS.MODEL_CHECKING
        else:
            assert(False)

class Node:
    def __init__(self, name, graph):
        self.name = name
        self.graph = graph

    def get_type(self):
        raise NotImplementedError("get_type() must be overriden by sub-classes")

    def connect_edge_to_port(self, edge, port_name):
        raise NotImplementedError("connect_edge_to_port() must be overriden by sub-classes")

    def get_incoming_edges(self):
        raise NotImplementedError("must be overriden by sub-classes")

    def get_outgoing_edges(self):
        raise NotImplementedError("must be overriden by sub-classes")

    def execute(self):
        raise NotImplementedError("must be overriden")

    def replace_edge(self, old, new):
        raise NotImplementedError("must be overriden")

    #def __repr__(self):
    #    return "( node " + self.name + " incoming: " + \
    #        " ".join(e.name for e in self.get_incoming_edges()) \
    #        + " outgoing: " + " ".join(e.name for e in self.get_outgoing_edges()) + " )"

    def __str__(self):
        return "(" + \
                " ".join([NodeType.to_string(self.get_type()), self.name]) + \
                ")"


    def str(self):
        return self.__str__()

class ModelCheckingNode(Node):
    def __init__(self, name, graph):
        super().__init__(name, graph)
        self._model = None
        self._property = None
        self._holds = None
        self._counter_example = None

    def get_incoming_edges(self):
        result = set([])
        result.add(self._model)
        result.add(self._property)
        return result

    def get_outgoing_edges(self):
        result = set([])
        if self._holds is not None:
            result.add(self._holds)
        if self._counter_example is not None:
            result.add(self._counter_example)
        return result
    
    def connect_edge_to_port(self, edge, port_name):
        if (port_name == STRING_CONSTANTS.MODEL):
            self._model = edge
        elif (port_name == STRING_CONSTANTS.PROPERTY):
            self._property = edge
        elif (port_name == STRING_CONSTANTS.HOLDS):
            self._holds = edge
        elif (port_name == STRING_CONSTANTS.COUNTER_EXAMPLE):
            self._counter_example = edge
        else:
            Assert(False)
    
    def get_nusmv_content(self):
        model = decode(self._model.blob, self._model.encoding)
        prop = decode(self._property.blob, self._property.encoding)
        return model + "\n" + prop

    def replace_edge(self, old, new):
        if old == self._model:
            self._model = new
        elif old == self._property:
            self._property = new
        elif old == self._holds:
            self._holds = new
        elif old == self._counter_example:
            self._counter_example = new
        else:
            assert(False)

    def get_type(self):
        return NodeType.MODEL_CHECKING

    def execute(self):
        print("Executing node: ", self.name)
        nusmv_content = self.get_nusmv_content()
        nusmv_solver = NuSmvSolver()
        nusmv_solver.set_content(nusmv_content)
        with open(self.name + '.nusmv', 'w') as the_file:
            the_file.write(nusmv_content)
        solver_result, solver_trace = nusmv_solver.solve()
        result = model_checking_solver_result_to_result(solver_result)
        old_boolx_edge = self._holds
        new_boolx_edge = SolvedBoolXEdge(old_boolx_edge.name,
                                        old_boolx_edge.src,
                                        old_boolx_edge.dest,
                                        result)
        self.graph.replace_edge(old_boolx_edge, new_boolx_edge)
        old_nusmv_edge = self._counter_example
        if old_nusmv_edge is not None:
            new_nusmv_edge = NuSmvEdge(old_nusmv_edge.name,
                                            old_nusmv_edge.src,
                                            old_nusmv_edge.dest,
                                            solver_trace,
                                            old_nusmv_edge.encoding)
        self.graph.replace_edge(old_nusmv_edge, new_nusmv_edge)

class EntailmentNode(Node):
    def __init__(self, name, graph):
        super().__init__(name, graph)
        self._base = None
        self._kb = None #edge
        self._g = None #edge
        self._valid = None #edge
        self._counter_model = None #edge


    def replace_edge(self, old, new):
        if old == self._kb:
            self._kb = new
        elif old == self._g:
            self._g == new
        elif old == self._valid:
            self._valid = new
        elif old == self._counter_model:
            self._counter_model = new
        else:
            assert(False)

    def get_type(self):
        return NodeType.ENTAILMENT

    def connect_edge_to_port(self, edge, port_name):
        if (port_name == STRING_CONSTANTS.BASE):
            self._base = edge
        elif (port_name == STRING_CONSTANTS.KB):
            self._kb = edge
        elif (port_name == STRING_CONSTANTS.G):
            self._g = edge
        elif (port_name == STRING_CONSTANTS.VALID):
            self._valid = edge
        elif (port_name == STRING_CONSTANTS.COUNTER_MODEL):
            self._counter_model = edge
        else:
            assert(False)

    def get_incoming_edges(self):
        result = set([])
        result.add(self._kb)
        result.add(self._g)
        result.add(self._base)
        return result

    def get_outgoing_edges(self):
        result = set([])
        if self._valid is not None:
            result.add(self._valid)
        if self._counter_model is not None:
            result.add(self._counter_model)
        return result

    def execute(self):
        print("Executing node: ", self.name)
        base_smtlib = self._base.decode_smtlib()
        kb_smtlib = "(assert " + self._kb.decode_smtlib() + ")"
        g_smtlib = "(assert (not " + self._g.decode_smtlib()  + "))"
        if self._counter_model is not None:
            get_val_smtlib = self._counter_model.wanted_values
        else:
            get_val_smtlib = ""
        smtlib = "(set-option :produce-models true) " + \
                base_smtlib + " " + " " + kb_smtlib +" " + g_smtlib + \
                " (check-sat) " + \
                get_val_smtlib
        solver = PortfolioSolver(smtlib, self.graph._config, self.name)
        with open(self.name + '.smt2', 'w') as the_file:
            the_file.write(smtlib)
        solver_result, values = solver.solve()
        result = smt_solver_result_to_result(solver_result)
        old_boolx_edge = self._valid
        new_boolx_edge = SolvedBoolXEdge(old_boolx_edge.name,
                                         old_boolx_edge.src,
                                         old_boolx_edge.dest,
                                         result)
        self.graph.replace_edge(old_boolx_edge, new_boolx_edge)

        old_evaluate_edge = self._counter_model
        if old_evaluate_edge:
            new_evaluate_edge = SolvedEvaluateEdge(old_evaluate_edge.name,
                                               old_evaluate_edge.src,
                                               old_evaluate_edge.dest,
                                               old_evaluate_edge.wanted_values,
                                               values)
            self.graph.replace_edge(old_evaluate_edge, new_evaluate_edge)


class DoneNode(Node):
    def __init__(self, name, graph):
        super().__init__(name, graph)
        self._input_edges = set([])

    def replace_edge(self, old, new):
        self._input_edges.remove(old)
        self._input_edges.add(new)

    def get_type(self):
        return NodeType.DONE

    def connect_edge_to_port(self, edge, port_name):
        self._input_edges.add(edge)

    def get_incoming_edges(self):
        return self._input_edges

    def get_outgoing_edges(self):
        return set([])

    def execute(self):
        pass

class StartNode(Node):
    def __init__(self, name, graph):
        super().__init__(name, graph)
        self._output_edges = set([])

    def replace_edge(self, old, new):
        self._input_edges.remove(old)
        self._input_edges.add(new)

    def get_type(self):
        return NodeType.START

    def connect_edge_to_port(self, edge, port_name):
        self._output_edges.add(edge)

    def get_incoming_edges(self):
        return set([])

    def get_outgoing_edges(self):
        return self._output_edges

    def execute(self):
        pass

class AndNode(Node):
    def __init__(self, name, graph):
        super().__init__(name, graph)
        self._conjuncts = set([]) #set of edges
        self._output = None #edge

    def replace_edge(self, old, new):
        if old in self._conjuncts:
            self._conjuncts.remove(old)
            self._conjuncts.add(new)
        elif old == self._output:
            self._output = new
        else:
            assert(False)

    def get_type(self):
        return NodeType.AND

    def connect_edge_to_port(self, edge, port_name):
        if port_name == STRING_CONSTANTS.IN:
            self._conjuncts.add(edge)
        elif port_name == STRING_CONSTANTS.OUT:
            self._output = edge
        else:
            assert(false)

    def get_incoming_edges(self):
        return self._conjuncts

    def get_outgoing_edges(self):
        return [self._output]

    def execute(self):
        print("Executing node: ", self.name)
        conjuncts_values = [c.boolx for c in self._conjuncts]
        result = TriValLogic.kleene_and(conjuncts_values)
        old_boolx_edge = self._output
        new_boolx_edge = SolvedBoolXEdge(old_boolx_edge.name,
                                         old_boolx_edge.src,
                                         old_boolx_edge.dest,
                                         result)
        self.graph.replace_edge(old_boolx_edge, new_boolx_edge)




class ReasoningGraph:

    def __init__(self, sexp_str, config):
        self._sexp = loads(sexp_str)
        self._nodes_dict_by_name = {}
        self._start_nodes = set([])
        self._done_nodes = set([])
        self._edges = set([])
        self._generate_reasoning_graph_from_sexp()
        self._config = config

    def __str__(self):
        nodes = self._nodes_dict_by_name.values()
        edges = self._edges
        result = "nodes: " + "\n".join(node.str() for node in nodes) + "\nedges:\n" + \
        "\n".join(e.str() for e in edges)
        return result

    def replace_edge(self, old, new):
        self._edges.remove(old)
        self._edges.add(new)
        src = old.src
        dest = old.dest
        src.replace_edge(old, new)
        dest.replace_edge(old, new)

    def execute(self):
        raise NotImplementedError("currently we only executre reasoning dags")

    def _generate_reasoning_graph_from_sexp(self):
        edges = set([])
        assert(dumps(car(self._sexp)) == STRING_CONSTANTS.GRAPH)
        graph_name_and_def = cdr(self._sexp)
        graph_def = cdr(graph_name_and_def)
        node_defs = car(graph_def)
        edge_defs = car(cdr(graph_def))
        for e in node_defs:
            assert(is_node_sexp(e))
            node_sexp_body = cdr(e)
            node = self._generate_node_from_sexp(node_sexp_body)
            self._nodes_dict_by_name[node.name] = node
        for e in edge_defs:
            assert(is_edge_sexp(e))
            edge_sexp_body = cdr(e)
            self._generate_and_add_edge_from_sexp(edge_sexp_body)

    def _generate_and_add_edge_from_sexp(self, e):
        edge_type, edge_name, src_node, src_port, dest_node, dest_port, label, encoding = \
            self._get_type_name_src_dest_label_encoding_of_edge_from_sexp(e)
        if edge_type is EdgeType.SIMPLE:
            edge = SimpleEdge(edge_name, src_node, dest_node)
        elif edge_type is EdgeType.SMTLIB:
            label = label.replace("\\", "")
            edge = SmtLibEdge(edge_name, src_node, dest_node, label, encoding)
        elif edge_type is EdgeType.BOOLX:
            edge = UnsolvedBoolXEdge(edge_name, src_node, dest_node, label)
        elif edge_type is EdgeType.EVALUATE:
            label = label[1:-1] #remove wrapping ( and )
            label = label.replace("\\", "")
            edge = UnsolvedEvaluateEdge(edge_name, src_node, dest_node, label)
        elif edge_type is EdgeType.NUSMV:
            edge = NuSmvEdge(edge_name, src_node, dest_node, label, encoding)
        else:
            assert(False)
        src_node.connect_edge_to_port(edge, src_port)
        dest_node.connect_edge_to_port(edge, dest_port)
        self._edges.add(edge)

    def node_and_port(self, e):
        if dumps(e) == "__":
            return ["__", ""]
        else:
            node = dumps(car(e))
            port = dumps(car(cdr(e)))
            return [node, port]

    def _get_type_name_src_dest_label_encoding_of_edge_from_sexp(self, e):
        first = car(e)
        second = car(cdr(e))
        third = car(cdr(cdr(e)))
        rest = cdr(cdr(cdr(e)))
        edge_name = dumps(first)
        src_node_name, src_port_name = self.node_and_port(second)
        dest_node_name, dest_port_name = self.node_and_port(third)
        attributes = get_attributes(rest)
        edge_type = EdgeType.from_string(attributes[STRING_CONSTANTS.ATTRIBUTE_TYPE])
        label = attributes[STRING_CONSTANTS.ATTRIBUTE_CONTENT]
        encoding = attributes[STRING_CONSTANTS.ATTRIBUTE_ENCODING]
        if src_node_name == "__":
            start_node_name = "start" + str(len(self._start_nodes))
            src = StartNode(start_node_name, self)
            self._nodes_dict_by_name[start_node_name] = src
            dest = self._nodes_dict_by_name[dest_node_name]
            self._start_nodes.add(src)
        elif dest_node_name == "__":
            done_node_name = "done" + str(len(self._done_nodes))
            src = self._nodes_dict_by_name[src_node_name]
            dest = DoneNode(done_node_name, self)
            self._nodes_dict_by_name[done_node_name] = dest
            self._done_nodes.add(dest)
        else:
            src = self._nodes_dict_by_name[src_node_name]
            dest = self._nodes_dict_by_name[dest_node_name]
        return edge_type, edge_name, src, src_port_name, dest, dest_port_name, label, encoding



class ReasoningDag(ReasoningGraph):
    def __init__(self, sexp_str, config):
        super().__init__(sexp_str, config)

    def execute(self):
        topo = self._topo_sort()
        for node in topo:
            node.execute()


    def _topo_sort(self):
        result = []
        nodes_to_process = set([])
        nodes_to_process.update(self._start_nodes)
        processed_edges = set([])
        while nodes_to_process: #while it is not empty
            n = nodes_to_process.pop()
            result.append(n)
            for e in n.get_outgoing_edges():
                if e not in processed_edges:
                    m = e.dest
                    processed_edges.add(e)
                    if m.get_incoming_edges().issubset(processed_edges):
                        nodes_to_process.add(m)
        return result

    def _generate_node_from_sexp(self, e):
        node_name = dumps(car(e))
        node_type_str = dumps(car(cdr(e)))
        node_type = NodeType.from_string(node_type_str)
        if node_type is NodeType.ENTAILMENT:
            result = EntailmentNode(node_name, self)
        elif node_type is NodeType.AND:
            result = AndNode(node_name, self)
        elif node_type is NodeType.DONE:
            result = DoneNode(node_name, self)
        elif node_type is NodeType.MODEL_CHECKING:
            result = ModelCheckingNode(node_name, self)            
        else:
            assert(False)
        return result


#if there is at least one seperator inside original_str,
#act like original_str.split().
#Otherwise, return original_str
def split_or_same(original_str, separator):
    res_list = original_str.split(separator)
    if len(res_list) == 1:
        return res_list[0], None
    else:
        return res_list

def get_smtlib_str_from_sexp(e):
    return dumps(e)

def is_node_sexp(e):
    car_str = dumps(car(e))
    return car_str == STRING_CONSTANTS.NODE

def is_edge_sexp(e):
    car_str = dumps(car(e))
    return car_str == STRING_CONSTANTS.EDGE


def process_graph(graph, config):
    rg = ReasoningDag(graph, config)
    rg.execute()
    output_lines = []
    for edge in rg._edges:
        if edge.get_type() == EdgeType.BOOLX:
            if edge.boolx == Values.UNKNOWN and edge.src.get_type() == NodeType.ENTAILMENT:
                expr = edge.src._counter_model.get_values_in_output_format()
            else:
                expr = ""
            line = " ".join(["(", edge.name,
                                 Values.to_string(edge.boolx),
                                 expr,
                                 ")"
                                 ])
            #output_lines.append(" ".join(["(", edge.name,
             #                            Values.to_string(edge.boolx),
             #                            ")"]))
            output_lines.append(line)

    for edge in rg._edges:
        if edge.get_type() == EdgeType.EVALUATE:
            src = edge.src
            validity_edge = src._valid
            validity_value = validity_edge.boolx
            if validity_value == Values.FALSE:
                output_lines.append(" ".join(["(", edge.name,
                                        edge.get_values_in_output_format(),
                                        ")"]))

    for edge in rg._edges:
        if edge.get_type() == EdgeType.NUSMV:
            src = edge.src
            if src.get_type() == NodeType.MODEL_CHECKING:
                holds_edge = src._holds
                holds_value = holds_edge.boolx
                if holds_value == Values.FALSE:
                    output_lines.append(" ".join(["(", edge.name, 
                        edge.blob, ")"]))

    return output_lines



def process_graph_with_files(in_path, out_path, config):
    lines = []
    with open(in_path) as inputfile:
        for line in inputfile:
            if not line.startswith(SExp.COMMENT):
                lines.append(line)
    sexp_str = "".join(lines)
    output_lines = process_graph(sexp_str, config)
    with open(out_path, 'w') as outputfile:
        for line in output_lines:
            outputfile.write("%s\n" % line)


def process_graph_with_strings(graph, config):
    return "\n".join(process_graph(graph, config))

class Config:
    def __init__(self):
        self.disabled_solvers = []
        self.dreal_precision = None

def main(args):
    argparser = argparse.ArgumentParser(description='Hermes')
    argparser.add_argument('input_file',
                           metavar='reasoning_graph',
                           type=str,
                           help='path to the input file describing the reasoning \
                           graph')
    argparser.add_argument('output_file',
                           metavar='result',
                           type=str,
                           help='path to output file')
    argparser.add_argument('--disable_solver',
                           action='append',
                           help='disable a solver')
    argparser.add_argument('--dreal_precision',
                            help='dreal precision')
    argparser.add_argument('--strategy',
                            help='strategy to pick solvers')
    args = argparser.parse_args(args)
    if len(sys.argv) < 2:
        argparser.print_help()
        exit(1)
    if args.disable_solver == None:
        solvers_to_disable = []
    else:
        solvers_to_disable = args.disable_solver
    if args.strategy != None and args.strategy not in StrategyFactory.STRATEGY_NAMES:
        print("strategy must be either empty or one of: " + StrategyFactory.STRATEGY_NAMES)
        exit(1)

    config = Config()
    config.disabled_solvers = solvers_to_disable
    config.dreal_precision = args.dreal_precision
    config.strategy = args.strategy
    process_graph_with_files(args.input_file,
                  args.output_file, config)


def decode(s, encoding):
    assert(encoding == STRING_CONSTANTS.BASE64 or encoding == STRING_CONSTANTS.PLAIN)
    if (encoding == STRING_CONSTANTS.BASE64):
        s = s + "="
        result = base64.b64decode(s).decode('utf-8')
    elif (encoding == STRING_CONSTANTS.PLAIN):
        result = s
    else:
        #for now, we only support base64 encoding
        Assert(False)
    return result


def smt_solver_result_to_result(solver_result):
        if solver_result == SolverResult.SAT:
            result = Values.FALSE
        elif solver_result == SolverResult.UNSAT:
            result = Values.TRUE
        elif solver_result == SolverResult.UNKNOWN:
            result = Values.UNKNOWN
        else:
            assert(False)
        return result


def model_checking_solver_result_to_result(solver_result):
        if solver_result == ModelCheckingSolver.HOLDS:
            result = Values.TRUE
        elif solver_result == ModelCheckingSolver.DOES_NOT_HOLD:
            result = Values.FALSE
        elif solver_result == ModelCheckingSolver.UNKNOWN:
            result = Values.UNKNOWN
        else:
            assert(False)
        return result

def get_attributes(e):
    result = {}
    i = e
    while (i):
        key = dumps(car(i))
        assert(key.startswith(":"))
        value = dumps(car(cdr(i)))
        result[key] = value
        i = cdr(cdr(i))
    return result



if __name__ == "__main__":
    main(sys.argv[1:])
