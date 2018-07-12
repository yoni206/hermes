import sys
import argparse
import pprint
from transcendental import SIN, COS, ExtendedFormulaManager
from transcendental import ExtendedHRPrinter, ExtendedHRSerializer
from transcendental import ExtendedEnvironment
from enum import Enum
from sexpdata import loads, dumps, car, cdr
from trivalogic import TriValLogic, Values
from portfolio_solver import SolverResult, PortfolioSolver

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



class EdgeType(Enum):
    SIMPLE = 1
    SMTLIB = 2
    BOOLX = 3
    EVALUATE = 4

    def from_string(str):
        if str == STRING_CONSTANTS.SIMPLE:
            return EdgeType.SIMPLE
        elif str == STRING_CONSTANTS.SMTLIB:
            return EdgeType.SMTLIB
        elif str == STRING_CONSTANTS.BOOLX:
            return EdgeType.BOOLX
        elif str == STRING_CONSTANTS.EVALUATE:
            return EdgeType.EVALUATE
        else:
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

class SmtLibEdge(Edge):
    def __init__(self, name, src, dest, smtlib):
        super().__init__(name, src, dest)
        self.smtlib = smtlib

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
        return " ".join(["(edge ", self.name, self.src.name,
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
        else:
            assert(False)

class Node:
    def __init__(self, name, graph):
        self.name = name
        self.graph = graph

    def get_type(self):
        raise NotImplementedError("get_type() must be overriden by sub-classes")

    def generate_from_sexp(e):
        raise NotImplementedError("generate_from_sexp() must be overriden by sub-classes")

    def connect_edge_to_port(self, edge, port_name):
        raise NotImplementedError("connect_edge_to_port() must be overriden by sub-classes")

    def get_incoming_edges(self):
        raise NotImplementedError("must be overriden by sub-classes")

    def get_outgoing_edges(self):
        raise NotImplementedError("must be overriden by sub-classes")

    def execute(self):
        raise NotImplementedError("must be overriden")

    def replace_edge(self, old, new):
        raise NotImplementedError("most be overriden")

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

    def generate_from_sexp(e, graph):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return EntailmentNode(node_name, graph)

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
        print('executing node ', self.name)
        base_smtlib = self._base.smtlib
        kb_smtlib = "(assert " + self._kb.smtlib + ")"
        g_smtlib = "(assert (not " + self._g.smtlib  + "))"
        if self._counter_model is not None:
            get_val_smtlib = self._counter_model.wanted_values
        else:
            get_val_smtlib = ""
        smtlib = "(set-option :produce-models true) " + \
                base_smtlib + " " + " " + kb_smtlib +" " + g_smtlib + \
                " (check-sat) " + \
                get_val_smtlib
        solver = PortfolioSolver(smtlib, self.graph._disabled_solvers)
        solver_result, values = solver.solve()
        if solver_result == SolverResult.SAT:
            result = Values.FALSE
        elif solver_result == SolverResult.UNSAT:
            result = Values.TRUE
        elif solver_result == SolverResult.UNKNOWN:
            result = Values.UNKNOWN
        else:
            print(solver_result)
            assert(False)
        old_boolx_edge = self._valid
        new_boolx_edge = SolvedBoolXEdge(old_boolx_edge.name,
                                         old_boolx_edge.src,
                                         old_boolx_edge.dest,
                                         result)
        self.graph.replace_edge(old_boolx_edge, new_boolx_edge)

        old_evaluate_edge = self._counter_model
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

    def generate_from_sexp(e, graph):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return DoneNode(node_name, graph)

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

    def generate_from_sexp(e, graph):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return StartNode(node_name, graph)

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

    def generate_from_sexp(e, graph):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return AndNode(node_name, graph)

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
        conjuncts_values = [c.boolx for c in self._conjuncts]
        result = TriValLogic.kleene_and(conjuncts_values)
        old_boolx_edge = self._output
        new_boolx_edge = SolvedBoolXEdge(old_boolx_edge.name,
                                         old_boolx_edge.src,
                                         old_boolx_edge.dest,
                                         result)
        self.graph.replace_edge(old_boolx_edge, new_boolx_edge)




class ReasoningGraph:

    def __init__(self, sexp_str, disabled_solvers = []):
        self._sexp = loads(sexp_str)
        self._nodes_dict_by_name = {}
        self._start_nodes = set([])
        self._done_nodes = set([])
        self._edges = set([])
        self._generate_reasoning_graph_from_sexp()
        self._disabled_solvers = disabled_solvers

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
        for e in graph_def:
            if is_node_sexp(e):
                node_sexp_body = cdr(e)
                node = self._generate_node_from_sexp(node_sexp_body)
                self._nodes_dict_by_name[node.name] = node
            elif is_edge_sexp(e):
                edge_sexp_body = cdr(e)
                self._generate_and_add_edge_from_sexp(edge_sexp_body)
            else:
                assert(false)

    def _generate_and_add_edge_from_sexp(self, e):
        edge_type, edge_name, src_node, src_port, dest_node, dest_port, label = \
            self._get_type_name_src_dest_label_of_edge_from_sexp(e)
        if edge_type is EdgeType.SIMPLE:
            edge = SimpleEdge(edge_name, src_node, dest_node)
        elif edge_type is EdgeType.SMTLIB:
            label = label[1:-1] #remove wrapping ( and )
            label = label.replace("\\", "")
            edge = SmtLibEdge(edge_name, src_node, dest_node, label)
        elif edge_type is EdgeType.BOOLX:
            edge = UnsolvedBoolXEdge(edge_name, src_node, dest_node, label)
        elif edge_type is EdgeType.EVALUATE:
            label = label[1:-1] #remove wrapping ( and )
            label = label.replace("\\", "")
            edge = UnsolvedEvaluateEdge(edge_name, src_node, dest_node, label)
        else:
            assert(False)
        src_node.connect_edge_to_port(edge, src_port)
        dest_node.connect_edge_to_port(edge, dest_port)
        self._edges.add(edge)

    def _get_type_name_src_dest_label_of_edge_from_sexp(self, e):
        first = car(e)
        second = car(cdr(e))
        third = car(cdr(cdr(e)))
        fourth = car(cdr(cdr(cdr(e))))
        edge_name = dumps(first)
        src_node_name, src_port_name = split_or_same(dumps(second),"\\.")
        dest_node_name, dest_port_name = split_or_same(dumps(third),"\\.")
        label_type = dumps(car(fourth))
        edge_type = EdgeType.from_string(label_type)
        label = dumps(car(cdr(fourth)))
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

        return edge_type, edge_name, src, src_port_name, dest, dest_port_name, label


class ReasoningDag(ReasoningGraph):
    def __init__(self, sexp_str, disabled_solvers = []):
        super().__init__(sexp_str, disabled_solvers)

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
        node_type_str = dumps(car(e))
        sexp_after_type = cdr(e)
        node_type = NodeType.from_string(node_type_str)
        if node_type is NodeType.ENTAILMENT:
            result = EntailmentNode.generate_from_sexp(sexp_after_type, self)
        elif node_type is NodeType.AND:
            result = AndNode.generate_from_sexp(sexp_after_type, self)
        elif node_type is NodeType.DONE:
            result = DoneNode.generate_from_sexp(sexp_after_type, self)
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


def process_graph(in_path, out_path, disable_solvers):
    lines = []
    with open(in_path) as inputfile:
        for line in inputfile:
            if not line.startswith(SExp.COMMENT):
                lines.append(line)
    sexp_str = "".join(lines)
    rg = ReasoningDag(sexp_str, disable_solvers)
    print(rg)
    rg.execute()
    print(rg)
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

    with open(out_path, 'w') as outputfile:
        for line in output_lines:
            outputfile.write("%s\n" % line)


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
    args = argparser.parse_args(args)
    if len(sys.argv) < 2:
        argparser.print_help()
        exit(1)
    if args.disable_solver == None:
        solvers_to_disable = []
    else:
        solvers_to_disable = args.disable_solver
    #comment: args.disable_solver is a list of solvers to disable.
    process_graph(args.input_file, args.output_file, solvers_to_disable)

if __name__ == "__main__":
    main(sys.argv[1:])
