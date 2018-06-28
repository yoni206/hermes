import sys
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
        return " ".join(["(edge ", self.name, self.src.name,
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
        return " ".join(["(edge ", self.name, self.src.name,
                     self.dest.name, self.boolx,  ")"])

class EvaluateEdge(Edge):
    def __init__(self, name, src, dest, get_value_cmds):
        super().__init__(name, src, dest)
        self.get_value_cmds = get_value_cmds

    def get_type(self):
        return EdgeType.EVALUATE

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



class Node:
    def __init__(self, name):
        self.name = name

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

    def __repr__(self):
        return "( node " + self.name + " incoming: " + \
            " ".join(e.name for e in self.get_incoming_edges()) \
            + " outgoing: " + " ".join(e.name for e in self.get_outgoing_edges()) + " )"


class EntailmentNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._kb = None #edge
        self._g = None #edge
        self._valid = None #edge
        self._counter_model = None #edge

    def get_type(self):
        return NodeType.ENTAILMENT

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return EntailmentNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        if (port_name == STRING_CONSTANTS.KB):
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
        return result

    def get_outgoing_edges(self):
        result = set([])
        result.add(self._valid)
        result.add(self._counter_model)
        return result

    def execute(self):
        kb_smtlib = self._kb.smtlib
        g_smtlib = "(assert (not " + self._g.smtlib  + "))"
        smtlib = kb_smtlib + g_smtlib + " (check-sat)"
        solver = PortfolioSolver(smtlib)
        solver_result = solver.solve()
        if solver_result == SolverResult.SAT:
            result = Values.FALSE
        elif solver_result == SolverResult.UNSAT:
            result = Values.TRUE
        elif solver_result == SolverResult.UNKNOWN:
            result = Values.UNKNOWN
        else:
            assert(False)
        self._valid.boolx = result





class DoneNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._input_edges = set([])

    def get_type(self):
        return NodeType.DONE

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return DoneNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        self._input_edge = edge

    def get_incoming_edges(self):
        return self._input_edges

    def get_outgoing_edges(self):
        return set([])

    def execute(self):
        pass

class StartNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._output_edges = set([])

    def get_type(self):
        return NodeType.START

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return StartNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        self._output_edges.add(edge)

    def get_incoming_edges(self):
        return set([])

    def get_outgoing_edges(self):
        return self._output_edges

    def execute(self):
        pass

class AndNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._conjuncts = set([]) #set of edges
        self._output = None #edge

    def get_type(self):
        return NodeType.AND

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return AndNode(node_name)

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
        _output = TriValLogic.kleene_and(conjuncts_values)


class ReasoningGraph:

    def __init__(self, sexp_str):
        self._sexp = loads(sexp_str)
        self._nodes_dict_by_name = {}
        self._start_nodes = set([])
        self._done_nodes = set([])
        self._edges = set([])
        self._generate_reasoning_graph_from_sexp()

    def __str__(self):
        nodes = self._nodes_dict_by_name.keys()
        edges = self._edges
        result = "nodes:\n" + " ".join(nodes) + "\nedges:" + \
        " ".join(e.str() for e in edges)
        return result


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
                node = generate_node_from_sexp(node_sexp_body)
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
            edge = BoolXEdge(edge_name, src_node, dest_node, label)
        elif edge_type is EdgeType.EVALUATE:
            edge = EvaluateEdge(edge_name, src_node, dest_node, label)
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
            src = StartNode(start_node_name)
            self._nodes_dict_by_name[start_node_name] = src
            dest = self._nodes_dict_by_name[dest_node_name]
            self._start_nodes.add(src)
        elif dest_node_name == "__":
            done_node_name = "done" + str(len(self._done_nodes))
            src = self._nodes_dict_by_name[src_node_name]
            dest = DoneNode(done_node_name)
            self._nodes_dict_by_name[done_node_name] = dest
            self._done_nodes.add(dest)
        else:
            src = self._nodes_dict_by_name[src_node_name]
            dest = self._nodes_dict_by_name[dest_node_name]

        return edge_type, edge_name, src, src_port_name, dest, dest_port_name, label


class ReasoningDag(ReasoningGraph):
    def __init__(self, sexp_str):
        super().__init__(sexp_str)

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

def generate_node_from_sexp(e):
    node_type_str = dumps(car(e))
    sexp_after_type = cdr(e)
    node_type = NodeType.from_string(node_type_str)
    if node_type is NodeType.ENTAILMENT:
        result = EntailmentNode.generate_from_sexp(sexp_after_type)
    elif node_type is NodeType.AND:
        result = AndNode.generate_from_sexp(sexp_after_type)
    elif node_type is NodeType.DONE:
        result = DoneNode.generate_from_sexp(sexp_after_type)
    else:
        assert(False)
    return result

def main(path):
    lines = []
    with open(path) as inputfile:
        for line in inputfile:
            if not line.startswith(SExp.COMMENT):
                lines.append(line)
    sexp_str = "".join(lines)
    rg = ReasoningDag(sexp_str)
    print(rg)
    rg.execute()

if __name__ == "__main__":
    main(sys.argv[1])
