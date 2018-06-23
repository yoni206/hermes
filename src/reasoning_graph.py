import sys
from enum import Enum
from sexpdata import loads, dumps, car, cdr


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
    ASSUMPTIONS = "kb"
    CONCLUSION = "g"
    SAT = "sat"
    MODEL = "model"

class EdgeType(Enum):
    SIMPLE = 1
    SMTLIB = 2

    def from_string(str):
        if str == STRING_CONSTANTS.SIMPLE:
            return EdgeType.SIMPLE
        elif str == STRING_CONSTANTS.SMTLIB:
            return EdgeType.SMTLIB
        else:
            assert(False)

class Edge:
    def __init__(self, name, src, dest):
        self.name = name
        self.src = src
        self.dest = dest


    def get_type(self):
        raise NotImplementedError("get_type() must be overriden by sub-classes")


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
        self.edges = set([])

    def get_type(self):
        raise NotImplementedError("get_type() must be overriden by sub-classes")

    def generate_from_sexp(e):
        raise NotImplementedError("generate_from_sexp() must be overriden by sub-classes")


    def connect_edge_to_port(edge, port_name):
        raise NotImplementedError("connect_edge_to_port() must be overriden by sub-classes")


class EntailmentNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._assumptions = set([]) #set of edges
        self._conclusion = None #edge
        self._sat = None #edge
        self._model = set([]) #edge

    def get_type(self):
        return NodeType.ENTAILMENT

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return EntailmentNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        if (port_name == STRING_CONSTANTS.ASSUMPTIONS):
            self._assumptions.add(edge)
        elif (port_name == STRING_CONSTANTS.CONCLUSION):
            self._conclusion = edge
        elif (port_name == STRING_CONSTANTS.SAT):
            self._sat = edge
        elif (port_name == STRING_CONSTANTS.MODEL):
            self._model.add(edge)
        else:
            assert(False)

class DoneNode(Node):
    def __init__(self, name):
        super().__init__(name)
        _input_edge = None

    def get_type():
        return NodeType.DONE

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return DoneNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        self._input_edge = edge

class StartNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._output_edge = None

    def get_type():
        return NodeType.START

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return StartNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        self._output_edge = edge

class AndNode(Node):
    def __init__(self, name):
        super().__init__(name)
        self._conjuncts = set([]) #set of edges
        self._output = None #edge

    def get_type():
        return NodeType.AND

    def generate_from_sexp(e):
        node_name = dumps(car(e))
        node_sexp_after_name = cdr(e)
        return AndNode(node_name)

    def connect_edge_to_port(self, edge, port_name):
        self._conjuncts.add(edge)



class ReasoningGraph:

    def __init__(self, sexp_str):
        self._sexp = loads(sexp_str)
        self._nodes_dict_by_name = {}
        self._generate_reasoning_graph_from_sexp()

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
        edge_type, src_node, src_port, dest_node, dest_port, smtlib = \
            self._get_type_src_dest_and_smtlib_of_edge_from_sexp(e)
        if edge_type is EdgeType.SIMPLE:
            edge = SimpleEdge("", src_node, dest_node)
        elif edge_type is EdgeType.SMTLIB:
            edge = SmtLibEdge("", src_node, dest_node, smtlib)
        src_node.connect_edge_to_port(edge, src_port)
        dest_node.connect_edge_to_port(edge, dest_port)

    def _get_type_src_dest_and_smtlib_of_edge_from_sexp(self, e):
        first = car(e)
        second = car(cdr(e))
        try:
            third = car(cdr(cdr(e)))
        except IndexError:
            third = None

        if (third is not None):
            src_node_name, src_port_name = dumps(first).split("\\.")
            dest_node_name, dest_port_name = dumps(second).split("\\.")
            dest_node_name = dumps(second)
            assert(dumps(car(third)).startswith(STRING_CONSTANTS.SMTLIB))
            smtlib = dumps(car(cdr(third)))
            src = self._nodes_dict_by_name[src_node_name]
            dest = self._nodes_dict_by_name[dest_node_name]
            edge_type = EdgeType.SMTLIB
        else:
            smtlib_flag = True
            try:
                car(second)
            except TypeError:
                smtlib_flag = False
            if (smtlib_flag and (dumps(car(second)) == STRING_CONSTANTS.SMTLIB)):
                edge_type = EdgeType.SMTLIB
                node_name, port_name = dumps(first).split("\\.")
                assert(dumps(car(second)).startswith(STRING_CONSTANTS.SMTLIB))
                smtlib = dumps(car(cdr(second)))
                if port_name in ["in1", "in2", "in", "g", "kb"]:
                    src = StartNode("start")
                    src_port_name = "exit_port"
                    dest = self._nodes_dict_by_name[node_name]
                    dest_port_name = port_name
                else:
                    src = self._nodes_dict_by_name[node_name]
                    src_port_name = port_name
                    dest = DoneNode("done")
            else:
                smtlib = None
                src_node_name, src_port_name = dumps(first).split("\\.")
                dest_node_name, dest_port_name = dumps(second).split("\\.")
                src = self._nodes_dict_by_name[src_node_name]
                dest = self._nodes_dict_by_name[dest_node_name]
                edge_type = EdgeType.SIMPLE

        return edge_type, src, src_port_name, dest, dest_port_name, smtlib


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
    rg = ReasoningGraph(sexp_str)
    print(rg._nodes_dict_by_name["n1"].name)
    print(rg._nodes_dict_by_name["n1"].get_type())
    assumptions = rg._nodes_dict_by_name["n1"]._assumptions
    for assumption in assumptions:
        print(assumption.smtlib)

if __name__ == "__main__":
    main(sys.argv[1])
