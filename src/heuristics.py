from itertools import combinations, chain
import collections
import pprint
from pysmt.shortcuts import get_env, Solver, Equals, And
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.smtlib.script import SmtLibScript
from portfolio_solver import PortfolioSolver, SolverResult
from trivalogic import Values
from six.moves import cStringIO
from transcendental import ExtendedEnvironment, reset_env
from transcendental import ExtendedSmtLibParser
from pysmt.rewritings import Skolemization

pp = pprint.PrettyPrinter(indent=4)

class Inequality(object):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return "[" + str(self.left) + ", " + str(self.right) + "]"

    def __repr__(self):
        return self.__str__()

    def from_tuple(tup):
        result = set([])
        ls = list(tup)
        for x in ls:
            result.add(x)
        return result

class SegmentsHeuristics:
    def __init__(self, smtlib, config):
        reset_env()
        self._smtlib = smtlib
        parser = ExtendedSmtLibParser()
        stream = cStringIO(smtlib)
        script = parser.get_script(stream)
        self._formula = script.get_last_formula()
        s = Skolemization(get_env())
        self._formula = s.simple_skolemization(self._formula)
        self._inequals = set([])
        self._quantified_variables = set([])
        self._generate_quantified_variables(self._formula)
        self._generate_inequals(self._formula)
        self._config = config

    def _should_be_added(self, inequality):
        left = inequality.left
        right = inequality.right
        variables = set([])
        variables.update(left.get_free_variables())
        variables.update(right.get_free_variables())
        not_bound = len(variables.intersection(self._quantified_variables)) == 0

        has_constant = left.is_constant() or right.is_constant()

        return not_bound and has_constant

    def _generate_quantified_variables(self, formula):
        if formula.is_quantifier():
            q_vars = formula.quantifier_vars()
            self._quantified_variables.update(q_vars)
        else:
            for arg in formula.args():
                self._generate_quantified_variables(arg)

    def _generate_inequals(self, formula):
        if formula.is_le():
            inequality = Inequality(left=formula.args()[0], right=formula.args()[1])
            if self._should_be_added(inequality):
                self._inequals.add(inequality)
        else:
            for arg in formula.args():
                self._generate_inequals(arg)

    def try_to_unsatisfy(self):
        solver = PortfolioSolver(self._smtlib, self._config)
        options = []
        singles = list(singletons(self._inequals))
        for single in singles:
            print('panda ', single)
            solver.add_assertion(Equals(single.left, single.right))
            result, values = solver.solve()
            print('panda ', result)
            if result == SolverResult.UNSAT:
                options.append(single)
        return options

def singletons(iterable):
    xs = list(iterable)
    return chain.from_iterable(combinations(xs,1))

def ordered_non_empty_subsets(iterable, size):
    """
    powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    """
    xs = list(iterable)

    # note we return an iterator rather than a list
    return chain.from_iterable(combinations(xs,size) for n in range(1,len(xs)+1))
