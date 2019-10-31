from enum import Enum
from typing import Dict, List


class Kind2Object(Enum):
    kind2Options = 'kind2Options'
    log = 'log'
    analysisStart = 'analysisStart'
    property = 'property'
    analysisStop = 'analysisStop'


class Answer(Enum):
    valid = 'valid'
    falsifiable = 'falsifiable'
    unknown = 'unknown'


class Property:
    def __init__(self, name: str, scope: str, line: int, column: int, answer: Answer):
        self.name, self.scope, self.line, self.column, self.answer = name, scope, line, column, answer


class Kind2Analysis:
    def __init__(self, json_object: Dict[str, str]):
        self.top = json_object['top']
        self.abstract = json_object['abstract']
        self.concrete = json_object['concrete']
        self.assumptions = json_object['assumptions']
        self.properties = []

    def add_property(self, json_object: Dict[str, str]):
        name, scope, line = json_object['name'], json_object['scope'], json_object['line']
        column, answer = json_object['column'], Answer(json_object['answer']['value'])
        self.properties.append(Property(name, scope, line, column, answer))


class Kind2Result:
    analyses: Dict[str, List[Kind2Analysis]]
    suggestions: List[str]
    explanations: List[str]

    def __init__(self):
        self.analyses = {}
        self.suggestions = []
        self.explanations = []

    def put_analysis(self, node: str, analysis: Kind2Analysis):
        if node in self.analyses.keys():
            self.analyses[node].append(analysis)
        else:
            self.analyses[node] = [analysis]

    def get_suggestions_and_explanations(self):
        if not self.abstract and not self.assumptions:
            self.suggestions.append("No action required.")
            self.explanations.append("No component of the system was refined.")



