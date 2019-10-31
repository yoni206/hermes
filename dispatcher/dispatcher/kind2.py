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


class SuggestionType(Enum):
    NoActionRequired = 1
    FixContract = 2
    CompleteSpecificationOrRemoveComponent = 3
    MakeWeakerOrFixDefinition = 4
    MakeAssumptionStrongerOrFixDefinition = 5
    FixReportedIssues = 6


class Property:
    def __init__(self, json_object: dict):
        self.json = json_object
        self.name = json_object['name']
        self.scope = json_object['scope']
        self.line = json_object['line']
        self.column = json_object['column']
        self.answer = Answer(json_object['answer']['value'])


class Analysis:
    def __init__(self, json_object: Dict[str, str]):
        self.json = json_object
        self.top = json_object['top']
        self.abstract = json_object['abstract']
        self.concrete = json_object['concrete']
        self.assumptions = json_object['assumptions']
        self.properties = []

    def add_property(self, json_object: Dict[str, str]):
        self.properties.append(Property(json_object))


class Suggestion:
    suggestionType: SuggestionType
    explanations: List[str]
    label: str

    def __init__(self, suggestion_type: SuggestionType):
        self.suggestionType = suggestion_type
        self.explanations = []

    def __str__(self):
        string: str = "Suggestion: " + self.label + "\n"
        for explanation in self.explanations:
            string += explanation + "\n"
        return string

    @classmethod
    def no_action_required(cls):
        # suggestion 1
        suggestion = cls(SuggestionType.NoActionRequired)
        suggestion.label = "No action required"
        suggestion.explanations.append('All components of the system satisfy their contract')
        suggestion.explanations.append('No component of the system was refined.')
        return suggestion

    @classmethod
    def not_proved_properties(cls, analysis: Analysis, not_proved_properties: List[Property]):
        # suggestion 6
        suggestion = cls(SuggestionType.FixReportedIssues)
        suggestion.label = "Fix reported issues for {}'s subcomponents.".format(analysis.top)
        suggestion.explanations.append(
            'Component {} does not satisfy its contract after refinement'.format(analysis.top))
        # suggestion.explanations.append('No component of the system was refined.')
        return suggestion


class NodeResult:
    node_analyses: List[Analysis]
    node_name: str
    suggestion: Suggestion

    def __init__(self, node_name: str, analysis: Analysis):
        self.node_name = node_name
        self.node_analyses = [analysis]

    def append(self, analysis: Analysis):
        self.node_analyses.append(analysis)

    def set_suggestion(self, suggestion: Suggestion):
        self.suggestion = suggestion

    def __str__(self):
        string: str = "Component: " + self.node_name + "\n"
        string += str(self.suggestion)
        return string


class Kind2Result:
    result_dict: Dict[str, NodeResult]

    def __init__(self):
        self.result_dict = {}

    def put_analysis(self, node: str, analysis: Analysis):
        if node in self.result_dict.keys():
            self.result_dict[node].append(analysis)
        else:
            self.result_dict[node] = NodeResult(node, analysis)

    def analyze(self):
        for node in self.result_dict.keys():
            node_result: NodeResult = self.result_dict[node]
            node_analyses: List[Analysis] = node_result.node_analyses
            # case of a single analysis for this node
            if len(node_result.node_analyses) == 1:
                # filter properties that are not proved to be valid
                not_proved_properties = list(filter(lambda p: (p.answer != Answer.valid), node_analyses[0].properties))
                if len(not_proved_properties) == 0:
                    # suggestion 1
                    node_result.set_suggestion(Suggestion.no_action_required())
                else:
                    # suggestion 6
                    node_result.set_suggestion(
                        Suggestion.not_proved_properties(node_analyses[0], not_proved_properties))
            else:
                raise Exception('Not implemented yet.')

    def __str__(self):
        string: str = ""
        for node_result in self.result_dict.values():
            string += str(node_result) + "\n"
        return string


def analyze_json_result(json_result):
    kind2_result = Kind2Result()
    for json_object in json_result:
        analysis: Analysis
        if Kind2Object(json_object['objectType']) == Kind2Object.analysisStart:
            analysis = Analysis(json_object)
        elif Kind2Object(json_object['objectType']) == Kind2Object.property:
            analysis.add_property(json_object)
        elif Kind2Object(json_object['objectType']) == Kind2Object.analysisStop:
            kind2_result.put_analysis(analysis.top, analysis)
        else:
            pass

    return kind2_result
