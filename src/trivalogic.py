from enum import Enum

class Values(Enum):
    TRUE = 3
    UNKNOWN = 2
    FALSE = 1

class TriValLogic:
    def kleene_and(conjuncts):
        return min(conjuncts)

