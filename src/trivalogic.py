from enum import IntEnum

class Values(IntEnum):
    TRUE = 3
    UNKNOWN = 2
    FALSE = 1

    def to_string(v):
        if v == Values.TRUE:
            return "true"
        elif v == Values.FALSE:
            return "false"
        elif v == Values.UNKNOWN:
            return "unknown"

class TriValLogic:
    def kleene_and(conjuncts):
        return min([int(x) for x in conjuncts])

