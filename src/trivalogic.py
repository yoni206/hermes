from enum import IntEnum

class Values(IntEnum):
    TRUE = 3
    UNKNOWN = 2
    FALSE = 1

class TriValLogic:
    def kleene_and(conjuncts):
        return min([int(x) for x in conjuncts])

def to_int(v):
    return int(v)


