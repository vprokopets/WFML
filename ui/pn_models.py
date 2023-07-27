class PetriNetModels:
    dpn_model = "\
        DPN{\
            Places {\
                PD* {\
                    startTokens-> integer\
                    nIn -> integer\
                    nOut -> integer\
                    [nIn >= 0]\
                    [nOut >= 0]\
                }\
            }\
            Transitions {\
                T* {\
                    nIn -> integer\
                    nOut -> integer\
                    [nIn >= 0]\
                    [nOut >= 0]\
                }\
            }\
            Arcs {\
                Arc*{\
                    start -> string\
                    end -> string\
                    [start in childs.DPN.Places or start in childs.DPN.Transitions]\
                    [end in childs.DPN.Places or end in childs.DPN.Transitions]\
                    [start != end]\
                }\
            }\
        }\
    "
    hpn_model = "\
        HPN{\
            Places {\
                PD* {\
                    startTokens-> integer\
                    nIn -> integer\
                    nOut -> integer\
                    [nIn >= 0]\
                    [nOut >= 0]\
                }\
                PC* {\
                    startMarks -> float\
                    nIn -> integer\
                    nOut -> integer\
                    [nIn >= 0]\
                    [nOut >= 0]\
                }\
            }\
            Transitions {\
                TD* {\
                    nIn -> integer\
                    nOut -> integer\
                    delay -> integer\
                    [nIn >= 0]\
                    [nOut >= 0]\
                    [delay >= 0]\
                }\
                TC*{\
                    nIn -> integer\
                    nOut -> integer\
                    maximumSpeed -> float\
                    [nIn >= 0]\
                    [nOut >= 0]\
                }\
            }\
            Arcs {\
                Arc*{\
                    start -> string\
                    end-> string\
                    [start in childs.HPN.Places or start in childs.HPN.Transitions]\
                    [end in childs.HPN.Places or end in childs.HPN.Transitions]\
                    [start != end]\
                    [if start in childs.HPN.Places.PD then end not in childs.HPN.Transitions.TC]\
                    [if start in childs.HPN.Transitions.TC then end not in childs.HPN.Places.PD]\
                }\
            }\
        }\
    "
