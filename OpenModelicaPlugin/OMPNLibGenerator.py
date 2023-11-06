import json
import networkx as nx


def wfml_json_to_om_pnlib_file(jsonPath):
    """
    Method that takes the wfml json feature model of a petri net and converts it to a OpenModelica PNLib file
    :param jsonPath: path to the json file from wfml
    :type jsonPath: str
    :return: openmodelica file using the PNlib
    :rtype: TextIOWrapper
    """
    data = json.load(open(jsonPath))
    name = list(data.keys())[0]
    componentsStr, equationsStr = parse_wfml_json_data(data[name])
    modelicaFile = open("./core/output/output.mo", "w")
    om_model_str = generate_pnlib_model(name, componentsStr, equationsStr)
    modelicaFile.write(om_model_str)
    return open("./core/output/output.mo", "r")


def parse_wfml_json_data(json_data):
    """
    Method to parse wfml feature petri net and generate modelica component / equation strings
    :param json_data: json data containing feature model petri net places, arcs and transitions
    :type json_data: dict
    :return: components and equations for openmodelica as strings
    :rtype: str,str
    """
    graph = generate_graph(json_data)
    componentsStr = ""
    equationsStr = ""
    for component_collection_name, components in json_data.items():
        for component_name, properties in components.items():
            if component_collection_name == "Arcs":
                startName = properties["start"].split(".")[-1]
                endName = properties["end"].split(".")[-1]
                pos_start = graph.get(startName)
                pos_end = graph.get(endName)
                startCount = 1 + equationsStr.count("connect(" + startName)
                endCount = 1 + equationsStr.count("," + endName)
                if "Transition" in properties["start"]:
                    startName += f".outPlaces[{str(startCount)}]"

                else:
                    startName += f".outTransition[{str(startCount)}]"

                if "Transition" in properties["end"]:
                    endName += f".inPlaces[{str(endCount)}]"
                else:
                    endName += f".inTransition[{str(endCount)}]"
                # example connect(PD_0.outPlaces[1],T_0.inTransition[1]);

                line_points_str = f"{{{int(pos_start[0])},{int(pos_start[1])}}},{{{int(pos_end[0])},{int(pos_end[1])}}}"
                equationsStr += f"        connect({startName},{endName}) annotation(\n"
                equationsStr += f"   Line(points = {{{line_points_str}}} , thickness = 0.5));\n"
            else:
                # example : PNlib.Components.PD PD_0
                componentsStr += f"    PNlib.Components.{component_name.split('_')[0]} {component_name}("

                # example (startTokens=1,nIn=0,nOut=1);
                for property_name, property_value in properties.items():
                    if property_value:
                        componentsStr += f"{property_name}={property_value},"
                comp_pos = graph.get(component_name)
                pos = f"{{{comp_pos[0]}, {comp_pos[1]}}}"
                transform = f"origin = {pos}, extent = {{{{-10, -10}}, {{10, 10}}}}, rotation = 0)"
                componentsStr = (
                    f"{componentsStr[:-1]}) annotation(\n    Placement(visible = true, transformation({transform}));"
                )

    return componentsStr, equationsStr


def generate_pnlib_model(name, components, equations):
    """
    Generate modelica PNLib file structure
    :param name: name of model
    :type name: str
    :param components: places and transitions of pn model
    :type components: str
    :param components: arcs of pn model
    :type components: str
    :return: modelica file structure of petri net
    :type: str
    """
    return (
        "model "
        + name
        + "\n"
        + components
        + "    equation\n"
        + equations
        + "    annotation(\n"
        + '        uses(PNlib(version = "2.2"))\n'
        + "    );\n"
        + "end "
        + name
        + ";"
    )


def generate_graph(json_data):
    G = nx.Graph()
    nodes = []
    edges = []
    for component_collection_name, components in json_data.items():
        for component_name, properties in components.items():
            if component_collection_name == "Arcs":
                startName = properties["start"].split(".")[-1]
                endName = properties["end"].split(".")[-1]
                if startName not in nodes:
                    nodes.append(startName)
                if endName not in nodes:
                    nodes.append(endName)
                edges.append((startName, endName))
    for node in nodes:
        G.add_node(node)
    for edge in edges:
        G.add_edge(edge[0], edge[1])
    return nx.spring_layout(G, scale=75)
