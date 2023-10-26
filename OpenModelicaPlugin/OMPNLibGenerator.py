import json


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
    componentsStr = ""
    equationsStr = ""
    for component_collection_name, components in json_data.items():
        for component_name, properties in components.items():
            if component_collection_name == "Arcs":
                startName = properties["start"].split(".")[-1]
                endName = properties["end"].split(".")[-1]

                startCount = 1 + equationsStr.count("connect(" + startName)
                endCount = 1 + equationsStr.count("," + endName)
                if "Transition" in properties["start"]:
                    startName += ".outPlaces[" + str(startCount) + "]"

                else:
                    startName += ".outTransition[" + str(startCount) + "]"

                if "Transition" in properties["end"]:
                    endName += ".inPlaces[" + str(endCount) + "]"
                else:
                    endName += ".inTransition[" + str(endCount) + "]"
                # example connect(PD_0.outPlaces[1],T_0.inTransition[1]);
                equationsStr += "        connect(" + startName + "," + endName + ");\n"
            else:
                # example : PNlib.Components.PD PD_0
                componentsStr += f"    PNlib.Components.{component_name.split('_')[0]} {component_name}("

                # example (startTokens=1,nIn=0,nOut=1);
                for property_name, property_value in properties.items():
                    if property_value:
                        componentsStr += f"{property_name}={property_value},"
                componentsStr = f"{componentsStr[:-1]});\n"

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
