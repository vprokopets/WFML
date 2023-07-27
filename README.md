### WFML Modelica Coupling

This project is extending the [WFML](https://github.com/vprokopets/WFML) project by adding feature Models for the PNlib of Modelica. This allows for the creation of validated PetriNet simulation files. Additionally the projects adds the possibility to download a Modelica Simulation file at the end of the WFML configuration process.

To run the project, please follow the instructions below. Once WFML is running the Petri net configuration can be found under ```127.0.0.1:8000/wizard/pn-models/```

## Language Overview

#### Core

Core describes lexer, parser, and transpiler to JSON functionality;

#### User Interface

UI is implemented with the Django framework.

## Installation and launch

WFML could be launched in two modes:

#### Standalone

This will launch django server on ```127.0.0.1:8000```

#### Docker-compose

This option will build a docker container for application and launch Django server on ```127.0.0.1:8000``` through docker-compose bridge networking

For more information about WFML management, please use ```./wfml.sh help```

## Requirements

Docker (version 20.10.8+) - **only for Docker-compose mode**

Docker-compose (version 1.29.2+) - **only for Docker-compose mode**

Python (version 3.7+) with actual pip installed - **only for Standalone mode**

#### Required pip packaged are listed in ![requirements.txt](requirements.txt) and could be installed with

```python3.7 -m pip install --no-cache-dir -q -r *path_to_requirements.txt*```

## License

![MIT](LICENSE)
