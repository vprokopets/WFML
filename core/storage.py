import copy
import logging


class Storage:
    def __init__(self, workspace):
        self.workspace = workspace
        self.stage_snap = {}
        self.last_snap = {}

    def restore_stage_snap(self, step=None):
        """
        Function to restore stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.

        RETURN
        Stage snapshot.
        """

        self.workspace.features = copy.deepcopy(self.stage_snap[step]['Features'] if step is not None 
                                                else self.last_snap['Features'])
        constr_meta = copy.deepcopy(self.stage_snap[step]['Constraints'] if step is not None 
                                    else self.last_snap['Constraints'])
        self.workspace.configuration_history = copy.deepcopy(self.stage_snap[step]['History'] if step is not None
                                                             else self.last_snap['History'])
        for k, v in constr_meta.items():
            self.workspace.constraints[k].update({'Metadata': v})

        if step is not None:
            rm_steps = []
            for snap_step in self.stage_snap.keys():
                if int(snap_step) >= int(step):
                    rm_steps.append(snap_step)
            for rm_step in rm_steps:
                del self.stage_snap[rm_step]
        logging.info(f"Namespace was restored due to {'unvalidated constraint' if step is None else 'going to previous step'}.")

    def save_stage_snap(self, step, data):
        """
        Function to read stage snapshot by keyword.

        INPUTS
        step (type = str): step's keyword.
        data (type = dict): fields for this step
        """
        constr_meta = {}
        for k, v in self.workspace.constraints.items():
            constr_meta.update({k: v['Metadata']})
        self.last_snap = {
            'Features': copy.deepcopy(self.workspace.features),
            'Constraints': copy.deepcopy(constr_meta),
            'Fields': data,
            'History': copy.deepcopy(self.workspace.configuration_history)
        }
        self.stage_snap.update({step: copy.deepcopy(self.last_snap)})

    def register_initialization_data(self, dependencies, configuration_sequence, sequence_filtered,
                                     constraint_groups, constraint_groups_representation, test_sequence):

        self.dependencies = dependencies
        self.configuration_sequence = configuration_sequence
        self.sequence_filtered = sequence_filtered
        self.constraint_groups = constraint_groups
        self.constraint_groups_representation = constraint_groups_representation
        self.workspace.constraint_groups_w = constraint_groups
        self.test_sequence = test_sequence
