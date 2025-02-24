import copy
import random

import networkx as nx


class DependencyGraph:
    def __init__(self):
        self.graph_configuration = {
            'Features': {
                'Layout': 'Hierarchical',
                'Limitation': None,
                'Priority': 1
            },
            'ConstraintGroups': {
                'Layout': 'Random',
                'Limitation': 'Waffle_Constraint_Group_',
                'Priority': 2
            },
            'Constraints': {
                'Layout': 'Random',
                'Limitation': 'Constraint_',
                'Priority': 3
            }
        }
        self.scale = 2
        self.val_map = {
            'Feature': {
                'NotConfigured': 1.0,
                'Configured': 0.5714285714285714,
                'Skipped': 0.0
            },
            'Constraint': {
                'NotValidated': 1.0,
                'Validated': 0.5714285714285714,
                'Skipped': 0.0
            }
        }

    def define_graph_layout(self, dependencies):
        # TODO: investigate the nessessity of labels_dict or remove it
        labels_dict, fnum, node_sets, categorized_dependencies = self._transform_labels(dependencies, self.graph_configuration)
        self.graph_obj, self.pos = self._define_element_positions(self.graph_configuration, node_sets, categorized_dependencies)
        deps_transformed = []
        for category in categorized_dependencies.values():
            for dep in category:
                deps_transformed.append((dep[0], dep[1]))
        self.graph_obj.add_edges_from(deps_transformed)
        self.constraint_edges = []
        for dependency in deps_transformed:
            for edge in dependency:
                if isinstance(fnum[edge], str) and fnum[edge].startswith('Constraint_'):
                    self.constraint_edges.append(dependency)
                    break

        values = [self.val_map.get(node, 0.25) for node in self.graph_obj.nodes()]
        # edge_colours = ['black' if edge not in self.constraint_edges else 'red'
        #                 for edge in G.edges()]
        # black_edges = [edge for edge in G.edges() if edge not in red_edges]

        # Create Node and Edge list with appropriate data
        self.nodes = [
            {
                "id": node,
                "x": float(self.pos[node][0]),
                "y": float(-self.pos[node][1]),
                'label_short': fnum[node].rsplit('.')[-1],
                'label_long': fnum[node],
                'value': None,
                'data': None,
                'color': '#FFCC33'
            }
            for node in self.graph_obj.nodes
        ]
        self.node_indices = {}
        for index, node in enumerate(self.nodes):
            self.node_indices.update({node['label_long']: index})
        self.edges = [
            {
                "source": edge[0],
                "target": edge[1],
                "source_label": fnum[edge[0]],
                "target_label": fnum[edge[1]],
                'label': f"Edge {edge}",
                'color': 'black' if edge not in self.constraint_edges else 'red'  # Assign red to selected edges, otherwise black
            }
            for edge in self.graph_obj.edges
        ]

    def get_graph_state(self):
        nodes = copy.deepcopy(self.nodes)
        edges = copy.deepcopy(self.edges)
        data = {"nodes": nodes, "edges": edges, 'indices': self.node_indices}
        return data

    def update_graph_colors(self, colors):
        pass

    def _hierarchy_branch_pos(self, G, root, leftmost, width, leafdx=0.2, vert_gap=0.2, vert_loc=0,
                              xcenter=0.5, rootpos=None,
                              leafpos=None, parent=None):
        '''
        see hierarchy_pos docstring for most arguments

        pos: a dict saying where all nodes go if they have been assigned
        parent: parent of this branch. - only affects it if non-directed

        '''

        if rootpos is None:
            rootpos = {root: (xcenter, vert_loc)}
        else:
            rootpos[root] = (xcenter, vert_loc)
        if leafpos is None:
            leafpos = {}
        children = list(G.neighbors(root))
        leaf_count = 0
        if not isinstance(G, nx.DiGraph) and parent is not None:
            children.remove(parent)
        if len(children) != 0:
            rootdx = width/len(children)
            nextx = xcenter - width/2 - rootdx/2
            for child in children:
                nextx += rootdx
                rootpos, leafpos, newleaves = self._hierarchy_branch_pos(G, child, leftmost+leaf_count*leafdx,
                                                                         width=rootdx, leafdx=leafdx,
                                                                         vert_gap=vert_gap, vert_loc=vert_loc-vert_gap,
                                                                         xcenter=nextx, rootpos=rootpos,
                                                                         leafpos=leafpos, parent=root)
                leaf_count += newleaves

            leftmostchild = min((x for x, y in [leafpos[child] for child in children]))
            rightmostchild = max((x for x, y in [leafpos[child] for child in children]))
            leafpos[root] = ((leftmostchild+rightmostchild)/2, vert_loc)
        else:
            leaf_count = 1
            leafpos[root] = (leftmost, vert_loc)
        return rootpos, leafpos, leaf_count

    def _hierarchy_pos(self, edges, root=None, width=1., vert_gap=0.2, vert_loc=0, leaf_vs_root_factor=0.5):

        '''
        If the graph is a tree this will return the positions to plot this in a
        hierarchical layout.

        Based on Joel's answer at https://stackoverflow.com/a/29597209/2966723,
        but with some modifications.

        We include this because it may be useful for plotting transmission trees,
        and there is currently no networkx equivalent (though it may be coming soon).

        There are two basic approaches we think of to allocate the horizontal
        location of a node.

        - Top down: we allocate horizontal space to a node.  Then its ``k``
            descendants split up that horizontal space equally.  This tends to result
            in overlapping nodes when some have many descendants.
        - Bottom up: we allocate horizontal space to each leaf node.  A node at a
            higher level gets the entire space allocated to its descendant leaves.
            Based on this, leaf nodes at higher levels get the same space as leaf
            nodes very deep in the tree.

        We use use both of these approaches simultaneously with ``leaf_vs_root_factor``
        determining how much of the horizontal space is based on the bottom up
        or top down approaches.  ``0`` gives pure bottom up, while 1 gives pure top
        down.


        :Arguments:

        **G** the graph (must be a tree)

        **root** the root node of the tree
        - if the tree is directed and this is not given, the root will be found and used
        - if the tree is directed and this is given, then the positions will be
            just for the descendants of this node.
        - if the tree is undirected and not given, then a random choice will be used.

        **width** horizontal space allocated for this branch - avoids overlap with other branches

        **vert_gap** gap between levels of hierarchy

        **vert_loc** vertical location of root

        **leaf_vs_root_factor**

        xcenter: horizontal location of root
        '''
        G = nx.Graph()
        G.add_edges_from(edges)
        if not nx.is_tree(G):
            raise TypeError('cannot use hierarchy_pos on a graph that is not a tree')

        if root is None:
            if isinstance(G, nx.DiGraph):
                root = next(iter(nx.topological_sort(G)))  # allows back compatibility with nx version 1.11
            else:
                root = random.choice(list(G.nodes))

        xcenter = width/2.
        if isinstance(G, nx.DiGraph):
            leafcount = len([node for node in nx.descendants(G, root) if G.out_degree(node) == 0])
        elif isinstance(G, nx.Graph):
            leafcount = len([node for node in nx.node_connected_component(G, root) if G.degree(node) == 1 and node != root])
        rootpos, leafpos, _ = self._hierarchy_branch_pos(G, root, 0, width,
                                                         leafdx=width*1./leafcount,
                                                         vert_gap=vert_gap,
                                                         vert_loc=vert_loc,
                                                         xcenter=xcenter)
        pos = {}
        for node in rootpos:
            pos[node] = (leaf_vs_root_factor*leafpos[node][0] + (1-leaf_vs_root_factor)*rootpos[node][0], leafpos[node][1]) 
        xmax = max(x for x, y in pos.values())
        for node in pos:
            pos[node] = (pos[node][0]*width/xmax, pos[node][1])
        return pos

    def _define_element_positions(self, graph_metadata, node_sets, categorized_dependencies, title="Subgraphs in Grid Layout",
                                  spacing=2.0, node_colors=None):
        """
        Draw multiple subgraphs in a grid layout

        Parameters:
        - subgraphs: list of networkx graphs
        - title: plot title
        - spacing: space between subgraphs
        - node_colors: list of colors for each subgraph
        """

        if node_colors is None:
            node_colors = ['lightblue'] * len(graph_metadata)

        G = nx.DiGraph()
        # Combined position dictionary for all nodes
        pos_combined = {}
        offset = 0
        # Process each set with its specified layout
        for node_set_name, node_set in node_sets.items():
            if node_set != []:
                # Create subgraph for this set
                Gtemp = nx.Graph()
                Gtemp.add_nodes_from(node_set)
                layout_type = graph_metadata[node_set_name]['Layout']

                # Get layout for this set
                if layout_type == 'Circular':
                    pos = nx.circular_layout(Gtemp)
                elif layout_type == 'Spring':
                    pos = nx.spring_layout(Gtemp)
                elif layout_type == 'Shell':
                    pos = nx.shell_layout(Gtemp)
                elif layout_type == 'Random':
                    pos = nx.random_layout(Gtemp),
                elif layout_type == 'Hierarchical':
                    try:
                        pos = self._hierarchy_pos(categorized_dependencies[node_set_name], 1)
                    except TypeError:
                        pos = nx.spring_layout(Gtemp)
                else:
                    raise ValueError(f"Unsupported layout type: {layout_type}")

                if isinstance(pos, tuple):
                    pos = pos[0]

                y_coords = [coord[1] for coord in pos.values()]

                for node in pos:
                    x, y = pos[node]
                    pos_combined[node] = (
                        self.scale * x,
                        self.scale * (y - offset - max(y_coords) + min(y_coords) if offset > 0 else y)
                    )
                offset += abs(min(y_coords)) + 2
                # Add nodes to the main graph
                G.add_nodes_from(node_set)
        return G, pos_combined

    def _transform_labels(self, feature_deps, graph_configuration):
        labels_dict = {}
        counter = 1
        node_sets = {key: [] for key in graph_configuration}
        categorized_dependencies = {key: [] for key in graph_configuration}
        for dependency in feature_deps:
            dep = []
            feature_group, group_priority = None, 0
            for feature in dependency:
                if feature not in labels_dict.keys():
                    labels_dict.update({feature: counter})
                    numerical_id = counter
                    dep.append(numerical_id)
                    counter += 1
                else:
                    numerical_id = labels_dict[feature]
                    dep.append(numerical_id)
                feature_set = None
                for key, values in graph_configuration.items():
                    if values['Limitation'] is None:
                        feature_set = key if feature_set is None else feature_set
                        feature_group = key if values['Priority'] > group_priority else feature_group
                        group_priority = values['Priority'] if values['Priority'] > group_priority else group_priority

                    elif feature.startswith(values['Limitation']):
                        feature_set = key
                        feature_group = key if values['Priority'] > group_priority else feature_group
                        group_priority = values['Priority'] if values['Priority'] > group_priority else group_priority

                if numerical_id not in node_sets[feature_set]:
                    node_sets[feature_set].append(numerical_id)
            categorized_dependencies[feature_group].append(dep)
        feature_nummeration = {}
        for k, v in labels_dict.items():
            feature_nummeration.update({v: k})

        return labels_dict, feature_nummeration, node_sets, categorized_dependencies
