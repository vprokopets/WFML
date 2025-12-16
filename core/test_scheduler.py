import collections
import graphlib  # Requires Python 3.9+
import sys  # For checking python version


class TestScheduler():
    def __init__(self):
        pass

    def get_initial_schedule_and_info(self, dependencies):
        """
        Performs a standard topological sort and gathers node info.

        Returns:
            tuple: (initial_schedule, node_info, all_nodes) or (None, None, None) on error.
            initial_schedule: List of tuples representing steps.
            node_info: Dict mapping node name to its details (predecessors, etc.).
            all_nodes: Set of all unique node names.
        """
        # Check Python version for graphlib availability
        if sys.version_info < (3, 9):
            print("Error: This script requires Python 3.9+ for the 'graphlib' module.")
            return None, None, None

        graph = collections.defaultdict(set)
        all_nodes = set(dependencies.keys())
        node_info = {}

        # Build graph and node_info simultaneously
        for node, deps in dependencies.items():
            predecessors = set(deps.get('After', []))
            successors = set(deps.get('Before', []))
            is_constraint = node.startswith("Constraint_")
            is_gating = is_constraint and bool(successors)

            node_info[node] = {
                'predecessors': predecessors,
                'successors': successors,
                'is_constraint': is_constraint,
                'is_gating': is_gating,  # Keep track even if not used in this version
            }

            graph[node] = predecessors
            all_nodes.update(predecessors)
            all_nodes.update(successors)

        # Ensure all nodes mentioned anywhere exist in graph and node_info
        for node in list(all_nodes):  # Iterate over copy as we might modify all_nodes
            if node not in graph:
                graph[node] = set()
            if node not in node_info:
                is_constraint = node.startswith("Constraint_")
                node_info[node] = {
                    'predecessors': set(), 'successors': set(),
                    'is_constraint': is_constraint, 'is_gating': False
                }
                all_nodes.add(node)  # Ensure it's in the set

        # Perform Topological Sort
        try:
            ts = graphlib.TopologicalSorter(graph)
            ts.prepare()
            initial_schedule = []
            while ts.is_active():
                ready_nodes = sorted(list(ts.get_ready()))
                if not ready_nodes:
                    print("Error during initial sort: No nodes ready but graph is active.")
                    # Debugging info
                    processed_in_ts = getattr(ts, '_marked', set())  # Access internal if needed
                    remaining_nodes = all_nodes - processed_in_ts
                    print(f"Remaining nodes: {remaining_nodes}")
                    for r_node in remaining_nodes:
                        r_prereqs = graph.get(r_node, set())
                        unmarked_prereqs = {p for p in r_prereqs if p not in processed_in_ts}
                        print(f"  - {r_node}: Unmarked Prerequisites: {unmarked_prereqs}")
                    return None, None, None
                initial_schedule.append(tuple(ready_nodes))
                ts.done(*ready_nodes)

            processed_nodes = {node for step in initial_schedule for node in step}
            if processed_nodes != all_nodes:
                print("Error during initial sort: Not all nodes processed.")
                print(f"Expected: {all_nodes}")
                print(f"Processed: {processed_nodes}")
                print(f"Missing: {all_nodes - processed_nodes}")
                return None, None, None

            return initial_schedule, node_info, all_nodes

        except (graphlib.CycleError, graphlib.NodeNotFoundError) as e:
            print(f"Error during initial sort: {e}")
            return None, None, None
        except Exception as e:
            print(f"Unexpected error during initial sort: {e}")
            import traceback
            traceback.print_exc()
            return None, None, None


    def create_configuration_schedule_v4(self, dependencies):
        """
        Calculates schedule using post-processing to merge ALL constraints
        to the step where their last prerequisite finishes.
        Formats output as list of {'features': [], 'constraints': []} dicts.
        """
        initial_schedule, node_info, all_nodes = self.get_initial_schedule_and_info(dependencies)

        if initial_schedule is None:
            return None  # Error already printed by helper

        # Build map from item to its original step index
        item_to_initial_step_index = {
            item: i for i, step in enumerate(initial_schedule) for item in step
        }

        if len(item_to_initial_step_index) != len(all_nodes):
            print("Error: Mismatch between nodes in schedule map and all known nodes.")
            print(f"Nodes in map ({len(item_to_initial_step_index)}): {set(item_to_initial_step_index.keys())}")
            print(f"All nodes ({len(all_nodes)}): {all_nodes}")
            print(f"Difference (should be empty): {all_nodes.symmetric_difference(set(item_to_initial_step_index.keys()))}")
            return None

        # Pre-allocate final schedule structure
        final_schedule_lists = [[] for _ in range(len(initial_schedule))]
        processed_items = set()

        # Iterate through the initial schedule to place items
        for i, step in enumerate(initial_schedule):
            for item in step:
                if item in processed_items:
                    continue  # Should not happen with correct logic, but safe check

                info = node_info[item]
                target_step_idx = i  # Default target step

                # --- Modification: Apply logic to ALL constraints ---
                if info['is_constraint']:
                    max_prereq_step_idx = -1
                    has_prerequisites = bool(info['predecessors'])
                    valid_prereqs = True  # Assume valid until proven otherwise

                    if has_prerequisites:
                        for prereq in info['predecessors']:
                            prereq_idx = item_to_initial_step_index.get(prereq)
                            if prereq_idx is None:
                                print(f"Error: Prerequisite '{prereq}' of constraint '{item}' not found in initial schedule map.")
                                valid_prereqs = False
                                break  # Cannot determine target step for this constraint
                            max_prereq_step_idx = max(max_prereq_step_idx, prereq_idx)

                        # Only change target index if prerequisites were validly found
                        if valid_prereqs:
                            # Ensure max_prereq_step_idx is sensible (>=0 if any prereqs)
                            if max_prereq_step_idx >= 0:
                                target_step_idx = max_prereq_step_idx
                            # else: constraint had prereqs listed, but they resulted in index -1? Error state or 0-indexed issue. Stick to original step 'i' maybe? Or error out. Let's stick to 'i' for now if calculation weirdly results in -1.
                            # Better check: If has_prerequisites=True but max_prereq_step_idx remains -1, something is wrong.
                            elif has_prerequisites:
                                print(f"Warning: Constraint '{item}' has prerequisites {info['predecessors']} but max prerequisite step index remained -1. Placing in original step {i}.")
                                target_step_idx = i  # Fallback to original

                    # If constraint has NO prerequisites OR prerequisite lookup failed,
                    # target_step_idx remains 'i' (its original step)

                # Place the item in the determined target step's list
                if 0 <= target_step_idx < len(final_schedule_lists):
                    final_schedule_lists[target_step_idx].append(item)
                    processed_items.add(item)
                else:
                    print(f"Error: Invalid target step index {target_step_idx} calculated for item '{item}' (Original Step: {i}).")
                    return None  # Abort

        # Final check: Ensure all nodes were processed and placed
        if len(processed_items) != len(all_nodes):
            print("Error: Item count mismatch after processing placement.")
            print(f"Expected: {len(all_nodes)}, Processed: {len(processed_items)}")
            unprocessed = all_nodes - processed_items
            print(f"Unprocessed items: {unprocessed}")
            return None

        # --- New Formatting Step ---
        formatted_schedule = []
        for step_list in final_schedule_lists:
            if not step_list:
                continue  # Skip empty steps that might result from moving items

            step_dict = {'features': [], 'constraints': []}
            # Sort items first for consistent feature/constraint list order
            sorted_items = sorted(step_list)
            for item in sorted_items:
                if item.startswith("Constraint_"):
                    step_dict['constraints'].append(item)
                else:
                    step_dict['features'].append(item)

            # Only add the step if it contains any features or constraints after sorting
            if step_dict['features'] or step_dict['constraints']:
                formatted_schedule.append(step_dict)

        return formatted_schedule

    def find_all_affected_features_final(self, dependencies, initial_update_features):
        impact_adj = collections.defaultdict(set)  # Stores: prerequisite_feature -> {set of dependent_features}
        all_mentioned_nodes = set()

        # 1. Build the "impact" adjacency list (P -> D means if P changes, D is affected)
        for key_feature, relations in dependencies.items():
            all_mentioned_nodes.add(key_feature)

            # Rule 1: F: {'Before': [B]} means F happens BEFORE B.
            # F is a prerequisite for B. If F is updated, B is affected.
            # Edge: F -> B.
            if 'Before' in relations:
                for b_dependent in relations['Before']:
                    impact_adj[key_feature].add(b_dependent)
                    all_mentioned_nodes.add(b_dependent)

            # Rule 2: F: {'After': [A]} means F happens AFTER A (i.e., A happens BEFORE F).
            # A is a prerequisite for F. If A is updated, F is affected.
            # Edge: A -> F.
            if 'After' in relations:
                for a_prerequisite in relations['After']:
                    impact_adj[a_prerequisite].add(key_feature)  # a_prerequisite is the source of impact
                    all_mentioned_nodes.add(a_prerequisite)

        # 2. Traverse from initial features to find all affected features
        affected_features = set()
        queue = collections.deque()

        # Initialize queue and affected_features with the initial set
        for feature_to_update in initial_update_features:
            if feature_to_update in all_mentioned_nodes:  # Check if the feature is known
                if feature_to_update not in affected_features:
                    queue.append(feature_to_update)
                    affected_features.add(feature_to_update)
            else:
                print(f"Warning: Initial feature '{feature_to_update}' not found anywhere in dependency graph. Ignoring.")

        # BFS to find all downstream affected features
        while queue:
            current_prerequisite = queue.popleft()  # This feature has been updated

            # Find all features that depend on current_prerequisite
            # impact_adj[current_prerequisite] will be an empty set if nothing depends on it
            if current_prerequisite in impact_adj:
                for dependent_feature in impact_adj[current_prerequisite]:
                    if dependent_feature not in affected_features:
                        affected_features.add(dependent_feature)
                        queue.append(dependent_feature)

        return affected_features

    def find_dependency_islands(self, dependencies):
        adj = collections.defaultdict(set)  # Adjacency list for an undirected graph
        all_nodes = set()

        # 1. Build the adjacency list and gather all nodes
        for feature, relations in dependencies.items():
            all_nodes.add(feature)
            # 'After' means 'feature' must come before items in 'relations['After']'
            # 'Before' means items in 'relations['Before']' must come before 'feature'
            # For connectivity, if A relates to B, they are connected.

            # Typo in problem description 'after:' vs 'After:' in example. Using example's capitalization.
            if 'After' in relations:
                for other_feature in relations['After']:
                    adj[feature].add(other_feature)
                    adj[other_feature].add(feature)
                    all_nodes.add(other_feature)

            if 'Before' in relations:
                for other_feature in relations['Before']:
                    adj[feature].add(other_feature)
                    adj[other_feature].add(feature)
                    all_nodes.add(other_feature)

        # 2. Find connected components (islands) using BFS
        visited = set()
        islands = []

        for node in all_nodes:  # Iterate through all known nodes
            if node not in visited:
                current_island = set()
                q = collections.deque([node])
                visited.add(node)

                while q:
                    current_node = q.popleft()
                    current_island.add(current_node)

                    # adj[current_node] might be empty if a node was only mentioned
                    # but had no explicit entry in the main dependencies dict
                    # or had no 'Before'/'After' relations listed.
                    # defaultdict(set) handles this by returning an empty set.
                    for neighbor in adj[current_node]:
                        if neighbor not in visited:
                            visited.add(neighbor)
                            q.append(neighbor)

                islands.append(current_island)

        return islands
