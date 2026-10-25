"""Graph-only FSM properties and witnesses using the optional NetworkX wheel."""

import argparse
import ast
import hashlib
import json
from pathlib import Path

from ..components.fsm import FSM_COMPONENT, FSMConfiguration, prepare_fsm
from ..errors import ElaborationError


PROPERTY_FIELDS = {
    'reachable': 'reachable_from_initial',
    'all_can_reach': 'all_reachable_states_can_reach',
    'all_paths_reach': 'all_maximal_transition_paths_reach',
}


class GraphAnalysisError(ValueError):
    """Invalid analysis input or missing optional analysis dependency."""


def networkx_module():
    try:
        import networkx
    except ImportError as error:
        raise GraphAnalysisError('Install the optional locked dependency: pip install -r requirements-graph.txt') from error
    return networkx


def induced_graph(graph, states, rank, nx):
    selected = set(states)
    result = nx.DiGraph()
    result.add_nodes_from(sorted(selected, key=rank.__getitem__))
    result.add_edges_from(sorted(((left, right) for left, right in graph.edges
                                 if left in selected and right in selected),
                                key=lambda pair: (rank[pair[0]], rank[pair[1]])))
    return result


def cycle_witness(graph, nx):
    edges = nx.find_cycle(graph, source=next(iter(graph)))
    return [edges[0][0], *[edge[1] for edge in edges]]


def target_analysis(graph, initial, target, initial_paths, components, rank, nx):
    order = lambda nodes: sorted(nodes, key=rank.__getitem__)
    reverse_paths = nx.single_source_shortest_path(graph.reverse(copy=False), target)
    paths = {state: list(reversed(reverse_paths[state])) if state in reverse_paths else None for state in graph}
    bad = [state for state in initial_paths if paths[state] is None]
    bad.sort(key=rank.__getitem__)
    recovery = None
    if bad:
        state = min(bad, key=lambda node: (len(initial_paths[node]), rank[node]))
        recovery = {'state': state, 'prefix': initial_paths[state],
                    'closed_reachable_set': order({state} | nx.descendants(graph, state)),
                    'target_excluded': target}

    avoiding = induced_graph(graph, [state for state in graph if state != target], rank, nx)
    avoiding_paths = nx.single_source_shortest_path(avoiding, initial) if initial != target else {}
    reachable_avoiding = induced_graph(avoiding, avoiding_paths, rank, nx)
    cyclic_regions = []
    witnesses = []
    for component in nx.strongly_connected_components(reachable_avoiding):
        members = order(component)
        if len(members) == 1 and not graph.has_edge(members[0], members[0]):
            continue
        cycle = cycle_witness(induced_graph(graph, members, rank, nx), nx)
        witness = {'kind': 'cycle', 'prefix': avoiding_paths[cycle[0]], 'cycle': cycle,
                   'region': members,
                   'has_exit': any(neighbor not in component for state in members for neighbor in graph.successors(state))}
        cyclic_regions.append(witness)
        witnesses.append(witness)
    cyclic_regions.sort(key=lambda item: tuple(rank[state] for state in item['region']))
    dead_ends = [state for state in avoiding_paths if graph.out_degree(state) == 0]
    dead_ends.sort(key=rank.__getitem__)
    witnesses.extend({'kind': 'terminal', 'prefix': avoiding_paths[state], 'terminal': state} for state in dead_ends)
    counterexample = min(witnesses, key=lambda item: (len(item['prefix']),
                          tuple(rank[state] for state in item['prefix']), item['kind'])) if witnesses else None
    bound = None
    if counterexample is None:
        distances = {target: 0}
        for state in reversed(list(nx.topological_sort(reachable_avoiding))):
            distances[state] = 1 + max(distances[neighbor] for neighbor in graph.successors(state))
        bound = distances[initial]

    return {'target': target, 'reachable_from_initial': initial in reverse_paths,
            'path_from_initial': initial_paths.get(target),
            'paths_to_target': paths,
            'states_without_path_to_target': [state for state in graph if paths[state] is None],
            'reachable_states_without_path_to_target': bad,
            'all_reachable_states_can_reach': not bad,
            'recovery_counterexample': recovery,
            'closed_regions_avoiding_target': [item['id'] for item in components
                                              if item['closed'] and target not in item['states']],
            'reachable_target_avoiding_cycles': cyclic_regions,
            'reachable_non_target_dead_ends': dead_ends,
            'all_maximal_transition_paths_reach': counterexample is None,
            'max_transitions_to_first_target': bound,
            'path_counterexample': counterexample}


def analyze_graph(states, initial, edges, *, targets=(), requirements=()):
    """Analyze declared edges only; no implicit hold, guards or scheduler model.

    Requirements are (kind, target) pairs. The initial state is always queried
    to expose recovery facts. A terminal or closed SCC alone is not an error.
    """
    nx = networkx_module()
    states, edges = list(states), list(edges)
    if not states or any(not isinstance(state, str) or not state for state in states) or len(set(states)) != len(states):
        raise GraphAnalysisError('states must be a nonempty sequence of unique names')
    rank = {state: index for index, state in enumerate(states)}
    if not isinstance(initial, str) or initial not in rank:
        raise GraphAnalysisError('initial state is not declared: ' + str(initial))
    normalized = []
    for edge in edges:
        if (not isinstance(edge, (tuple, list)) or len(edge) != 2
                or any(not isinstance(state, str) or state not in rank for state in edge)):
            raise GraphAnalysisError('edge endpoints must name declared states: ' + str(edge))
        pair = tuple(edge)
        if pair in normalized:
            raise GraphAnalysisError('duplicate edge: ' + str(pair))
        normalized.append(pair)
    requirements = list(requirements)
    if any(not isinstance(item, (tuple, list)) or len(item) != 2 or not isinstance(item[0], str)
           or item[0] not in PROPERTY_FIELDS for item in requirements):
        raise GraphAnalysisError('unknown graph property requirement')
    requested = list(targets) + [target for _, target in requirements] + [initial]
    if any(not isinstance(target, str) or target not in rank for target in requested):
        raise GraphAnalysisError('analysis target is not a declared state')
    graph = nx.DiGraph()
    graph.add_nodes_from(states)
    graph.add_edges_from(sorted(normalized, key=lambda pair: (rank[pair[0]], rank[pair[1]])))
    initial_paths = nx.single_source_shortest_path(graph, initial)
    groups = sorted((sorted(group, key=rank.__getitem__) for group in nx.strongly_connected_components(graph)),
                    key=lambda group: tuple(rank[state] for state in group))
    condensed = nx.condensation(graph, [set(group) for group in groups])
    components = []
    for index, members in enumerate(groups):
        cyclic = len(members) > 1 or graph.has_edge(members[0], members[0])
        entry = min((state for state in members if state in initial_paths),
                    key=lambda state: (len(initial_paths[state]), rank[state]), default=None)
        components.append({'id': index, 'states': members, 'reachable': entry is not None,
                           'cyclic': cyclic, 'closed': condensed.out_degree(index) == 0,
                           'successors': sorted(condensed.successors(index)),
                           'entry_path': initial_paths[entry] if entry is not None else None,
                           'cycle': cycle_witness(induced_graph(graph, members, rank, nx), nx) if cyclic else None})
    queries = {target: target_analysis(graph, initial, target, initial_paths, components, rank, nx)
               for target in states if target in requested}
    properties = []
    for kind, target in requirements:
        query = queries[target]
        passed = query[PROPERTY_FIELDS[kind]]
        if kind == 'reachable':
            witness = ({'path': query['path_from_initial']} if passed else
                       {'closed_reachable_set': list(initial_paths), 'target_excluded': target})
        elif kind == 'all_can_reach':
            witness = {'certificate': 'paths_to_target'} if passed else query['recovery_counterexample']
        else:
            witness = ({'max_transitions_to_first_target': query['max_transitions_to_first_target']}
                       if passed else query['path_counterexample'])
        properties.append({'kind': kind, 'target': target, 'status': 'PASS' if passed else 'FAIL',
                           'evidence': 'GRAPH_PROVEN' if passed else 'GRAPH_COUNTEREXAMPLE', 'witness': witness})
    return {'schema': 'arch-fsm-graph/v1', 'engine': {'name': 'networkx', 'version': nx.__version__},
            'scope': {'model': 'declared directed graph', 'implicit_hold_edges': False,
                      'target_semantics': 'first visit; an initial target is satisfied at zero transitions',
                      'rule_guards': 'NOT_MODELED', 'resource_waits': 'NOT_MODELED',
                      'fairness': 'NOT_ASSUMED', 'hardware_liveness': 'NOT_PROVEN'},
            'states': states, 'initial': initial, 'edges': [list(edge) for edge in graph.edges],
            'reachable': [state for state in states if state in initial_paths],
            'unreachable': [state for state in states if state not in initial_paths],
            'terminal': [state for state in states if graph.out_degree(state) == 0],
            'self_loops': [state for state in states if graph.has_edge(state, state)],
            'paths_from_initial': {state: initial_paths.get(state) for state in states},
            'strongly_connected_components': components,
            'condensation_edges': [list(edge) for edge in sorted(condensed.edges)],
            'targets': queries, 'properties': properties,
            'status': 'FAIL' if any(item['status'] == 'FAIL' for item in properties) else 'PASS'}


def analyze_source(source, *, targets=None, requirements=None):
    """Read local FSM declarations with the existing AST frontend, without exec."""
    source = Path(source)
    original = source.read_bytes()
    tree = ast.parse(original.decode('utf-8'), filename=str(source))
    markers = {item.asname or item.name for node in tree.body if isinstance(node, ast.ImportFrom)
               and node.module in FSM_COMPONENT.import_modules for item in node.names if item.name == 'FSM'}
    if not markers:
        raise GraphAnalysisError('source must explicitly import FSM')
    helpers = {item.asname or item.name: item.name for node in tree.body if isinstance(node, ast.ImportFrom)
               and node.module in FSM_COMPONENT.import_modules for item in node.names
               if item.name in FSM_COMPONENT.helpers}
    try:
        _, context = prepare_fsm(markers, tree.body, helpers=helpers)
    except ElaborationError as error:
        raise GraphAnalysisError(str(error)) from error
    definitions = context['definitions']
    targets, requirements = targets or {}, requirements or {}
    unknown = (targets.keys() | requirements.keys()) - definitions.keys()
    if unknown:
        raise GraphAnalysisError('unknown FSM declaration: ' + ', '.join(sorted(unknown)))
    reports = {}
    for name, config in definitions.items():
        if not isinstance(config, FSMConfiguration):
            raise GraphAnalysisError('composite FSM graph analysis is not implemented; this tool accepts Enum graphs only')
        report = analyze_graph([state for state, _ in config.states], config.initial, config.edges,
                               targets=targets.get(name, ()), requirements=requirements.get(name, ()))
        report['declaration_line'] = next(node.lineno for node in tree.body if isinstance(node, ast.ClassDef) and node.name == name)
        reports[name] = report
    return {'schema': 'arch-fsm-source-analysis/v1', 'source': str(source),
            'source_sha256': hashlib.sha256(original).hexdigest(),
            'status': 'FAIL' if any(report['status'] == 'FAIL' for report in reports.values()) else 'PASS',
            'hardware_generation': 'NOT_RUN', 'machines': reports}


def render_text(report):
    """Concise paths and property outcomes for CLI inspection."""
    lines = [f"FSM graph analysis: {report['status']}", 'Scope: declared edges only; no implicit hold, guards or resource waits.',
             'Target means first visit; an initial target is already satisfied at zero transitions.']
    for name, machine in report['machines'].items():
        lines += ['', f"{name} (line {machine['declaration_line']}, initial={machine['initial']})",
                  '  unreachable: ' + (', '.join(machine['unreachable']) or '(none)'),
                  '  terminal: ' + (', '.join(machine['terminal']) or '(none)')]
        for region in machine['strongly_connected_components']:
            lines.append(f"  SCC {region['id']}: {', '.join(region['states'])}; closed={region['closed']}; reachable={region['reachable']}")
        for target, query in machine['targets'].items():
            lines.append(f"  target {target}: reachable={query['reachable_from_initial']}; all-can-reach={query['all_reachable_states_can_reach']}; all-transition-paths-reach={query['all_maximal_transition_paths_reach']}")
            if query['path_from_initial'] is not None:
                lines.append('    shortest initial path: ' + ' -> '.join(query['path_from_initial']))
            if query['max_transitions_to_first_target'] is not None:
                lines.append('    bound in graph transitions: ' + str(query['max_transitions_to_first_target']))
            recovery = query['recovery_counterexample']
            if recovery:
                lines.append('    cannot recover after: ' + ' -> '.join(recovery['prefix']))
                lines.append('    closed reachable set: ' + ', '.join(recovery['closed_reachable_set']))
            counterexample = query['path_counterexample']
            if counterexample:
                lines.append('    avoiding prefix: ' + ' -> '.join(counterexample['prefix']))
                if counterexample['kind'] == 'cycle':
                    lines.append('    avoiding cycle: ' + ' -> '.join(counterexample['cycle']))
                else:
                    lines.append('    non-target terminal: ' + counterexample['terminal'])
        for prop in machine['properties']:
            lines.append(f"  REQUIRE {prop['kind']}({prop['target']}): {prop['status']}")
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    parser.add_argument('--target', action='append', default=[], metavar='FSM=STATE')
    for kind in PROPERTY_FIELDS:
        parser.add_argument('--require-' + kind.replace('_', '-'), action='append', default=[], metavar='FSM=STATE')
    args = parser.parse_args()
    if args.output.resolve() == args.source.resolve():
        parser.error('analysis output must not overwrite source')
    targets, requirements = {}, {}

    def split(value):
        parts = value.split('=')
        if len(parts) != 2 or not all(part.isidentifier() for part in parts):
            raise GraphAnalysisError('expected FSM=STATE, got: ' + value)
        return parts

    try:
        for value in args.target:
            name, target = split(value)
            targets.setdefault(name, []).append(target)
        for kind in PROPERTY_FIELDS:
            for value in getattr(args, 'require_' + kind):
                name, target = split(value)
                requirements.setdefault(name, []).append((kind, target))
        report = analyze_source(args.source, targets=targets, requirements=requirements)
    except (GraphAnalysisError, OSError, SyntaxError) as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='ascii')
    print(render_text(report), end='')
    return 1 if report['status'] == 'FAIL' else 0
