'''
Procedure-based UCLID5 backend for BehaVerify.
Each BT node becomes a UCLID5 procedure. One tick = one call to the root procedure.
'''
import json
import os
import sys
import copy
import itertools

from behaverify.meta_functions import build_meta_func
from behaverify.check_grammar import validate_model
from behaverify.behaverify_common import (
    create_node_template,
    create_variable_template,
    indent,
    is_local,
    is_array,
    handle_constant_or_reference,
    handle_constant_or_reference_no_type,
    resolve_potential_reference_no_type,
    variable_array_size,
    get_min_max,
    BTreeException,
    get_root_node,
    refine_return_types,
    refine_invalid,
    prune_nodes,
    order_nodes,
    map_node_name_to_number,
    format_node_type,
)


def dsl_to_uclid5(metamodel_file, model_file, output_file, keep_last_stage,
                   do_not_trim, recursion_limit, skip_grammar_check, contracts_file=None):
    '''Convert a .tree DSL file to a UCLID5 model.'''

    # ---- Helper: copy loop references and misc_args ----
    def copy_loop_references(loop_references):
        return {key: loop_references[key] for key in loop_references}

    def create_misc_args(loop_references, node_name, use_stages, overwrite_stage,
                         define_substitutions, specification_writing, specification_warning):
        return {
            'loop_references': loop_references,
            'node_name': node_name,
            'use_stages': use_stages,
            'overwrite_stage': overwrite_stage,
            'define_substitutions': define_substitutions,
            'trace_num': 1,
            'specification_writing': specification_writing,
            'specification_warning': specification_warning,
        }

    def copy_misc_args(misc_args):
        result = create_misc_args(
            copy_loop_references(misc_args['loop_references']),
            misc_args['node_name'], misc_args['use_stages'],
            misc_args['overwrite_stage'], misc_args['define_substitutions'],
            misc_args['specification_writing'], misc_args['specification_warning'])
        if misc_args.get('spec_mode'):
            result['spec_mode'] = True
        return result

    # ---- Loop execution ----
    def execute_loop(function_call, to_call, packaged_args, misc_args):
        new_misc_args = copy_misc_args(misc_args)
        loop_references = new_misc_args['loop_references']
        return_vals = []
        all_domain_values = []
        if function_call.min_val is None:
            for domain_code in function_call.loop_variable_domain:
                domain_func = build_meta_func(domain_code)
                for domain_value in domain_func((constants, loop_references)):
                    resolved = resolve_potential_reference_no_type(
                        domain_value, declared_enumerations, nodes, variables,
                        constants, loop_references)
                    all_domain_values.append(resolved[1])
        else:
            (min_val, max_val) = get_min_max(
                function_call.min_val, function_call.max_val,
                declared_enumerations, nodes, variables, constants, loop_references)
            all_domain_values = range(min_val, max_val + 1)
        if function_call.reverse == 'reverse':
            all_domain_values = reversed(all_domain_values)
        cond_func = build_meta_func(function_call.loop_condition)
        for domain_member in all_domain_values:
            loop_references[function_call.loop_variable] = domain_member
            if cond_func((constants, loop_references))[0]:
                return_vals.extend(to_call(packaged_args, new_misc_args))
            loop_references.pop(function_call.loop_variable)
        return return_vals

    # ---- Expression formatting for UCLID5 ----

    def format_function_if(_, function_call, misc_args):
        cond = format_code(function_call.values[0], misc_args)[0]
        then_val = format_code(function_call.values[1], misc_args)[0]
        else_val = format_code(function_call.values[2], misc_args)[0]
        return ['(if (' + cond + ') then (' + then_val + ') else (' + else_val + '))']

    def format_function_loop(_, function_call, misc_args):
        return execute_loop(function_call, format_code, function_call.values[0], misc_args)

    def format_function_case_loop(_, function_call, misc_args):
        new_misc_args = copy_misc_args(misc_args)
        loop_references = new_misc_args['loop_references']
        case_value_pairs = []
        all_domain_values = []
        if function_call.min_val is None:
            for domain_code in function_call.loop_variable_domain:
                domain_func = build_meta_func(domain_code)
                for domain_value in domain_func((constants, loop_references)):
                    resolved = resolve_potential_reference_no_type(
                        domain_value, declared_enumerations, nodes, variables,
                        constants, loop_references)
                    all_domain_values.append(resolved[1])
        else:
            (min_val, max_val) = get_min_max(
                function_call.min_val, function_call.max_val,
                declared_enumerations, nodes, variables, constants, loop_references)
            all_domain_values = range(min_val, max_val + 1)
        if function_call.reverse == 'reverse':
            all_domain_values = reversed(all_domain_values)
        cond_func = build_meta_func(function_call.loop_condition)
        for domain_member in all_domain_values:
            loop_references[function_call.loop_variable] = domain_member
            if cond_func((constants, loop_references))[0]:
                case_value_pairs.append((
                    format_code(function_call.cond_value, new_misc_args)[0],
                    format_code(function_call.values[0], new_misc_args)))
            loop_references.pop(function_call.loop_variable)
        case_value_pairs[-1] = ('true', format_code(function_call.default_value, misc_args))
        result = case_value_pairs[-1][1][0]
        for i in range(len(case_value_pairs) - 2, -1, -1):
            cond_str = case_value_pairs[i][0]
            val_str = case_value_pairs[i][1][0]
            result = '(if (' + cond_str + ') then (' + val_str + ') else (' + result + '))'
        return [result]

    # Track which helper functions are used so we can emit defines
    used_helper_functions = set()
    HELPER_FUNCTIONS = {'abs', 'min', 'max', 'xor', 'xnor', 'floor', 'count'}

    def format_function_before(function_name, function_call, misc_args):
        if function_name in HELPER_FUNCTIONS:
            used_helper_functions.add(function_name)
        return [
            function_name + '('
            + ', '.join([', '.join(format_code(value, misc_args)) for value in function_call.values])
            + ')'
        ]

    def format_function_recursive_before(function_name, function_call, misc_args):
        if function_name in HELPER_FUNCTIONS:
            used_helper_functions.add(function_name)
        formatted_values = []
        for value in function_call.values:
            formatted_values.extend(format_code(value, misc_args))
        if len(formatted_values) == 1:
            return [formatted_values[0]]
        result = formatted_values[-1]
        for i in range(len(formatted_values) - 2, -1, -1):
            result = function_name + '(' + formatted_values[i] + ', ' + result + ')'
        return [result]

    def format_function_between(function_name, function_call, misc_args):
        if function_name in HELPER_FUNCTIONS:
            used_helper_functions.add(function_name)
        return [
            '('
            + (' ' + function_name + ' ').join(
                [(' ' + function_name + ' ').join(format_code(value, misc_args))
                 for value in function_call.values])
            + ')'
        ]

    def format_function_integer_division(function_name, function_call, misc_args):
        return [
            '('
            + (' ' + function_name + ' ').join(
                [(' ' + function_name + ' ').join(format_code(value, misc_args))
                 for value in function_call.values])
            + ')'
        ]

    def format_function_after(function_name, function_call, misc_args):
        node_func = build_meta_func(function_call.node_name)
        node_name_vals = node_func((constants, misc_args['loop_references']))
        node_ref = node_name_vals[0]
        return ['(' + node_ref + function_name + ')']

    def format_function_before_bounded(function_name, function_call, misc_args):
        print('WARNING: Bounded temporal operator ' + function_name + ' not supported in UCLID5.')
        return [
            function_name + '('
            + ', '.join([', '.join(format_code(value, misc_args)) for value in function_call.values])
            + ')'
        ]

    def format_function_between_bounded(function_name, function_call, misc_args):
        print('WARNING: Bounded temporal operator ' + function_name + ' not supported in UCLID5.')
        formatted_values = []
        for value in function_call.values:
            formatted_values.extend(format_code(value, misc_args))
        return ['(' + (' ' + function_name + ' ').join(formatted_values) + ')']

    def format_function_before_between(function_name, function_call, misc_args):
        formatted_values = []
        for value in function_call.values:
            formatted_values.extend(format_code(value, misc_args))
        return [
            function_name[0] + '['
            + (' ' + function_name[1] + ' ').join(formatted_values)
            + ']'
        ]

    def case_index(var_name, array_size, index_expression):
        if array_size <= 1:
            return var_name + '_index_0'
        result = var_name + '_index_' + str(array_size - 1)
        for i in range(array_size - 2, -1, -1):
            result = ('(if (' + index_expression + ' == ' + str(i) + ') then ('
                      + var_name + '_index_' + str(i)
                      + ') else (' + result + '))')
        return result

    def format_function_index(_, function_call, misc_args):
        new_misc_args = adjust_args(function_call, misc_args)
        var_func = build_meta_func(function_call.to_index)
        variable = resolve_potential_reference_no_type(
            var_func((constants, new_misc_args['loop_references']))[0],
            declared_enumerations, nodes, variables, constants,
            new_misc_args['loop_references'])[1]
        var_name = format_variable(variable, new_misc_args)
        if function_call.constant_index == 'constant_index':
            index_func = build_meta_func(function_call.values[0])
            index = resolve_potential_reference_no_type(
                index_func((constants, new_misc_args['loop_references']))[0],
                declared_enumerations, nodes, variables, constants,
                new_misc_args['loop_references'])[1]
            return [var_name + '_index_' + str(index)]
        index_expression = format_code(function_call.values[0], new_misc_args)[0]
        arr_size = variable_array_size(variable, declared_enumerations, nodes,
                                       variables, constants, misc_args['loop_references'])
        return [case_index(var_name, arr_size, index_expression)]

    def format_function(code, misc_args):
        (function_name, function_to_call) = function_format[code.function_call.function_name]
        return function_to_call(function_name, code.function_call, misc_args)

    # ---- Variable reference (procedure-based: plain names, no staging) ----

    def variable_reference(base_name, _is_local_, node_name):
        # Local variables are procedure-local in UCLID5, so use bare name
        return base_name

    def format_variable(variable_obj, misc_args):
        var_key = variable_reference(variable_obj.name, is_local(variable_obj), misc_args['node_name'])
        # Inline-substitute DEFINE variables with their expression
        if var_key in define_exprs:
            return define_exprs[var_key]
        return format_variable_by_key(var_key, misc_args)

    def format_variable_by_key(var_key, misc_args):
        '''In procedure mode, variables are referenced by plain name.
        In specification mode, handle at-k references via snapshot names.'''
        overwrite_stage = misc_args['overwrite_stage']
        if misc_args.get('spec_mode'):
            # Specification mode: use snapshot variables for at-k
            if overwrite_stage is not None:
                if overwrite_stage == 0:
                    return var_key + '_at_0'
                elif overwrite_stage < 0:
                    return var_key  # at -1 = post-tick = the variable itself
                else:
                    return var_key + '_at_' + str(overwrite_stage)
            return var_key  # default in specs = post-tick
        # In procedure body: just use the variable name
        return var_key

    def adjust_args(code, misc_args):
        new_misc_args = copy_misc_args(misc_args)
        if code.node_name is not None:
            node_name_func = build_meta_func(code.node_name)
            new_misc_args['node_name'] = resolve_potential_reference_no_type(
                node_name_func((constants, new_misc_args['loop_references']))[0],
                declared_enumerations, nodes, variables, constants,
                new_misc_args['loop_references'])[1]
        if code.read_at is not None:
            read_at_func = build_meta_func(code.read_at)
            new_misc_args['overwrite_stage'] = resolve_potential_reference_no_type(
                read_at_func((constants, new_misc_args['loop_references']))[0],
                declared_enumerations, nodes, variables, constants,
                new_misc_args['loop_references'])[1]
        return new_misc_args

    def handle_atom(code, misc_args):
        (atom_class, atom_type, atom) = handle_constant_or_reference(
            code.atom, declared_enumerations, nodes, variables, constants,
            misc_args['loop_references'])
        if atom_class == 'CONSTANT':
            if atom_type == 'BOOLEAN':
                return str(atom).lower()
            return str(atom)
        return format_variable(atom, adjust_args(code, misc_args))

    def format_code(code, misc_args):
        return (
            [handle_atom(code, misc_args)] if code.atom is not None else (
                ['(' + fc + ')' for fc in format_code(code.code_statement, misc_args)]
                if code.code_statement is not None else
                format_function(code, misc_args)
            )
        )

    # ---- Collect at-k references from specifications ----

    def collect_at_refs_from_code(code, refs):
        '''Walk a code AST and collect (variable_name, k) pairs from at-k references.'''
        if code.atom is not None:
            if code.read_at is not None:
                (atom_class, _, atom) = handle_constant_or_reference(
                    code.atom, declared_enumerations, nodes, variables, constants, {})
                if atom_class == 'VARIABLE':
                    read_at_func = build_meta_func(code.read_at)
                    k = resolve_potential_reference_no_type(
                        read_at_func((constants, {}))[0],
                        declared_enumerations, nodes, variables, constants, {})[1]
                    var_name = atom.name
                    refs.add((var_name, k))
            return
        if code.code_statement is not None:
            collect_at_refs_from_code(code.code_statement, refs)
            return
        if code.function_call is not None:
            fc = code.function_call
            if fc.function_name == 'loop':
                # Can't easily resolve loop vars statically; collect from body
                for v in fc.values:
                    collect_at_refs_from_code(v, refs)
            elif fc.function_name == 'case_loop':
                collect_at_refs_from_code(fc.cond_value, refs)
                for v in fc.values:
                    collect_at_refs_from_code(v, refs)
                collect_at_refs_from_code(fc.default_value, refs)
            else:
                for v in fc.values:
                    collect_at_refs_from_code(v, refs)
            if hasattr(fc, 'node_name') and fc.node_name is not None:
                # Node status refs like (success, node_name)
                if fc.function_name in ('active', 'success', 'failure', 'running'):
                    node_func = build_meta_func(fc.node_name)
                    node_ref = node_func((constants, {}))[0]
                    node_status_refs.add(node_ref)

    def collect_all_at_refs(specifications):
        '''Scan all specs to find which (variable, k) pairs are needed for snapshots.'''
        refs = set()
        for spec in specifications:
            collect_at_refs_from_code(spec.code_statement, refs)
        return refs

    # ---- Walk tree (build node hierarchy) ----

    def create_composite(current_node, node_name, node_names, parent_name):
        children = []
        all_nodes = {}
        local_variables = []
        initial_statements = []
        statements = []
        for child in current_node.children:
            new_vals = walk_tree(child, node_name, node_names)
            children.append(new_vals[0])
            node_names = new_vals[1]
            all_nodes.update(new_vals[2])
            local_variables = local_variables + new_vals[3]
            initial_statements = initial_statements + new_vals[4]
            statements = statements + new_vals[5]
        all_nodes[node_name] = create_node_template(
            node_name, parent_name, children,
            'composite', current_node.node_type,
            (('_' + current_node.parallel_policy) if current_node.node_type == 'parallel' else ''),
            current_node.memory,
            True, True, True)
        return (node_name, node_names, all_nodes, local_variables, initial_statements, statements)

    def create_decorator(current_node, node_name, node_names, parent_name, additional_arguments=None):
        children = []
        all_nodes = {}
        local_variables = []
        initial_statements = []
        statements = []
        new_vals = walk_tree(current_node.child, node_name, node_names)
        children.append(new_vals[0])
        node_names = new_vals[1]
        all_nodes.update(new_vals[2])
        local_variables = local_variables + new_vals[3]
        initial_statements = initial_statements + new_vals[4]
        statements = statements + new_vals[5]
        all_nodes[node_name] = create_node_template(
            node_name, parent_name, children,
            'decorator', current_node.node_type, '', '',
            True, True, True, additional_arguments)
        return (node_name, node_names, all_nodes, local_variables, initial_statements, statements)

    def create_X_is_Y(current_node, node_name, node_names, parent_name):
        return create_decorator(current_node, node_name, node_names, parent_name,
                                [current_node.x, current_node.y])

    def create_repeat(current_node, node_name, node_names, parent_name):
        return create_decorator(current_node, node_name, node_names, parent_name,
                                [str(current_node.repeat)])

    def create_one_shot(current_node, node_name, node_names, parent_name):
        return create_decorator(current_node, node_name, node_names, parent_name,
                                ['0' if current_node.one_shot == 'success_only' else '-1',
                                 '0' if current_node.one_shot == 'failure_only' else '1'])

    def create_check(current_node, argument_pairs, node_name, node_names, parent_name):
        return (
            node_name, node_names,
            {node_name: create_node_template(
                node_name, parent_name, [],
                'leaf', current_node.node_type, '', '',
                True, False, True, custom_type=current_node.name)},
            [], [], [(node_name, argument_pairs, 'check', current_node.condition)]
        )

    def create_action(current_node, argument_pairs, node_name, node_names, parent_name):
        return (
            node_name, node_names,
            {node_name: create_node_template(
                node_name, parent_name, [],
                'leaf', current_node.node_type, '', '',
                True, True, True, custom_type=current_node.name)},
            list(map(lambda x: (node_name, x), current_node.local_variables)),
            list(map(lambda x: (node_name, argument_pairs, x), current_node.init_statements)),
            (
                list(map(lambda x: (node_name, argument_pairs, 'statement', x), current_node.pre_update_statements))
                + [(node_name, argument_pairs, 'return', current_node.return_statement)]
                + list(map(lambda x: (node_name, argument_pairs, 'statement', x), current_node.post_update_statements))
            )
        )

    def walk_tree(current_node, parent_name=None, node_names=None):
        if node_names is None:
            node_names = set()
        argument_pairs = None
        while hasattr(current_node, 'sub_root'):
            current_node = current_node.sub_root
        node_name = (current_node.name
                     if hasattr(current_node, 'name') and current_node.name is not None
                     else current_node.leaf.name)
        if hasattr(current_node, 'leaf'):
            all_arguments = []
            for argument in current_node.arguments:
                arg_func = build_meta_func(argument)
                all_arguments.extend(arg_func((constants, {})))
            argument_pairs = {
                current_node.leaf.arguments[index].argument_name: all_arguments[index]
                for index in range(len(current_node.arguments))
            }
            current_node = current_node.leaf
        cur_node_names = {node_name}.union(node_names)
        return (
            create_node[current_node.node_type](current_node, node_name, cur_node_names, parent_name)
            if argument_pairs is None else
            create_node[current_node.node_type](current_node, argument_pairs, node_name, cur_node_names, parent_name)
        )

    # ======================================================================
    # PROCEDURE-BASED UCLID5 CODE GENERATION
    # ======================================================================

    def get_var_type(variable):
        '''Determine UCLID5 type for a model variable object.'''
        if variable.model_as == 'NEURAL':
            if variable.neural_mode == 'classification':
                return 'enum_t'
            return 'integer'
        if hasattr(variable, 'domain') and variable.domain is not None:
            if isinstance(variable.domain, str):
                if variable.domain == 'BOOLEAN':
                    return 'boolean'
                if variable.domain == 'ENUM':
                    return 'enum_t'
                return 'integer'
            if variable.domain.boolean is not None:
                return 'boolean'
            if variable.domain.true_int is not None:
                return 'integer'
            if variable.domain.true_real is not None:
                return 'integer'  # approximate
            if variable.domain.min_val is not None:
                return 'integer'
            if variable.domain.domain_codes is not None and len(variable.domain.domain_codes) > 0:
                # Check if enum
                vals = []
                for dc in variable.domain.domain_codes:
                    func = build_meta_func(dc)
                    vals.extend(func((constants, {})))
                if all(isinstance(v, str) and v in declared_enumerations for v in vals):
                    return 'enum_t'
                return 'integer'
        return 'integer'

    def get_neural_enum_values(variable):
        '''For a NEURAL classification variable, return its valid enum values.'''
        if variable.neural_mode != 'classification':
            return []
        vals = []
        for dc in variable.domain_codes:
            func = build_meta_func(dc)
            vals.extend(func((constants, {})))
        return [str(v) for v in vals]

    def get_enum_domain_values(variable):
        '''For a variable with enum domain_codes, return its valid values.'''
        if not hasattr(variable, 'domain') or variable.domain is None:
            return []
        if isinstance(variable.domain, str):
            return []
        if variable.domain.domain_codes is None or len(variable.domain.domain_codes) == 0:
            return []
        vals = []
        for dc in variable.domain.domain_codes:
            func = build_meta_func(dc)
            vals.extend(func((constants, {})))
        return [str(v) for v in vals]

    def try_range_assume(var_name, vals):
        '''If vals are consecutive integers, return a concise range assume string.
        Otherwise return an enumeration assume string.'''
        try:
            int_vals = sorted([int(v) for v in vals])
        except (ValueError, TypeError):
            # Not all integers; use enumeration
            return var_name + ' == ' + (' || ' + var_name + ' == ').join(vals)
        if len(int_vals) >= 3 and int_vals == list(range(int_vals[0], int_vals[-1] + 1)):
            return var_name + ' >= ' + str(int_vals[0]) + ' && ' + var_name + ' <= ' + str(int_vals[-1])
        return ' || '.join([var_name + ' == ' + v for v in vals])

    def get_var_init_values(variable):
        '''Get the list of initial values for a variable. Returns (is_nondet, values_list).'''
        if not hasattr(variable, 'assign') or variable.assign is None:
            return (False, ['0'])
        assign = variable.assign
        # Collect all results (default + case results)
        all_case_results = []
        for cr in assign.case_results:
            cond = format_code(cr.condition, create_misc_args({}, None, False, None, None, False, False))[0]
            vals = []
            for v in cr.values:
                vals.extend(format_code(v, create_misc_args({}, None, False, None, None, False, False)))
            all_case_results.append((cond, vals))
        default_vals = []
        for v in assign.default_result.values:
            default_vals.extend(format_code(v, create_misc_args({}, None, False, None, None, False, False)))
        all_case_results.append(('true', default_vals))

        # Check if any result is non-deterministic
        has_cases = len(assign.case_results) > 0
        has_nondet = any(len(vals) > 1 for (_, vals) in all_case_results)

        if not has_cases and not has_nondet:
            return (False, default_vals)
        if not has_cases and has_nondet:
            return (True, default_vals)
        # Has cases: build if-then-else for deterministic, or havoc for nondet
        if has_nondet:
            # Collect all possible values across all branches
            all_vals = set()
            for (_, vals) in all_case_results:
                all_vals.update(vals)
            return (True, sorted(all_vals))
        # Deterministic with cases: build if-then-else
        result = all_case_results[-1][1][0]
        for i in range(len(all_case_results) - 2, -1, -1):
            cond = all_case_results[i][0]
            val = all_case_results[i][1][0]
            result = '(if (' + cond + ') then (' + val + ') else (' + result + '))'
        return (False, [result])

    def collect_action_write_vars(node_name, statements_for_node):
        '''Collect variable names written by an action node, in order.'''
        writes = []
        for (nn, _, stmt_type, stmt) in statements_for_node:
            if nn != node_name:
                continue
            if stmt_type == 'statement':
                if stmt.variable_statement is not None:
                    vs = stmt.variable_statement
                    var_obj = vs.variable if hasattr(vs, 'variable') else vs
                    writes.append(var_obj.name)
                elif stmt.write_statement is not None:
                    for var_update in stmt.write_statement.update:
                        var_obj = var_update.variable if hasattr(var_update, 'variable') else var_update
                        writes.append(var_obj.name)
        return writes

    def build_write_counter_map(ordered_node_list, all_statements):
        '''Build a global write counter across the tick: action writes then environment updates.
        Populates snapshot_insert_points for action nodes and env_snapshot_insert_points
        for environment update writes.'''
        var_write_count = {}  # var_name -> current global count

        # Walk action nodes in tree execution order
        for node in ordered_node_list:
            nn = node['name']
            if node['category'] != 'leaf' or node['type'] not in ('action',):
                continue
            for (snn, _, stmt_type, stmt) in all_statements:
                if snn != nn or stmt_type != 'statement':
                    continue
                if stmt.variable_statement is not None:
                    vs = stmt.variable_statement
                    var_obj = vs.variable if hasattr(vs, 'variable') else vs
                    vname = var_obj.name
                    if vname not in var_write_count:
                        var_write_count[vname] = 0
                    var_write_count[vname] += 1
                    write_idx = var_write_count[vname]
                    if (vname, write_idx) in needed_snapshots:
                        snapshot_insert_points.setdefault(nn, []).append(
                            (vname, write_idx))

        # Walk environment updates (happen after tree traversal in the tick)
        if hasattr(model, 'update') and model.update:
            for stmt in model.update:
                if not stmt.instant:
                    var_obj = stmt.variable if hasattr(stmt, 'variable') else stmt
                    vname = var_obj.name
                    if vname not in var_write_count:
                        var_write_count[vname] = 0
                    var_write_count[vname] += 1
                    write_idx = var_write_count[vname]
                    if (vname, write_idx) in needed_snapshots:
                        env_snapshot_insert_points.setdefault(vname, []).append(
                            (vname, write_idx))

        return var_write_count

    # ---- Compute modifies sets for procedures ----

    def compute_modifies(ordered_node_list, all_statements):
        '''Compute which module-level variables each procedure modifies (transitively).
        Returns dict: node_name -> set of variable names.'''
        modifies = {}

        for node in reversed(ordered_node_list):  # bottom-up (leaves first)
            nn = node['name']
            mods = set()

            if node['category'] == 'leaf' and node['type'] in ('action',):
                # Collect direct writes (skip local vars — they are procedure-local)
                for (snn, _, stmt_type, stmt) in all_statements:
                    if snn != nn or stmt_type != 'statement':
                        continue
                    if stmt.variable_statement is not None:
                        vs = stmt.variable_statement
                        var_obj = vs.variable if hasattr(vs, 'variable') else vs
                        if is_local(var_obj):
                            continue
                        vname = variable_reference(var_obj.name, False, nn)
                        mods.add(vname)
                        # Snapshot vars
                        base_name = var_obj.name
                        for (sv, sk) in needed_snapshots:
                            if sv == base_name and sk > 0:
                                mods.add(sv + '_at_' + str(sk))
                    elif stmt.write_statement is not None:
                        for var_update in stmt.write_statement.update:
                            var_obj = var_update.variable if hasattr(var_update, 'variable') else var_update
                            if var_update.instant:
                                mods.add(var_obj.name)
                            else:
                                mods.add('delayed__' + var_obj.name)
                                mods.add('delayed__' + var_obj.name + '__pending')

            elif node['category'] in ('composite', 'decorator'):
                # Union of children's modifies
                for child_name in node.get('children', []):
                    if child_name in modifies:
                        mods.update(modifies[child_name])

            # Decorator-specific state
            if node['type'] == 'repeat':
                mods.add('repeat_count__' + nn)
            elif node['type'] == 'one_shot':
                mods.add('one_shot_val__' + nn)

            modifies[nn] = mods

        return modifies

    # ---- Generate procedure for a node ----

    # Map node name -> procedure name prefix based on node type
    proc_names = {}  # populated in write_uclid5 after nodes are ordered

    # Shared procedure support:
    # Each leaf definition (check/action/env_check) produces exactly one procedure.
    # parameterized_defs: def_name -> [(arg_name, arg_type), ...] — formal params (empty if none)
    # node_def_name: instance_name -> def_name (maps every instance to its definition)
    # node_arg_values: instance_name -> {arg_name: actual_value, ...} (actual arg values per instance)
    parameterized_defs = {}
    node_arg_values = {}
    node_def_name = {}

    def get_proc_name(node_name):
        '''Get the full procedure name for a node.'''
        # If this node is an instance of a parameterized def, use the def's procedure name
        if node_name in node_def_name:
            def_name = node_def_name[node_name]
            return proc_names.get(def_name, 'proc_' + def_name)
        return proc_names.get(node_name, 'proc_' + node_name)

    def get_proc_call(node_name):
        '''Get the full procedure call expression including arguments.'''
        pname = get_proc_name(node_name)
        if node_name in node_arg_values and node_arg_values[node_name]:
            def_name = node_def_name[node_name]
            arg_decls = parameterized_defs[def_name]
            actuals = []
            for (aname, _) in arg_decls:
                actuals.append(str(node_arg_values[node_name][aname]))
            return pname + '(' + ', '.join(actuals) + ')'
        return pname + '()'

    # Indentation constants for generated procedures (match tick procedure style)
    PI = '  '        # procedure-level indent (declarations, braces)
    BI = '    '      # body indent level 1
    BI2 = '        '  # body indent level 2
    BI3 = '            '  # body indent level 3

    def uclid5_arg_type(arg_type):
        '''Map DSL argument type to UCLID5 type.'''
        if arg_type == 'ENUM':
            return 'enum_t'
        if arg_type == 'INT':
            return 'integer'
        if arg_type == 'BOOLEAN':
            return 'boolean'
        if arg_type == 'REAL':
            return 'real'
        return 'integer'

    def proc_header(nn, mods, comment=None, formal_params=None):
        '''Generate procedure header with modifies clause and optional formal parameters.'''
        pname = get_proc_name(nn)
        lines = []
        if comment:
            lines.append(PI + '// ' + comment)
        if formal_params:
            param_str = ', '.join(aname + ' : ' + uclid5_arg_type(atype) for (aname, atype) in formal_params)
            lines.append(PI + 'procedure ' + pname + '(' + param_str + ')')
        else:
            lines.append(PI + 'procedure ' + pname + '()')
        lines.append(BI + 'returns (s__' + nn + ' : status_t)')
        if mods:
            lines.append(BI + 'modifies ' + ', '.join(sorted(mods)) + ';')
        lines.append(PI + '{')
        return lines

    def generate_leaf_procedure(node, formal_params=None):
        '''Generate a leaf node (check or action) procedure.'''
        nn = node['name']
        mods = node_modifies.get(nn, set())
        node_type = node.get('type', 'leaf')
        if node_type in ('check', 'environment_check'):
            comment = 'Check node: tests a condition, returns success or failure.'
        else:
            comment = 'Action node: updates state variables.'
        lines = proc_header(nn, mods, comment, formal_params=formal_params)

        # Emit local variable declarations (procedure-local, fresh each invocation)
        def_name = node.get('custom_type', nn)
        if def_name in local_vars_by_def:
            for (lv_name, lv_type) in local_vars_by_def[def_name]:
                lines.append(BI + 'var ' + lv_name + ' : ' + lv_type + ';')

        if 'proc_statements' in node:
            for stmt_line in node['proc_statements']:
                lines.append(BI + stmt_line)
        else:
            lines.append(BI + 's__' + nn + ' = success;')

        lines.append(PI + '}')
        return lines

    def _generate_composite_body(node, short_circuit_on):
        '''Generate body for sequence (short_circuit_on='success') or selector (short_circuit_on='failure').'''
        nn = node['name']
        children = node['children']
        mods = node_modifies.get(nn, set())
        ntype = 'Sequence' if short_circuit_on == 'success' else 'Selector'
        comment = ntype + ' node: children=[' + ', '.join(children) + '].'
        lines = proc_header(nn, mods, comment)

        default_status = 'success' if short_circuit_on == 'success' else 'failure'
        if not children:
            lines.append(BI + 's__' + nn + ' = ' + default_status + ';')
            lines.append(PI + '}')
            return lines

        lines.append(BI + 'var cs__ : status_t;')
        nest = 0  # extra nesting level beyond BI
        for i, child_name in enumerate(children):
            pad = BI + '    ' * nest
            lines.append(pad + 'call (cs__) = ' + get_proc_call(child_name) + ';')
            if i == len(children) - 1:
                lines.append(pad + 's__' + nn + ' = cs__;')
            else:
                lines.append(pad + 'if (cs__ != ' + short_circuit_on + ') {')
                lines.append(pad + '    ' + 's__' + nn + ' = cs__;')
                lines.append(pad + '} else {')
                nest += 1
        # Close the else braces
        for i in range(len(children) - 1):
            nest -= 1
            pad = BI + '    ' * nest
            lines.append(pad + '}')
        lines.append(PI + '}')
        return lines

    def generate_sequence_procedure(node):
        return _generate_composite_body(node, 'success')

    def generate_selector_procedure(node):
        return _generate_composite_body(node, 'failure')

    def generate_parallel_procedure(node):
        '''Generate a parallel composite procedure.'''
        nn = node['name']
        children = node['children']
        policy = node['policy']
        mods = node_modifies.get(nn, set())
        comment = 'Parallel node (policy=' + str(policy) + '): children=[' + ', '.join(children) + '].'
        lines = proc_header(nn, mods, comment)

        if not children:
            lines.append(BI + 's__' + nn + ' = running;')
            lines.append(PI + '}')
            return lines

        for child_name in children:
            lines.append(BI + 'var cs__' + child_name + ' : status_t;')
        for child_name in children:
            lines.append(BI + 'call (cs__' + child_name + ') = ' + get_proc_call(child_name) + ';')

        if policy == '_and' or policy == '':
            fail_cond = ' || '.join(['cs__' + c + ' == failure' for c in children])
            run_cond = ' || '.join(['cs__' + c + ' == running' for c in children])
            lines.append(BI + 'if (' + fail_cond + ') {')
            lines.append(BI2 + 's__' + nn + ' = failure;')
            lines.append(BI + '} else {')
            lines.append(BI2 + 'if (' + run_cond + ') {')
            lines.append(BI3 + 's__' + nn + ' = running;')
            lines.append(BI2 + '} else {')
            lines.append(BI3 + 's__' + nn + ' = success;')
            lines.append(BI2 + '}')
            lines.append(BI + '}')
        else:
            succ_cond = ' || '.join(['cs__' + c + ' == success' for c in children])
            run_cond = ' || '.join(['cs__' + c + ' == running' for c in children])
            lines.append(BI + 'if (' + succ_cond + ') {')
            lines.append(BI2 + 's__' + nn + ' = success;')
            lines.append(BI + '} else {')
            lines.append(BI2 + 'if (' + run_cond + ') {')
            lines.append(BI3 + 's__' + nn + ' = running;')
            lines.append(BI2 + '} else {')
            lines.append(BI3 + 's__' + nn + ' = failure;')
            lines.append(BI2 + '}')
            lines.append(BI + '}')

        lines.append(PI + '}')
        return lines

    def generate_inverter_procedure(node):
        nn = node['name']
        child_name = node['children'][0]
        mods = node_modifies.get(nn, set())
        lines = proc_header(nn, mods, 'Inverter decorator: swaps success <-> failure.')
        lines.append(BI + 'var cs__ : status_t;')
        lines.append(BI + 'call (cs__) = ' + get_proc_call(child_name) + ';')
        lines.append(BI + 'if (cs__ == success) {')
        lines.append(BI2 + 's__' + nn + ' = failure;')
        lines.append(BI + '} else {')
        lines.append(BI2 + 'if (cs__ == failure) {')
        lines.append(BI3 + 's__' + nn + ' = success;')
        lines.append(BI2 + '} else {')
        lines.append(BI3 + 's__' + nn + ' = cs__;')
        lines.append(BI2 + '}')
        lines.append(BI + '}')
        lines.append(PI + '}')
        return lines

    def generate_x_is_y_procedure(node):
        nn = node['name']
        child_name = node['children'][0]
        args = node['additional_arguments']
        x_status = args[0]
        y_status = args[1]
        mods = node_modifies.get(nn, set())
        lines = proc_header(nn, mods, 'X_is_Y decorator: maps ' + x_status + ' -> ' + y_status + '.')
        lines.append(BI + 'var cs__ : status_t;')
        lines.append(BI + 'call (cs__) = ' + get_proc_call(child_name) + ';')
        lines.append(BI + 'if (cs__ == ' + x_status + ') {')
        lines.append(BI2 + 's__' + nn + ' = ' + y_status + ';')
        lines.append(BI + '} else {')
        lines.append(BI2 + 's__' + nn + ' = cs__;')
        lines.append(BI + '}')
        lines.append(PI + '}')
        return lines

    def generate_repeat_procedure(node):
        '''Generate a repeat decorator procedure.'''
        nn = node['name']
        child_name = node['children'][0]
        max_repeat = node['additional_arguments'][0]
        rc = 'repeat_count__' + nn
        mods = node_modifies.get(nn, set())
        lines = proc_header(nn, mods, 'Repeat decorator: repeats child up to ' + max_repeat + ' times on success.')
        lines.append(BI + 'var cs__ : status_t;')
        lines.append(BI + 'call (cs__) = ' + get_proc_call(child_name) + ';')
        lines.append(BI + 'if (cs__ == success) {')
        lines.append(BI2 + rc + ' = ' + rc + ' - 1;')
        lines.append(BI2 + 'if (' + rc + ' == 0) {')
        lines.append(BI3 + rc + ' = ' + max_repeat + ';')
        lines.append(BI3 + 's__' + nn + ' = success;')
        lines.append(BI2 + '} else {')
        lines.append(BI3 + 's__' + nn + ' = running;')
        lines.append(BI2 + '}')
        lines.append(BI + '} else {')
        lines.append(BI2 + 'if (cs__ == failure) {')
        lines.append(BI3 + rc + ' = ' + max_repeat + ';')
        lines.append(BI3 + 's__' + nn + ' = failure;')
        lines.append(BI2 + '} else {')
        lines.append(BI3 + 's__' + nn + ' = cs__;')
        lines.append(BI2 + '}')
        lines.append(BI + '}')
        lines.append(PI + '}')
        return lines

    def generate_one_shot_procedure(node):
        '''Generate a one_shot decorator procedure.'''
        nn = node['name']
        child_name = node['children'][0]
        args = node['additional_arguments']
        min_val = int(args[0])
        max_val = int(args[1])
        osv = 'one_shot_val__' + nn
        mods = node_modifies.get(nn, set())
        mode = 'success_only' if min_val == 0 else 'success_failure'
        lines = proc_header(nn, mods, 'One_shot decorator (' + mode + '): latches after target status.')
        lines.append(BI + 'if (' + osv + ' == 1) {')
        lines.append(BI2 + 's__' + nn + ' = success;')
        if min_val < 0:
            lines.append(BI + '} else { if (' + osv + ' == -1) {')
            lines.append(BI2 + 's__' + nn + ' = failure;')
            lines.append(BI + '} else {')
        else:
            lines.append(BI + '} else {')
        lines.append(BI2 + 'var cs__ : status_t;')
        lines.append(BI2 + 'call (cs__) = ' + get_proc_call(child_name) + ';')
        if max_val >= 1:
            lines.append(BI2 + 'if (cs__ == success) {')
            lines.append(BI3 + osv + ' = 1;')
            lines.append(BI2 + '}')
        if min_val <= -1:
            lines.append(BI2 + 'if (cs__ == failure) {')
            lines.append(BI3 + osv + ' = -1;')
            lines.append(BI2 + '}')
        lines.append(BI2 + 's__' + nn + ' = cs__;')
        if min_val < 0:
            lines.append(BI + '} }')
        else:
            lines.append(BI + '}')
        lines.append(PI + '}')
        return lines

    def generate_node_procedure(node, formal_params=None):
        '''Dispatch to the appropriate procedure generator.'''
        if node['category'] == 'leaf':
            return generate_leaf_procedure(node, formal_params=formal_params)
        elif node['category'] == 'composite':
            if node['type'] == 'sequence':
                return generate_sequence_procedure(node)
            elif node['type'] == 'selector':
                return generate_selector_procedure(node)
            elif node['type'] == 'parallel':
                return generate_parallel_procedure(node)
        elif node['category'] == 'decorator':
            if node['type'] == 'inverter':
                return generate_inverter_procedure(node)
            elif node['type'] == 'X_is_Y':
                return generate_x_is_y_procedure(node)
            elif node['type'] == 'repeat':
                return generate_repeat_procedure(node)
            elif node['type'] == 'one_shot':
                return generate_one_shot_procedure(node)
            else:
                # Default: pass through child status
                nn = node['name']
                child_name = node['children'][0]
                mods = node_modifies.get(nn, set())
                lines = proc_header(nn, mods, 'Decorator (pass-through).')
                lines.append(BI + 'var cs__ : status_t;')
                lines.append(BI + 'call (cs__) = ' + get_proc_call(child_name) + ';')
                lines.append(BI + 's__' + nn + ' = cs__;')
                lines.append(PI + '}')
                return lines
        return ['  // Unknown node type: ' + node['name']]

    # ---- Process action statements into procedure body lines ----

    def process_action_statements(node_name, all_statements):
        '''Convert action statements into UCLID5 procedure body lines.'''
        lines = []
        # Use the pre-computed snapshot insert points (from build_write_counter_map)
        pending_snapshots = list(snapshot_insert_points.get(node_name, []))
        snap_idx = 0  # index into pending_snapshots

        for (snn, arg_pairs, stmt_type, stmt) in all_statements:
            if snn != node_name:
                continue

            # Temporarily add argument constants
            for aname in arg_pairs:
                if arg_pairs[aname] in variables:
                    variables[aname] = variables[arg_pairs[aname]]
                else:
                    constants[aname] = arg_pairs[aname]

            misc = create_misc_args({}, node_name, False, None, None, False, False)

            if stmt_type == 'check':
                pass
            elif stmt_type == 'return':
                ret_stmt = stmt
                statuses = {result.status
                            for result in itertools.chain([ret_stmt.default_result], ret_stmt.case_results)}
                if len(ret_stmt.case_results) == 0 or len(statuses) == 1:
                    lines.append('s__' + node_name + ' = ' + ret_stmt.default_result.status + ';')
                else:
                    for case_result in ret_stmt.case_results:
                        cond = format_code(case_result.condition, misc)[0]
                        lines.append('if (' + cond + ') { s__' + node_name + ' = ' + case_result.status + '; }')
                        lines.append('else {')
                    lines.append('s__' + node_name + ' = ' + ret_stmt.default_result.status + ';')
                    for _ in ret_stmt.case_results:
                        lines.append('}')
            elif stmt_type == 'statement':
                if stmt.variable_statement is not None:
                    vs = stmt.variable_statement
                    var_obj = vs.variable if hasattr(vs, 'variable') else vs
                    var_name = variable_reference(var_obj.name, is_local(var_obj), node_name)
                    assign = vs.assign
                    assign_lines = format_assign_as_ite(assign, misc, var_name)
                    lines.extend(assign_lines)
                    # Insert snapshot assignment if this write matches a needed snapshot
                    if snap_idx < len(pending_snapshots):
                        (snap_vname, snap_k) = pending_snapshots[snap_idx]
                        if snap_vname == var_obj.name:
                            lines.append(snap_vname + '_at_' + str(snap_k) + ' = ' + var_name + ';')
                            snap_idx += 1
                elif stmt.write_statement is not None:
                    ws = stmt.write_statement
                    for var_update in ws.update:
                        var_obj = var_update.variable if hasattr(var_update, 'variable') else var_update
                        var_name = var_obj.name
                        if var_update.instant:
                            assign_lines = format_assign_as_ite(var_update.assign, misc, var_name)
                            lines.extend(assign_lines)
                        else:
                            # Delayed: save for post-tick application
                            delayed_var_name = 'delayed__' + var_name
                            assign_lines = format_assign_as_ite(var_update.assign, misc, delayed_var_name)
                            lines.extend(assign_lines)
                            lines.append('delayed__' + var_name + '__pending = true;')
                            delayed_env_writes.add(var_name)

            # Clean up argument constants
            for aname in arg_pairs:
                if arg_pairs[aname] in variables:
                    if aname in variables and variables[aname] == variables[arg_pairs[aname]]:
                        variables.pop(aname)
                else:
                    constants.pop(aname)

        return lines

    def format_assign_as_ite(assign, misc, var_name):
        '''Format an assign block as if-then-else assignment lines.'''
        lines = []
        case_results = assign.case_results
        default_result = assign.default_result

        # Format default value(s)
        default_vals = []
        for v in default_result.values:
            default_vals.extend(format_code(v, misc))

        if len(case_results) == 0:
            # Simple assignment
            if len(default_vals) == 1:
                lines.append(var_name + ' = ' + default_vals[0] + ';')
            else:
                # Non-deterministic
                lines.append('havoc ' + var_name + ';')
                lines.append('assume (' + try_range_assume(var_name, default_vals) + ');')
        else:
            # Case-based assignment
            for cr in case_results:
                cond = format_code(cr.condition, misc)[0]
                vals = []
                for v in cr.values:
                    vals.extend(format_code(v, misc))
                lines.append('if (' + cond + ') {')
                if len(vals) == 1:
                    lines.append('  ' + var_name + ' = ' + vals[0] + ';')
                else:
                    lines.append('  havoc ' + var_name + ';')
                    lines.append('  assume (' + try_range_assume(var_name, vals) + ');')
                lines.append('} else {')
            # Default
            if len(default_vals) == 1:
                lines.append('  ' + var_name + ' = ' + default_vals[0] + ';')
            else:
                lines.append('  havoc ' + var_name + ';')
                lines.append('  assume (' + try_range_assume(var_name, default_vals) + ');')
            for _ in case_results:
                lines.append('}')
        return lines

    # ---- Process check conditions ----

    def process_check_conditions(all_statements):
        '''Format check node conditions once per definition, store on the def node.'''
        defs_formatted = set()
        for (node_name, arg_pairs, stmt_type, stmt) in all_statements:
            if stmt_type != 'check':
                continue
            def_name = nodes[node_name].get('custom_type', None)
            if not def_name or def_name in defs_formatted:
                continue
            defs_formatted.add(def_name)

            # Temporarily add argument constants for formatting
            for aname in arg_pairs:
                if arg_pairs[aname] in variables:
                    variables[aname] = variables[arg_pairs[aname]]
                else:
                    constants[aname] = arg_pairs[aname]

            misc = create_misc_args({}, node_name, False, None, None, False, False)
            formatted = format_code(stmt, misc)[0]

            for aname in arg_pairs:
                if arg_pairs[aname] in variables:
                    if aname in variables:
                        variables.pop(aname)
                else:
                    constants.pop(aname)

            # Create synthetic def node and store proc_statements
            if def_name not in nodes:
                nodes[def_name] = dict(nodes[node_name])
                nodes[def_name]['name'] = def_name
            param_formatted = formatted
            for aname in arg_pairs:
                actual_val = str(arg_pairs[aname])
                param_formatted = param_formatted.replace(actual_val, aname)
            nodes[def_name]['proc_statements'] = [
                's__' + def_name + ' = if (' + param_formatted + ') then success else failure;',
            ]

    # ---- Handle specifications ----

    def handle_specifications(specifications):
        result = []
        for spec in specifications:
            spec_type = spec.spec_type
            misc = create_misc_args({}, None, False, None, None, False, False)
            misc['spec_mode'] = True
            formatted = format_code(spec.code_statement, misc)[0]
            if spec_type == 'INVARSPEC':
                result.append(('invariant', formatted))
            elif spec_type == 'LTLSPEC':
                result.append(('ltl', formatted))
            elif spec_type == 'CTLSPEC':
                print('WARNING: CTL specifications not supported in UCLID5. Skipping: ' + formatted)
        return result

    # ---- Load NN contracts ----

    def load_contracts(contracts_file):
        if contracts_file is None:
            return {}
        try:
            with open(contracts_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            print('WARNING: Failed to load contracts file: ' + str(e))
            return {}

    # ---- Assemble and write UCLID5 ----

    def write_uclid5(output_file):
        root_node_name = get_root_node(nodes)
        refine_return_types(nodes, root_node_name)
        refine_invalid(nodes, root_node_name)
        if not do_not_trim:
            prune_nodes(nodes)
        ordered_node_names = order_nodes(root_node_name, nodes)
        ordered_node_list = [nodes[name] for name in ordered_node_names if name in nodes]

        # Build procedure name mapping: node_name -> descriptive procedure name
        type_prefix = {
            'sequence': 'sequence', 'selector': 'selector', 'parallel': 'parallel',
            'check': 'check', 'environment_check': 'env_check', 'action': 'action',
            'inverter': 'inverter', 'X_is_Y': 'x_is_y', 'repeat': 'repeat',
            'one_shot': 'one_shot',
        }
        for node in ordered_node_list:
            nn = node['name']
            prefix = type_prefix.get(node['type'], node['type'])
            proc_names[nn] = prefix + '_' + nn

        # Build inline expressions for DEFINE variables (substituted at every reference)
        nonlocal define_exprs
        misc_def = create_misc_args({}, None, False, None, None, False, False)
        for variable in model.variables:
            if variable.model_as != 'DEFINE':
                continue
            if hasattr(variable, 'assign') and variable.assign is not None:
                vals = []
                for v in variable.assign.default_result.values:
                    vals.extend(format_code(v, misc_def))
                if len(variable.assign.case_results) > 0:
                    result = vals[0] if vals else '0'
                    cases = []
                    for cr in variable.assign.case_results:
                        cond = format_code(cr.condition, misc_def)[0]
                        cr_vals = []
                        for cv in cr.values:
                            cr_vals.extend(format_code(cv, misc_def))
                        cases.append((cond, cr_vals[0] if cr_vals else '0'))
                    cases.append(('true', result))
                    expr = cases[-1][1]
                    for i in range(len(cases) - 2, -1, -1):
                        expr = '(if (' + cases[i][0] + ') then (' + cases[i][1] + ') else (' + expr + '))'
                    define_exprs[variable.name] = expr
                else:
                    define_exprs[variable.name] = vals[0] if vals else '0'

        # Register every leaf definition — each produces exactly one procedure.
        for check_def in model.check_nodes:
            args = [(a.argument_name, a.argument_type) for a in check_def.arguments] if check_def.arguments else []
            parameterized_defs[check_def.name] = args
            proc_names[check_def.name] = 'check_' + check_def.name
        for env_check_def in model.environment_checks:
            args = [(a.argument_name, a.argument_type) for a in env_check_def.arguments] if env_check_def.arguments else []
            parameterized_defs[env_check_def.name] = args
            proc_names[env_check_def.name] = 'env_check_' + env_check_def.name
        for action_def in model.action_nodes:
            args = [(a.argument_name, a.argument_type) for a in action_def.arguments] if action_def.arguments else []
            parameterized_defs[action_def.name] = args
            proc_names[action_def.name] = 'action_' + action_def.name

        # Build local_vars_by_def for action-local variables
        nonlocal local_vars_by_def
        local_vars_by_def = {}
        for action_def in model.action_nodes:
            if action_def.local_variables:
                local_vars_by_def[action_def.name] = [
                    (lv.name, get_var_type(lv)) for lv in action_def.local_variables]

        # Map every leaf instance to its definition and argument values
        for (snn, arg_pairs, stmt_type, stmt) in all_statements:
            if snn in nodes:
                def_name = nodes[snn].get('custom_type', None)
                if def_name and def_name in parameterized_defs:
                    node_def_name[snn] = def_name
                    node_arg_values[snn] = dict(arg_pairs) if arg_pairs else {}

        # Process check conditions (once per definition)
        process_check_conditions(all_statements)
        build_write_counter_map(ordered_node_list, all_statements)

        # Process action statements (once per definition)
        for action_def in model.action_nodes:
            def_name = action_def.name
            first_instance = None
            for node in ordered_node_list:
                if node.get('custom_type', None) == def_name:
                    first_instance = node['name']
                    break
            if first_instance is None:
                continue
            if def_name not in nodes:
                nodes[def_name] = dict(nodes[first_instance])
                nodes[def_name]['name'] = def_name
            raw_stmts = process_action_statements(first_instance, all_statements)
            arg_pairs = node_arg_values.get(first_instance, {})
            param_stmts = []
            for line in raw_stmts:
                new_line = line.replace('s__' + first_instance, 's__' + def_name)
                for aname in arg_pairs:
                    new_line = new_line.replace(str(arg_pairs[aname]), aname)
                param_stmts.append(new_line)
            nodes[def_name]['proc_statements'] = param_stmts

        # Compute modifies sets for all procedures
        nonlocal node_modifies
        node_modifies = compute_modifies(ordered_node_list, all_statements)

        # For parameterized defs, compute modifies as union of all instances
        for nn, def_name in node_def_name.items():
            if def_name not in node_modifies:
                node_modifies[def_name] = set()
            node_modifies[def_name].update(node_modifies.get(nn, set()))

        out = []

        # Header
        out.append('// UCLID5 model (procedure-based) generated by BehaVerify')
        out.append('// Source: ' + model_file)
        out.append('//')
        out.append('// Each behavior tree node is modeled as a UCLID5 procedure.')
        out.append('// One UCLID5 transition (init -> next) corresponds to one behavior tree tick.')
        out.append('// Composite nodes (sequence, selector, parallel) encode BT traversal semantics')
        out.append('// via control flow (if-then-else and procedure calls).')
        out.append('')
        out.append('module main {')
        out.append('')

        # Type declarations
        out.append('  // Type declarations')
        out.append('  // status_t: return status for behavior tree nodes')
        out.append('  type status_t = enum { success, failure, running, invalid };')
        if declared_enumerations:
            enum_vals = sorted(declared_enumerations)
            out.append('  // enum_t: user-defined enumeration values from the behavior tree')
            out.append('  type enum_t = enum { ' + ', '.join(enum_vals) + ' };')
        out.append('')

        # Placeholder for helper function defines (filled in after full assembly)
        helper_insert_index = len(out)

        # State variable declarations
        out.append('  // State variables')
        out.append('  // Variables from the behavior tree blackboard (bl) and environment (env).')
        out.append('  // FROZENVAR variables are initialized non-deterministically and never change.')
        out.append('  // DEFINE variables are computed combinationally (no state).')
        out.append('  // NEURAL variables abstract neural network outputs (havoc + assume constraints).')
        for variable in model.variables:
            if is_local(variable):
                continue
            var_name = variable.name
            var_type = get_var_type(variable)
            scope = variable.var_type if hasattr(variable, 'var_type') and variable.var_type else 'bl'
            if variable.model_as == 'DEFINE':
                # DEFINE variables are inlined at every reference — no declaration needed
                continue
            if variable.model_as == 'NEURAL':
                neural_comment = '  // NEURAL ' + variable.neural_mode + ' (' + scope + ')'
                out.append('  var ' + var_name + ' : ' + var_type + ';' + neural_comment)
                continue
            frozen_tag = ' FROZENVAR' if variable.model_as == 'FROZENVAR' else ''
            var_comment = '  // ' + scope + frozen_tag
            if is_array(variable):
                arr_size = variable_array_size(variable, declared_enumerations, nodes, variables, constants, {})
                for i in range(arr_size):
                    out.append('  var ' + var_name + '_index_' + str(i) + ' : ' + var_type + ';' + var_comment + ' (array element ' + str(i) + ')')
            else:
                out.append('  var ' + var_name + ' : ' + var_type + ';' + var_comment)
        out.append('')

        # Snapshot variables (for at-k references in specs)
        if needed_snapshots:
            out.append('  // Snapshot variables for "at k" references in specifications.')
            out.append('  // These capture the value of a variable at a specific point within a tick.')
            out.append('  // at 0 = pre-tick value, at -1 = post-tick value (the variable itself).')
            for (vname, k) in sorted(needed_snapshots):
                if k >= 0:  # at -1 uses the variable itself
                    vtype = 'integer'  # TODO: look up actual type
                    for variable in model.variables:
                        if variable.name == vname:
                            vtype = get_var_type(variable)
                            break
                    out.append('  var ' + vname + '_at_' + str(k) + ' : ' + vtype + ';')
            out.append('')

        # Node status variables (for spec references to node status)
        if node_status_refs:
            out.append('  // Node status variables for specification references')
            for nref in sorted(node_status_refs):
                out.append('  var ' + nref + '_status : status_t;')
                out.append('  var ' + nref + '_was_active : boolean;')
            out.append('')

        # Delayed env write variables
        if delayed_env_writes:
            out.append('  // Delayed environment writes: buffered until the end of the tick.')
            for dv in sorted(delayed_env_writes):
                vtype = 'integer'
                for variable in model.variables:
                    if variable.name == dv:
                        vtype = get_var_type(variable)
                        break
                out.append('  var delayed__' + dv + ' : ' + vtype + ';')
                out.append('  var delayed__' + dv + '__pending : boolean;')
            out.append('')

        # Decorator state variables (repeat count, one_shot latch)
        decorator_state_vars = []
        for node in ordered_node_list:
            if node['category'] == 'decorator':
                if node['type'] == 'repeat':
                    max_repeat = node['additional_arguments'][0]
                    decorator_state_vars.append(('repeat_count__' + node['name'], 'integer', max_repeat))
                elif node['type'] == 'one_shot':
                    decorator_state_vars.append(('one_shot_val__' + node['name'], 'integer', '0'))
        if decorator_state_vars:
            out.append('  // Decorator state variables')
            for (vname, vtype, _) in decorator_state_vars:
                out.append('  var ' + vname + ' : ' + vtype + ';')
            out.append('')

        # Procedures (bottom-up: leaves first, then composites)
        out.append('  // ---- Node procedures ----')
        out.append('  // Each behavior tree node is a procedure returning its status.')
        out.append('  // Leaf nodes: check (condition test) and action (state update).')
        out.append('  // Composite nodes: sequence (stop on non-success), selector (stop on non-failure),')
        out.append('  //   parallel (run all children, aggregate by policy).')
        out.append('  // Decorator nodes: inverter, X_is_Y, repeat, one_shot.')
        # Emit leaf procedures (one per definition)
        leaf_defs_emitted = set()
        for node in reversed(ordered_node_list):
            nn = node['name']
            if node['category'] == 'leaf':
                def_name = node.get('custom_type', None)
                if def_name and def_name in leaf_defs_emitted:
                    continue
                if def_name:
                    leaf_defs_emitted.add(def_name)
                def_node = nodes[def_name] if def_name else node
                formal_params = parameterized_defs.get(def_name, []) if def_name else []
                proc_lines = generate_node_procedure(def_node, formal_params=formal_params)
                out.extend(proc_lines)
                out.append('')
            else:
                # Composite/decorator nodes: one procedure per instance
                proc_lines = generate_node_procedure(node)
                out.extend(proc_lines)
                out.append('')

        # Tick procedure
        tick_mods = set()
        if root_node_name and root_node_name in node_modifies:
            tick_mods.update(node_modifies[root_node_name])
        for (vname, k) in needed_snapshots:
            if k == 0:
                tick_mods.add(vname + '_at_0')
            else:
                tick_mods.add(vname + '_at_' + str(k))
        for variable in model.variables:
            if variable.model_as == 'NEURAL':
                tick_mods.add(variable.name)
        for nref in node_status_refs:
            tick_mods.add(nref + '_status')
            tick_mods.add(nref + '_was_active')
        for dv in delayed_env_writes:
            tick_mods.add(dv)
            tick_mods.add('delayed__' + dv)
            tick_mods.add('delayed__' + dv + '__pending')
        if hasattr(model, 'update') and model.update:
            for stmt in model.update:
                if not stmt.instant:
                    var_obj = stmt.variable if hasattr(stmt, 'variable') else stmt
                    tick_mods.add(var_obj.name)
        out.append('  // ---- Tick procedure ----')
        out.append('  // Executes one full behavior tree tick:')
        out.append('  //   1. Save pre-tick snapshots (for "at 0" references)')
        out.append('  //   2. Havoc neural network outputs (abstract NN evaluation)')
        out.append('  //   3. Call the root node procedure (tree traversal)')
        out.append('  //   4. Apply delayed environment writes')
        out.append('  //   5. Evaluate environment update rules')
        out.append('  procedure tick()')
        out.append('    returns (root_status : status_t)')
        if tick_mods:
            out.append('    modifies ' + ', '.join(sorted(tick_mods)) + ';')
        out.append('  {')

        # Phase 0: Save at-0 snapshots
        at0_vars = sorted(set(vname for (vname, k) in needed_snapshots if k == 0))
        if at0_vars:
            out.append('    // Save pre-tick snapshots')
            for vname in at0_vars:
                out.append('    ' + vname + '_at_0 = ' + vname + ';')

        # Phase 1: Havoc neural variables (with enum constraints)
        for variable in model.variables:
            if variable.model_as == 'NEURAL':
                out.append('    havoc ' + variable.name + ';')
                if variable.neural_mode == 'classification':
                    enum_vals = get_neural_enum_values(variable)
                    if enum_vals:
                        constraint = ' || '.join([variable.name + ' == ' + v for v in enum_vals])
                        out.append('    assume (' + constraint + ');')

        # Phase 2: Reset node status tracking
        for nref in sorted(node_status_refs):
            out.append('    ' + nref + '_was_active = false;')

        # Phase 3: Reset delayed write pending flags
        for dv in sorted(delayed_env_writes):
            out.append('    delayed__' + dv + '__pending = false;')

        # Phase 4: Call root procedure
        if root_node_name:
            out.append('    call (root_status) = ' + get_proc_name(root_node_name) + '();')
        else:
            out.append('    root_status = failure;')

        # Phase 5: Apply delayed environment writes
        for dv in sorted(delayed_env_writes):
            out.append('    if (delayed__' + dv + '__pending) {')
            out.append('      ' + dv + ' = delayed__' + dv + ';')
            out.append('    }')

        # Phase 6: Environment update (between ticks)
        if hasattr(model, 'update') and model.update:
            out.append('    // Environment update')
            misc_env = create_misc_args({}, None, False, None, None, False, False)
            for stmt in model.update:
                if not stmt.instant:
                    var_obj = stmt.variable if hasattr(stmt, 'variable') else stmt
                    var_name = var_obj.name
                    assign_lines = format_assign_as_ite(stmt.assign, misc_env, var_name)
                    for line in assign_lines:
                        out.append('    ' + line)
                    # Insert snapshot assignment if this env write matches a needed snapshot
                    if var_name in env_snapshot_insert_points:
                        for (snap_vname, snap_k) in env_snapshot_insert_points[var_name]:
                            out.append('    ' + snap_vname + '_at_' + str(snap_k) + ' = ' + var_name + ';')

        out.append('  }')
        out.append('')

        # Init block
        out.append('  // ---- Initialization ----')
        out.append('  // Sets initial values for all state variables.')
        out.append('  // Non-deterministic values use havoc + assume constraints.')
        out.append('  init {')
        for variable in model.variables:
            if is_local(variable) or variable.model_as == 'DEFINE':
                continue
            var_name = variable.name
            if variable.model_as == 'NEURAL':
                out.append('    havoc ' + var_name + ';')
                if variable.neural_mode == 'classification':
                    enum_vals = get_neural_enum_values(variable)
                    if enum_vals:
                        constraint = ' || '.join([var_name + ' == ' + v for v in enum_vals])
                        out.append('    assume (' + constraint + ');')
                continue
            (is_nondet, vals) = get_var_init_values(variable)
            if is_array(variable):
                arr_size = variable_array_size(variable, declared_enumerations, nodes, variables, constants, {})
                for i in range(arr_size):
                    elem_name = var_name + '_index_' + str(i)
                    # For arrays, use index-based init or default
                    out.append('    ' + elem_name + ' = 0;')
            elif is_nondet:
                out.append('    havoc ' + var_name + ';')
                out.append('    assume (' + try_range_assume(var_name, vals) + ');')
            else:
                val = vals[0] if vals else '0'
                out.append('    ' + var_name + ' = ' + val + ';')

        # Init snapshot variables
        for (vname, k) in sorted(needed_snapshots):
            if k == 0:
                out.append('    ' + vname + '_at_0 = ' + vname + ';')

        # Init decorator state variables
        for (vname, _, init_val) in decorator_state_vars:
            out.append('    ' + vname + ' = ' + init_val + ';')

        # Init delayed write pending flags
        for dv in sorted(delayed_env_writes):
            out.append('    delayed__' + dv + '__pending = false;')

        out.append('  }')
        out.append('')

        # Next block
        out.append('  // ---- Transition relation ----')
        out.append('  // Each transition corresponds to one behavior tree tick.')
        out.append('  next {')
        tick_cond = tick_condition
        if tick_cond != 'true':
            out.append('    if (' + tick_cond + ') {')
            out.append('      var root_s : status_t;')
            out.append('      call (root_s) = tick();')
            out.append('    }')
        else:
            out.append('    var root_s : status_t;')
            out.append('    call (root_s) = tick();')

        # FROZENVAR identity
        for variable in model.variables:
            if variable.model_as == 'FROZENVAR' and not is_local(variable):
                out.append('    ' + variable.name + '\' = ' + variable.name + ';')
        out.append('  }')
        out.append('')

        # Specifications
        if specifications_list:
            out.append('  // ---- Specifications ----')
            out.append('  // Translated from the behavior tree specification block.')
            out.append('  // INVARSPEC -> invariant, LTLSPEC -> property[LTL].')
            out.append('  // CTLSPEC is not supported by UCLID5 and is skipped with a warning.')
            for i, (spec_type, spec_expr) in enumerate(specifications_list):
                spec_name = 'spec_' + str(i)
                if spec_type == 'invariant':
                    out.append('  invariant ' + spec_name + ' : ' + spec_expr + ';')
                elif spec_type == 'ltl':
                    out.append('  property[LTL] ' + spec_name + ' : ' + spec_expr + ';')
            out.append('')

        # Control block
        out.append('  control {')
        has_invar = any(s[0] == 'invariant' for s in specifications_list)
        has_ltl = any(s[0] == 'ltl' for s in specifications_list)
        if has_invar:
            out.append('    v = induction;')
            out.append('    check;')
            out.append('    print_results;')
        if has_ltl:
            out.append('    vl = bmc(10);')
            out.append('    check;')
            out.append('    print_results;')
        if not has_invar and not has_ltl:
            out.append('    v = induction;')
            out.append('    check;')
            out.append('    print_results;')
        out.append('  }')
        out.append('')
        out.append('}')

        # Insert helper function defines for functions not natively supported by UCLID5
        helper_lines = []
        if used_helper_functions:
            helper_lines.append('  // Helper function defines (not natively supported by UCLID5)')
            if 'abs' in used_helper_functions:
                helper_lines.append('  define abs(x : integer) : integer = if (x >= 0) then x else -x;')
            if 'max' in used_helper_functions:
                helper_lines.append('  define max(a : integer, b : integer) : integer = if (a >= b) then a else b;')
            if 'min' in used_helper_functions:
                helper_lines.append('  define min(a : integer, b : integer) : integer = if (a <= b) then a else b;')
            if 'xor' in used_helper_functions:
                helper_lines.append('  define xor(a : boolean, b : boolean) : boolean = (a || b) && !(a && b);')
            if 'xnor' in used_helper_functions:
                helper_lines.append('  define xnor(a : boolean, b : boolean) : boolean = (a && b) || (!a && !b);')
            if 'floor' in used_helper_functions:
                helper_lines.append('  // floor is identity for integers')
                helper_lines.append('  define floor(x : integer) : integer = x;')
            if 'count' in used_helper_functions:
                helper_lines.append('  // count: not directly supported, using identity placeholder')
                helper_lines.append('  // TODO: count requires domain-specific implementation')
            helper_lines.append('')
        for i, line in enumerate(helper_lines):
            out.insert(helper_insert_index + i, line)

        output_str = os.linesep.join(out) + os.linesep
        if output_file is None:
            print(output_str)
        else:
            os.makedirs(os.path.dirname(output_file) if os.path.dirname(output_file) else '.', exist_ok=True)
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(output_str)
            print('UCLID5 procedure-based model written to: ' + output_file)

    # ==================================================================
    # FUNCTION FORMAT TABLE
    # ==================================================================

    function_format = {
        'if': ('', format_function_if),
        'loop': ('', format_function_loop),
        'case_loop': ('', format_function_case_loop),
        'abs': ('abs', format_function_before),
        'max': ('max', format_function_recursive_before),
        'min': ('min', format_function_recursive_before),
        'sin': ('sin', format_function_before),
        'cos': ('cos', format_function_before),
        'tan': ('tan', format_function_before),
        'ln': ('ln', format_function_before),
        'not': ('!', format_function_before),
        'and': ('&&', format_function_between),
        'or': ('||', format_function_between),
        'xor': ('xor', format_function_recursive_before),
        'xnor': ('xnor', format_function_recursive_before),
        'implies': ('==>', format_function_between),
        'equivalent': ('<==>', format_function_between),
        'eq': ('==', format_function_between),
        'neq': ('!=', format_function_between),
        'lt': ('<', format_function_between),
        'gt': ('>', format_function_between),
        'lte': ('<=', format_function_between),
        'gte': ('>=', format_function_between),
        'neg': ('-', format_function_before),
        'add': ('+', format_function_between),
        'sub': ('-', format_function_between),
        'mult': ('*', format_function_between),
        'idiv': ('/', format_function_integer_division),
        'mod': ('%', format_function_between),
        'rdiv': ('/', format_function_between),
        'floor': ('floor', format_function_before),
        'count': ('count', format_function_before),
        'index': ('index', format_function_index),
        'active': ('_was_active', format_function_after),
        'success': ('_status == success', format_function_after),
        'running': ('_status == running', format_function_after),
        'failure': ('_status == failure', format_function_after),
        'next': ('next', format_function_before),
        'globally': ('G', format_function_before),
        'finally': ('F', format_function_before),
        'until': ('U', format_function_between),
        'release': ('V', format_function_between),
        'previous': ('Y', format_function_before),
        'not_previous_not': ('Z', format_function_before),
        'historically': ('H', format_function_before),
        'once': ('O', format_function_before),
        'since': ('S', format_function_between),
        'triggered': ('T', format_function_between),
        'globally_bounded': ('G', format_function_before_bounded),
        'finally_bounded': ('F', format_function_before_bounded),
        'until_bounded': ('U', format_function_between_bounded),
        'release_bounded': ('V', format_function_between_bounded),
        'historically_bounded': ('H', format_function_before_bounded),
        'once_bounded': ('O', format_function_before_bounded),
        'since_bounded': ('S', format_function_between_bounded),
        'triggered_bounded': ('T', format_function_between_bounded),
        'exists_globally': ('EG', format_function_before),
        'exists_next': ('EX', format_function_before),
        'exists_finally': ('EF', format_function_before),
        'exists_until': (('E', 'U'), format_function_before_between),
        'always_globally': ('AG', format_function_before),
        'always_next': ('AX', format_function_before),
        'always_finally': ('AF', format_function_before),
        'always_until': (('A', 'U'), format_function_before_between),
    }

    create_node = {
        'sequence': create_composite,
        'selector': create_composite,
        'parallel': create_composite,
        'X_is_Y': create_X_is_Y,
        'inverter': create_decorator,
        'repeat': create_repeat,
        'one_shot': create_one_shot,
        'check': create_check,
        'environment_check': create_check,
        'action': create_action,
    }

    # ==================================================================
    # MAIN EXECUTION PIPELINE
    # ==================================================================

    # Phase 1: Parse and validate
    (model, variables, constants, declared_enumerations) = validate_model(
        metamodel_file, model_file, recursion_limit, skip_grammar_check)

    # Phase 2: Walk tree
    (_, _, nodes, local_variables, initial_statements, all_statements) = walk_tree(model.root)

    # Phase 3: Collect at-k references from specifications
    node_status_refs = set()
    needed_snapshots = set()
    snapshot_insert_points = {}
    env_snapshot_insert_points = {}
    delayed_env_writes = set()
    node_modifies = {}
    local_vars_by_def = {}
    define_exprs = {}  # DEFINE var name -> inline expression string

    at_refs = collect_all_at_refs(model.specifications)
    for (vname, k) in at_refs:
        if k >= 0:
            needed_snapshots.add((vname, k))

    # Phase 4: Format tick condition
    tick_condition = ('true' if model.tick_condition is None
                      else format_code(model.tick_condition, create_misc_args(
                          loop_references={}, node_name=None, use_stages=False,
                          overwrite_stage=None, define_substitutions=None,
                          specification_writing=False, specification_warning=False))[0])

    # Phase 5: Handle specifications
    specifications_list = handle_specifications(model.specifications)

    # Phase 6: Load NN contracts (if provided)
    nn_contracts = load_contracts(contracts_file)

    # Phase 7: Generate and write
    write_uclid5(output_file)
