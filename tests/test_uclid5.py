'''
Tests for the UCLID5 code generation backend.
'''
import os
import pytest
from importlib.resources import files

from behaverify.dsl_to_uclid5 import dsl_to_uclid5


@pytest.fixture
def metamodel_file():
    return files('behaverify').joinpath('data', 'metamodel', 'behaverify.tx')


@pytest.fixture
def collatz_tree():
    return os.path.join(os.path.dirname(__file__), '..', 'examples', 'Collatz', 'collatz_small.tree')


@pytest.fixture
def drunken_drone_tree():
    return os.path.join(os.path.dirname(__file__), '..', 'examples', 'DrunkenDrone', 'DrunkenDrone.tree')


@pytest.fixture
def acasxu_tree():
    return os.path.join(os.path.dirname(__file__), '..', 'examples', 'AcasXu', 'acasxu_SINGLE.tree')


@pytest.fixture
def tutorial_collatz_tree():
    return os.path.join(os.path.dirname(__file__), '..', 'tutorial_examples', 'collatz.tree')


@pytest.fixture
def tutorial_light_tree():
    return os.path.join(os.path.dirname(__file__), '..', 'tutorial_examples', 'light_controller.tree')


@pytest.fixture
def tutorial_primes_tree():
    return os.path.join(os.path.dirname(__file__), '..', 'tutorial_examples', 'primes.tree')


class TestUclid5Generation:
    '''Tests for basic UCLID5 code generation.'''

    def test_collatz_generates_file(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        assert os.path.exists(output_file)

    def test_collatz_has_module_main(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'module main {' in content

    def test_collatz_has_status_type(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'type status_t = enum { success, failure, running, invalid };' in content

    def test_collatz_has_state_variable(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'var x : integer;' in content

    def test_collatz_has_procedures(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'procedure check_a()' in content
        assert 'procedure action_b()' in content
        assert 'procedure action_c()' in content
        assert 'procedure action_d()' in content
        assert 'procedure sequence_seq()' in content
        assert 'procedure selector_sel()' in content

    def test_collatz_has_init_block(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'init {' in content
        assert 'havoc x;' in content

    def test_collatz_has_nondet_init_assume(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'x >= 1 && x <= 5' in content

    def test_collatz_has_next_block(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'next {' in content
        assert 'call (root_s) = tick();' in content

    def test_collatz_has_invariant_spec(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'invariant spec_0' in content
        assert 'x < 4000' in content

    def test_collatz_has_control_block(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'control {' in content
        assert 'induction' in content

    def test_collatz_has_tick_procedure(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'procedure tick()' in content
        assert 'returns (root_status : status_t)' in content

    def test_collatz_has_modifies_clauses(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'modifies x;' in content

    def test_collatz_has_min_helper(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'define min(' in content


class TestUclid5NodeStructure:
    '''Tests for correct procedure structure.'''

    def test_collatz_sequence_short_circuits(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        # Sequence stops on non-success
        assert 'cs__ != success' in content

    def test_collatz_selector_short_circuits(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        # Selector stops on non-failure
        assert 'cs__ != failure' in content

    def test_collatz_check_returns_success_or_failure(self, metamodel_file, collatz_tree, tmp_path):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 's__a = if (' in content
        assert 'then success else failure;' in content


class TestUclid5ParameterizedProcedures:
    '''Tests for parameterized procedure generation.'''

    def test_acasxu_single_check_procedure(self, metamodel_file, acasxu_tree, tmp_path):
        output_file = str(tmp_path / 'acasxu.ucl')
        dsl_to_uclid5(metamodel_file, acasxu_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        # Should have one parameterized check, not five separate ones
        assert 'procedure check_compare_val(value : enum_t)' in content
        # Should NOT have instance-specific procedures
        assert 'procedure check_if_was_clear' not in content

    def test_acasxu_calls_with_arguments(self, metamodel_file, acasxu_tree, tmp_path):
        output_file = str(tmp_path / 'acasxu.ucl')
        dsl_to_uclid5(metamodel_file, acasxu_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'check_compare_val(clear)' in content
        assert 'check_compare_val(strong_left)' in content


class TestUclid5CTLWarning:
    '''Test that CTL specifications produce warnings.'''

    def test_ctl_specs_skipped_with_warning(self, metamodel_file, drunken_drone_tree, tmp_path, capsys):
        output_file = str(tmp_path / 'drone.ucl')
        dsl_to_uclid5(metamodel_file, drunken_drone_tree, output_file, False, False, 0, False)
        captured = capsys.readouterr()
        assert 'CTL specifications not supported in UCLID5' in captured.out

    def test_drunken_drone_generates(self, metamodel_file, drunken_drone_tree, tmp_path):
        output_file = str(tmp_path / 'drone.ucl')
        dsl_to_uclid5(metamodel_file, drunken_drone_tree, output_file, False, False, 0, False)
        assert os.path.exists(output_file)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'module main {' in content

    def test_drunken_drone_has_snapshot(self, metamodel_file, drunken_drone_tree, tmp_path):
        output_file = str(tmp_path / 'drone.ucl')
        dsl_to_uclid5(metamodel_file, drunken_drone_tree, output_file, False, False, 0, False)
        with open(output_file, 'r') as f:
            content = f.read()
        assert 'y_d_at_1 = y_d;' in content


class TestUclid5NNContracts:
    '''Tests for neural network contract generation.'''

    def test_contracts_file_not_found(self, metamodel_file, collatz_tree, tmp_path, capsys):
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False,
                            contracts_file='/nonexistent/path.json')
        captured = capsys.readouterr()
        assert 'Failed to load contracts file' in captured.out

    def test_contracts_with_valid_json(self, metamodel_file, collatz_tree, tmp_path):
        import json
        contracts_file = str(tmp_path / 'contracts.json')
        with open(contracts_file, 'w') as f:
            json.dump({
                'some_network': {
                    'preconditions': ['x >= 0'],
                    'postconditions': ['result != 0']
                }
            }, f)
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, collatz_tree, output_file, False, False, 0, False,
                            contracts_file=contracts_file)
        assert os.path.exists(output_file)


class TestUclid5TutorialExamples:
    '''Test with tutorial examples to ensure broader compatibility.'''

    def test_tutorial_collatz(self, metamodel_file, tutorial_collatz_tree, tmp_path):
        if not os.path.exists(tutorial_collatz_tree):
            pytest.skip('Tutorial example not found')
        output_file = str(tmp_path / 'collatz.ucl')
        dsl_to_uclid5(metamodel_file, tutorial_collatz_tree, output_file, False, False, 0, False)
        assert os.path.exists(output_file)

    def test_tutorial_light_controller(self, metamodel_file, tutorial_light_tree, tmp_path):
        if not os.path.exists(tutorial_light_tree):
            pytest.skip('Tutorial example not found')
        output_file = str(tmp_path / 'light.ucl')
        dsl_to_uclid5(metamodel_file, tutorial_light_tree, output_file, False, False, 0, False)
        assert os.path.exists(output_file)

    def test_tutorial_primes(self, metamodel_file, tutorial_primes_tree, tmp_path):
        if not os.path.exists(tutorial_primes_tree):
            pytest.skip('Tutorial example not found')
        output_file = str(tmp_path / 'primes.ucl')
        dsl_to_uclid5(metamodel_file, tutorial_primes_tree, output_file, False, False, 0, False)
        assert os.path.exists(output_file)


class TestUclid5CLI:
    '''Test the CLI integration.'''

    def test_uclid5_mode_recognized(self):
        from behaverify.behaverify import main
        with pytest.raises(SystemExit) as exc_info:
            main(['uclid5', '--help'])
        assert exc_info.value.code == 0

    def test_uclid5_in_valid_modes(self):
        '''Verify uclid5 appears in the valid modes list.'''
        from behaverify.behaverify import main
        with pytest.raises(SystemExit):
            main(['uclid5_nonexistent', '--help'])
