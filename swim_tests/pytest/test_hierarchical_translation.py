from spade import Spade

from pathlib import Path

def state_file():
    return Path(__file__).parent / "../build/state.ron"

def test_correct_hierarchical_translation_works():
    s = Spade("proj::python::hierarchical_translation::top", str(state_file()))

    assert s.translate_value("sub_0.local", "0x") == "A()"
    assert s.translate_value("sub_0.local", "10") == "B(false)"
    assert s.translate_value("sub_0.local", "11") == "B(true)"

def test_stage_variables():
    s = Spade("proj::python::hierarchical_translation::top", str(state_file()))
    assert s.translate_value("subpipe_0.s1_var", "1") == "1"

def test_reg_value():
    s = Spade("proj::python::hierarchical_translation::top", str(state_file()))
    assert s.translate_value("in_reg", "10") == "2"

def test_output_value():
    s = Spade("proj::python::hierarchical_translation::top", str(state_file()))
    assert s.translate_value("output__", "1") == "true"


def test_input_value():
    s = Spade("proj::python::hierarchical_translation::top", str(state_file()))
    assert s.translate_value("in_i", "0x") == "A()"

