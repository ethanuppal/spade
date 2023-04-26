from spade import Spade

from pathlib import Path

def state_file():
    return Path(__file__).parent / "../build/state.ron"

def test_correct_hierarchical_translation_works():
    s = Spade("proj::python::hierarchical_translation::top", str(state_file()))

    assert s.translate_value("sub_0.local", "0x") == "A()"
    assert s.translate_value("sub_0.local", "10") == "B(false)"
    assert s.translate_value("sub_0.local", "11") == "B(true)"

