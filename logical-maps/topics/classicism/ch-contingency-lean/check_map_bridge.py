#!/usr/bin/env python3
"""Structural audit only; not a theorem-prover verification."""
from pathlib import Path
import re
import yaml

root = Path(__file__).resolve().parents[1]
standalone = root / 'ch-contingency-lean'
principles = root / 'principles'
result = root / 'results' / 'bounded-forcing-and-rigid-naturals-imply-cardinal-ch-contingency.yaml'

def load(path):
    with path.open(encoding='utf-8') as stream:
        return yaml.safe_load(stream)

rule = load(result)
assert rule['premises'] == ['bounded-ch-forcing-setup', 'necessary-lower-peano-e', 'rigid-lower-nat-e']
assert rule['conclusion'] == 'contingency-of-cardinal-ch'
assert rule['status'] == 'proved'
assert rule['certificate']['lean'] == 'none'
for label in rule['premises'] + [rule['conclusion']]:
    assert load(principles / (label + '.yaml'))['id'] == label

bridge = (standalone / 'Classicism/MathematicalContingency/MapBridge.lean').read_text(encoding='utf-8')
cert = (standalone / 'Classicism/MathematicalContingency/Certificates/MapBridge01.lean').read_text(encoding='utf-8')
endpoint = (standalone / 'Classicism/MathematicalContingency/ClosedBoundsCH.lean').read_text(encoding='utf-8')
for phrase in ['theorem bounded_forcing_implies_cardinal_ch_contingency', 'natural_CH_contingency_closedBounds', 'rigidN : Rigid (@LowerNat e _)', 'hi : DraftBoxInfinity e', 'StronglyInaccessible K L']:
    assert phrase in bridge
assert 'Rigid (@LowerNat e _)' in endpoint
assert 'natural_CH_contingency_closedBounds' in endpoint
assert 'Certificates.ClosedBoundsCH01' in cert
assert '#classicism_deep_split_derive Classicism.MathematicalContingency.bounded_forcing_implies_cardinal_ch_contingency' in cert
for path in [standalone / 'Classicism/MathematicalContingency/MapBridge.lean', standalone / 'Classicism/MathematicalContingency/Certificates/MapBridge01.lean', standalone / 'Diagnostics/MapBridgeImportCheck.lean']:
    src = path.read_text(encoding='utf-8')
    src = re.sub(r'/-.*?-/', '', src, flags=re.DOTALL)
    src = re.sub(r'--[^\n]*', '', src)
    for forbidden in ['sorry', 'admit', 'axiom ']:
        assert forbidden not in src, f'{forbidden} in {path.name}'
print('CH map bridge: source and record structure consistent (not Lean verified).')
