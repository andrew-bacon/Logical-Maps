#!/usr/bin/env python3
"""Prepare and verify exact/lower integration using the UNMODIFIED pmap auditor.

This script never sets certificate.lean itself. The only writer of verified
metadata is scripts/pmap.py lean-check classicism --update after its complete
native build, generated-statement probe and axiom audit have succeeded.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import yaml

ROOT = Path(__file__).resolve().parent.parent
TOPIC = ROOT / 'topics/classicism'
LEAN = TOPIC / 'lean'
DEFS = {
    'necessary-lower-peano-e': 'Classicism.P.NecessaryLowerPeanoE.schemaIn',
    'exact-peano-e': 'Classicism.P.ExactPeanoE.schemaIn',
    'exact-lower-finite-cardinality-bijection-e': 'Classicism.P.ExactLowerBijectionE.schemaIn',
}
RESULTS = {
    'necessary-lower-peano-implies-exact-peano-e': (
        ['necessary-lower-peano-e'], 'exact-peano-e'),
    'necessary-lower-peano-implies-cardinality-bijection-e': (
        ['necessary-lower-peano-e'], 'exact-lower-finite-cardinality-bijection-e'),
    'exact-peano-and-necessary-lower-peano-imply-cardinality-bijection-e': (
        ['exact-peano-e', 'necessary-lower-peano-e'],
        'exact-lower-finite-cardinality-bijection-e'),
}
MAP_MODULE = '''import Classicism.Map
import Classicism.Certified.ExactLower

/-!
# The exact/lower map arrows at their generated statement types

Each proof cites a native object-language entailment. Classicism.Map's
map_cert lifts the pure entailment to every admitted signature and every
axiom set entailing the displayed premises. No shallow extensionality
axiom or additional arithmetic premise is inserted here.
-/
namespace Classicism.Map

theorem necessary_lower_peano_implies_exact_peano_e :
    Statements.necessary_lower_peano_implies_exact_peano_e := by
  map_cert Proofs.necessary_lower_peano_implies_exact_peano_e.entails

theorem necessary_lower_peano_implies_cardinality_bijection_e :
    Statements.necessary_lower_peano_implies_cardinality_bijection_e := by
  map_cert Proofs.necessary_lower_peano_implies_cardinality_bijection_e.entails

theorem exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e :
    Statements.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e := by
  map_cert Proofs.exact_peano_and_necessary_lower_peano_imply_cardinality_bijection_e.entails

end Classicism.Map
'''


def load(path: Path):
    return yaml.safe_load(path.read_text(encoding='utf-8'))


def prepare() -> None:
    for pid, definition in DEFS.items():
        path = TOPIC / 'principles' / (pid + '.yaml')
        obj = load(path)
        if obj['id'] != pid:
            raise ValueError(f'Wrong principle at {path}')
        current = obj.get('lean_def')
        if current not in (None, definition):
            raise ValueError(f'Refusing to replace existing lean_def for {pid}')
        if current is None:
            path.write_text(path.read_text(encoding='utf-8').rstrip()
                            + '\nlean_def: ' + definition + '\n', encoding='utf-8')
    for rid, (premises, conclusion) in RESULTS.items():
        path = TOPIC / 'results' / (rid + '.yaml')
        obj = load(path)
        if (obj['premises'], obj['conclusion'], obj['status']) != (premises, conclusion, 'proved'):
            raise ValueError(f'Unexpected mathematical statement: {rid}')
        ref = 'Classicism.Map.' + rid.replace('-', '_')
        current = obj['certificate'].get('lean_ref')
        if current not in (None, ref):
            raise ValueError(f'Refusing to replace existing certificate for {rid}')
        if current is None:
            text, n = re.subn(r'(?m)^(  lean: (?:none|stated|verified))$',
                              lambda m: m[0] + '\n  lean_ref: ' + ref,
                              path.read_text(encoding='utf-8'))
            if n != 1:
                raise ValueError(f'Expected one Lean status field for {rid}')
            path.write_text(text, encoding='utf-8')
    topic_path = TOPIC / 'topic.yaml'
    text = topic_path.read_text(encoding='utf-8')
    new_import = '  - Classicism.Certified.ExactLowerSchemas\n'
    if new_import not in text:
        anchor = '  - Classicism.Certified.Arithmetic\n'
        if text.count(anchor) != 1:
            raise ValueError('Expected one native arithmetic import')
        text = text.replace(anchor, anchor + new_import)
        topic_path.write_text(text, encoding='utf-8')
    for path in (LEAN / 'Classicism.lean', LEAN / 'scripts/MapIndex.lean'):
        text = path.read_text(encoding='utf-8')
        new_import = 'import Classicism.MapExactLower\n'
        if new_import not in text:
            anchor = 'import Classicism.Map\n'
            if text.count(anchor) != 1:
                raise ValueError(f'Expected one map import in {path}')
            path.write_text(text.replace(anchor, anchor + new_import), encoding='utf-8')
    path = LEAN / 'Classicism/MapExactLower.lean'
    if path.exists() and path.read_text(encoding='utf-8') != MAP_MODULE:
        raise ValueError('Refusing to overwrite a different MapExactLower module')
    path.write_text(MAP_MODULE, encoding='utf-8')
    subprocess.run(['python3', str(ROOT / 'scripts/pmap.py'), 'lean', 'classicism'],
                   cwd=ROOT, check=True)
    print('Prepared definitions, certificate references and native generated statements.', flush=True)


def confirm() -> None:
    index = json.loads((LEAN / 'map/index.json').read_text(encoding='utf-8'))
    checked = {}
    for rid, (premises, conclusion) in RESULTS.items():
        obj = load(TOPIC / 'results' / (rid + '.yaml'))
        ref = 'Classicism.Map.' + rid.replace('-', '_')
        if (obj['premises'], obj['conclusion'], obj['certificate']['lean'],
            obj['certificate'].get('lean_ref')) != (premises, conclusion, 'verified', ref):
            raise RuntimeError(f'Native pmap did not verify the intended result: {rid}')
        entry = index['results'][rid]
        cert = entry['certificate']
        if cert['name'] != ref or not set(cert['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Certificate/index mismatch: {rid}')
        checked[rid] = entry
    report = {
        'source_commit': os.environ.get('GITHUB_SHA', ''),
        'workflow_run': os.environ.get('GITHUB_RUN_ID', ''),
        'command': 'python3 scripts/pmap.py lean-check classicism --update',
        'native_audit_succeeded': True,
        'principle_definitions': DEFS,
        'results': checked,
        'scope': 'Exact/at-least comparison only; no CH map verification is claimed.',
    }
    (LEAN / 'map/exact-lower-audit.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('Confirmed all three exact/lower map certificates after native pmap audit.', flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('step', choices=['prepare', 'audit', 'publish-paths'])
    args = parser.parse_args()
    if args.step == 'prepare':
        prepare()
    elif args.step == 'audit':
        subprocess.run(['python3', str(ROOT / 'scripts/pmap.py'), 'lean-check', 'classicism', '--update'],
                       cwd=ROOT, check=True)
        confirm()
        subprocess.run(['python3', str(ROOT / 'scripts/pmap.py'), 'validate', 'classicism'],
                       cwd=ROOT, check=True)
    else:
        paths = [TOPIC / 'topic.yaml', LEAN / 'Classicism.lean',
                 LEAN / 'scripts/MapIndex.lean', LEAN / 'Classicism/MapExactLower.lean',
                 LEAN / 'Classicism/Statements.lean', LEAN / 'Classicism/ModelStatements.lean',
                 LEAN / 'Classicism/MapDerived.lean', LEAN / 'map/index.json',
                 LEAN / 'map/exact-lower-audit.json']
        paths += [TOPIC / 'principles' / (pid + '.yaml') for pid in DEFS]
        paths += [TOPIC / 'results' / (rid + '.yaml') for rid in RESULTS]
        for path in paths:
            print(path.relative_to(ROOT.parent))


if __name__ == '__main__':
    main()
