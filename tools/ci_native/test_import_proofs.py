import hashlib
import zipfile
from pathlib import Path
import unittest
from unittest.mock import patch
import rpc
import import_proof_lease
import test_proofs

class CoordinatorReturnTests(unittest.TestCase):
    setUp = test_proofs.ProofProtocolTests.setUp
    plan = test_proofs.ProofProtocolTests.plan

    def fixture(self):
        control = self.plan(self.names[:1])
        lease = rpc.read(control / 'lease.json')
        request = rpc.read(control / 'request-0.json')
        returned = self.root / 'returned'
        returned.mkdir()
        module = self.names[0]
        files = []
        with zipfile.ZipFile(returned / 'runtime-parts.zip', 'w') as archive:
            for suffix in rpc.PROOF_PARTS:
                part = 'ir' if suffix == '.c' else 'lib/lean'
                path = f'.lake/build/{part}/{module.replace(".", "/")}{suffix}'
                data = (module + suffix).encode()
                archive.writestr(path, data)
                files.append({'module': module, 'path': path, 'bytes': len(data),
                              'sha256': hashlib.sha256(data).hexdigest()})
        manifest = {'schema': 1, 'snapshot': self.snapshot['fingerprint'],
                    'modules': [module], 'files': files}
        rpc.atomic(returned / 'artifacts-0.json', manifest)
        rpc.atomic(returned / 'response-0.json', {
            'snapshot': self.snapshot['fingerprint'], 'operation': rpc.PROOF_OPERATION,
            'batch': 0, 'elapsed_ms': 1234, 'lease_id': lease['lease_id'],
            'request_sha256': lease['request_sha256'], 'run_id': '123', 'run_attempt': 1,
            'runner_name': 'registered-james',
            'result': {'ok': True, 'modules': [{'module': module, 'ok': True}]},
            'artifacts': {'manifest': 'artifacts-0.json',
                          'sha256': rpc.digest(returned / 'artifacts-0.json')}})
        provenance = {'run_id': '123', 'run_attempt': 1, 'runner_name': 'registered-james',
                      'workflow_sha': 'b' * 40,
                      'artifact_name': f'native-123-1-{lease["lease_id"]}'}
        proxy = self.root / 'proxy'
        round = self.root / 'round'
        round.mkdir()
        rpc.atomic(round / 'request-7.json', request)
        durable = self.root / 'leases.json'
        rpc.atomic(durable, {'snapshot': self.snapshot,
                             'workers': {'james': {'batch': 7, 'modules': [module]}}})
        return control, returned, provenance, proxy, round, durable

    def test_real_accept_imports_eight_parts_and_completes_correct_batch(self):
        control, returned, provenance, proxy, round, durable = self.fixture()
        import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        response = rpc.read(round / 'response-7.json')
        self.assertEqual(response['batch'], 7)
        self.assertEqual(response['artifacts']['files'], 8)
        self.assertEqual(response['elapsed_ms'], 1234)
        self.assertEqual(len([p for p in proxy.rglob('*') if p.is_file()]), 8)

    def test_stale_lease_or_tampered_zip_cannot_write_completion(self):
        control, returned, provenance, proxy, round, durable = self.fixture()
        state = rpc.read(durable)
        state['workers']['james']['batch'] = 8
        rpc.atomic(durable, state)
        with self.assertRaises(ValueError):
            import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        self.assertFalse((round / 'response-7.json').exists())
        state['workers']['james']['batch'] = 7
        rpc.atomic(durable, state)
        with zipfile.ZipFile(returned / 'runtime-parts.zip', 'a') as archive:
            archive.writestr('../escape', b'foreign')
        with self.assertRaises(ValueError):
            import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        self.assertFalse((round / 'response-7.json').exists())

if __name__ == '__main__':
    unittest.main()
