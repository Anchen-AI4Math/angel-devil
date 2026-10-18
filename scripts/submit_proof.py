"""Submit one specified proof; never retries a mutation automatically."""
import argparse, json, urllib.request, uuid
from pathlib import Path
from prepare_proposal import authenticate, BASE

p = argparse.ArgumentParser()
p.add_argument('theorem_id')
p.add_argument('file', type=Path)
p.add_argument('explanation', type=Path)
p.add_argument('receipt', type=Path)
a = p.parse_args()
if a.receipt.exists():
    raise SystemExit('Receipt exists; poll that submission instead of resubmitting')
token = authenticate()
boundary = '----AngelDevil' + uuid.uuid4().hex
parts = []
for name, value in [('theorem_id', a.theorem_id),
                    ('explanation', a.explanation.read_text(encoding='utf-8'))]:
    parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"'
                  f'\r\n\r\n{value}\r\n').encode())
parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="file"; '
              f'filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n').encode()
             + a.file.read_bytes() + b'\r\n')
parts.append(f'--{boundary}--\r\n'.encode())
request = urllib.request.Request(BASE+'/verify', data=b''.join(parts), headers={
    'Authorization':'Bearer '+token, 'Content-Type':'multipart/form-data; boundary='+boundary})
with urllib.request.urlopen(request, timeout=60) as response:
    receipt = json.load(response)
a.receipt.write_text(json.dumps(receipt,indent=2), encoding='utf-8')
print(json.dumps(receipt))
