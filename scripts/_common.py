import os, sys, json, time, functools
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
RESULTS = os.path.join(ROOT, "results")
os.makedirs(RESULTS, exist_ok=True)
print = functools.partial(print, flush=True)
def save(name, obj):
    path = os.path.join(RESULTS, name + ".json")
    with open(path, "w") as f: json.dump(obj, f, indent=1, default=str)
    print(f"-> {os.path.relpath(path, ROOT)}")
def load(name):
    with open(os.path.join(RESULTS, name + ".json")) as f: return json.load(f)
