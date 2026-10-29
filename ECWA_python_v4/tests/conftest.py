import os
import sys

# Pin the v4 project root to sys.path[0] so that `import ecwa` resolves to
# *this* copy's ecwa/ (which contains maprefit) rather than the sibling
# v3/ecwa regular package that otherwise shadows it during pytest collection
# of tests/. (v3/ecwa has core.py but no maprefit.py.)
_V4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _V4 in sys.path:
    sys.path.remove(_V4)
sys.path.insert(0, _V4)
# Drop any `ecwa` already cached from the wrong (v3) location so the test
# modules re-resolve it to v4/ecwa above.
for _m in [m for m in list(sys.modules) if m == "ecwa" or m.startswith("ecwa.")]:
    del sys.modules[_m]
