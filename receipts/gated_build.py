#!/usr/bin/env python3
"""aft-lane gated build: swap gate (wait under 12GB used) + fcntl lock + lake build."""
import fcntl, subprocess, sys, time, os

LANE = "/Volumes/Substrate-1/bigo/aft-lane"
LOCK = "/Volumes/Substrate-1/bigo/.build.lock"
LIMIT_MB = 12288.0

def swap_used_mb() -> float:
    out = subprocess.check_output(["sysctl", "-n", "vm.swapusage"], text=True)
    for part in out.split():
        if part.endswith("M") and part[:-1].replace(".", "", 1).isdigit():
            pass
    # format: total = X M  used = Y M  free = Z M
    fields = out.replace("(", "").replace(")", "").split()
    used = fields[fields.index("used") + 2].rstrip("M")
    return float(used)

for attempt in range(30):
    used = swap_used_mb()
    if used < LIMIT_MB:
        break
    print(f"[gate] swap used {used:.0f}M > {LIMIT_MB:.0f}M — waiting (attempt {attempt + 1}/30)", flush=True)
    time.sleep(45)
else:
    print("[gate] Bounded wait exhausted; gate still blocked. Exiting without building.", flush=True)
    sys.exit(3)

with open(LOCK, "w") as lockf:
    fcntl.flock(lockf, fcntl.LOCK_EX)
    print(f"[gate] swap used {used:.0f}M — gate open, lock held, building", flush=True)
    os.chdir(LANE)
    r = subprocess.run(["lake", "build", "AFT"], capture_output=True, text=True, timeout=5400)
    stamp = time.strftime("%H%M%S")
    with open(f"receipts/build-{stamp}.log", "w") as rec:
        rec.write(r.stdout + r.stderr)
        rec.write(f"\nexit={r.returncode}\n")
    print(r.stdout[-4000:], flush=True)
    print(r.stderr[-4000:], file=sys.stderr, flush=True)
    print(f"[done] exit={r.returncode}", flush=True)
    sys.exit(r.returncode)
