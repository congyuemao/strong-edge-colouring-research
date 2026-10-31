"""runner: a small parallel job runner for long experiments on this machine (Windows, standard library only).

A job is a directory (keep it on E:, e.g. E:/se20-data/runs/<name>) holding
  tasks.jsonl    one task per line: {"id": str, "cmd": [args...], "cwd": str?, "env": {str: str}?}
  control.json   {"workers": int, "priority": "idle"|"below"|"normal"|"above", "pause": bool, "stop": bool,
                  "extra_pids": [int]}  -- re-read every 2 s while running, so it can be edited at any time
  results.jsonl  appended when a task ends: {"id", "rc", "start", "end", "last"} (last = last log line)
  logs/<id>.log  stdout + stderr of the task
  running.json   tasks currently running (id -> pid), for status and for cleaning up after a crash

Semantics
  * a task is done when it has a result with rc == 0; failed tasks (rc != 0) are not retried unless "retry" is run
  * priority is applied to every running task's whole process tree (the venv launcher spawns a child interpreter)
    and to "extra_pids" (other long processes that should yield too)
  * pause suspends all task trees (NtSuspendProcess); unpause resumes them; nothing is lost
  * stop (or killing the runner) terminates the task trees; a restarted runner relaunches unfinished tasks, so
    tasks must checkpoint and resume by themselves
  * lowering "workers" never kills tasks; it only stops launching new ones until fewer are running

Usage
  runner.py init <jobdir> <tasks.jsonl> [workers]     create the job (copies the task list, writes control.json)
  runner.py run <jobdir>                              run until every task is done (start it in the background)
  runner.py status <jobdir>                           counts, running tasks with their last log line, results
  runner.py ctl <jobdir> key=value ...                e.g. priority=idle  workers=8  pause=1  stop=1
  runner.py retry <jobdir>                            forget failed results so they run again
"""
import ctypes
import ctypes.wintypes as wt
import json
import os
import subprocess
import sys
import time

PRIORITY = {"idle": 0x40, "below": 0x4000, "normal": 0x20, "above": 0x8000}
k32 = ctypes.WinDLL("kernel32", use_last_error=True)
ntdll = ctypes.WinDLL("ntdll")


class PROCESSENTRY32W(ctypes.Structure):
    _fields_ = [("dwSize", wt.DWORD), ("cntUsage", wt.DWORD), ("th32ProcessID", wt.DWORD),
                ("th32DefaultHeapID", ctypes.c_size_t), ("th32ModuleID", wt.DWORD), ("cntThreads", wt.DWORD),
                ("th32ParentProcessID", wt.DWORD), ("pcPriClassBase", ctypes.c_long), ("dwFlags", wt.DWORD),
                ("szExeFile", ctypes.c_wchar * 260)]


k32.CreateToolhelp32Snapshot.restype = wt.HANDLE
k32.OpenProcess.restype = wt.HANDLE


def process_table():
    """pid -> (parent pid, exe name)"""
    snap = k32.CreateToolhelp32Snapshot(0x2, 0)
    entry = PROCESSENTRY32W()
    entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
    table = {}
    ok = k32.Process32FirstW(snap, ctypes.byref(entry))
    while ok:
        table[entry.th32ProcessID] = (entry.th32ParentProcessID, entry.szExeFile)
        ok = k32.Process32NextW(snap, ctypes.byref(entry))
    k32.CloseHandle(snap)
    return table


def tree(pid, table):
    """pid and all its descendants that are alive"""
    out, stack = [], [pid]
    children = {}
    for p, (pp, _) in table.items():
        children.setdefault(pp, []).append(p)
    while stack:
        p = stack.pop()
        if p in table and p not in out:
            out.append(p)
            stack.extend(children.get(p, []))
    return out


def with_handle(pid, fn):
    h = k32.OpenProcess(0x0200 | 0x0800 | 0x0001 | 0x1000, False, pid)
    if not h:
        return False
    try:
        return fn(h)
    finally:
        k32.CloseHandle(h)


class POWER_THROTTLING_STATE(ctypes.Structure):
    _fields_ = [("Version", wt.ULONG), ("ControlMask", wt.ULONG), ("StateMask", wt.ULONG)]


def set_priority(pid, cls):
    """Priority class, plus opting out of Windows power throttling (EcoQoS), which can park background processes
    on the efficiency cores; at idle priority throttling is left to Windows."""
    def apply(h):
        k32.SetPriorityClass(h, cls)
        st = POWER_THROTTLING_STATE(1, 0x1 | 0x4, 0x1 | 0x4 if cls == PRIORITY["idle"] else 0)
        k32.SetProcessInformation(h, 4, ctypes.byref(st), ctypes.sizeof(st))
        return True
    return with_handle(pid, apply)


def suspend(pid):
    return with_handle(pid, lambda h: ntdll.NtSuspendProcess(h) == 0)


def resume(pid):
    return with_handle(pid, lambda h: ntdll.NtResumeProcess(h) == 0)


def terminate(pid):
    return with_handle(pid, lambda h: k32.TerminateProcess(h, 1))


def read_json(path, default):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return default


def write_json(path, obj):
    with open(path + ".tmp", "w", encoding="utf-8") as fh:
        json.dump(obj, fh, indent=1)
    os.replace(path + ".tmp", path)


def load_tasks(job):
    with open(os.path.join(job, "tasks.jsonl"), encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def load_results(job):
    res = {}
    path = os.path.join(job, "results.jsonl")
    if os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                if line.strip():
                    r = json.loads(line)
                    res[r["id"]] = r
    return res


def last_line(path):
    try:
        with open(path, "rb") as fh:
            fh.seek(0, 2)
            size = fh.tell()
            fh.seek(max(0, size - 4096))
            lines = [l for l in fh.read().decode("utf-8", "replace").splitlines() if l.strip()]
            return lines[-1].strip() if lines else ""
    except OSError:
        return ""


def cmd_init(job, tasks_file, workers=None):
    os.makedirs(os.path.join(job, "logs"), exist_ok=True)
    with open(tasks_file, encoding="utf-8") as src, open(os.path.join(job, "tasks.jsonl"), "w",
                                                         encoding="utf-8") as dst:
        dst.write(src.read())
    ctl = read_json(os.path.join(job, "control.json"), {})
    ctl.setdefault("workers", int(workers) if workers else max(1, os.cpu_count() - 2))
    ctl.setdefault("priority", "normal")
    ctl.setdefault("pause", False)
    ctl.setdefault("stop", False)
    ctl.setdefault("extra_pids", [])
    write_json(os.path.join(job, "control.json"), ctl)
    print(f"job {job}: {len(load_tasks(job))} tasks, control {ctl}")


def cmd_run(job):
    ctl_path, run_path = os.path.join(job, "control.json"), os.path.join(job, "running.json")
    os.makedirs(os.path.join(job, "logs"), exist_ok=True)
    table = process_table()
    for tid, pid in read_json(run_path, {}).items():          # leftovers of a crashed runner
        for p in tree(pid, table):
            terminate(p)
    tasks = load_tasks(job)
    done = {i for i, r in load_results(job).items() if r["rc"] == 0}
    failed = {i for i, r in load_results(job).items() if r["rc"] != 0}
    pending = [t for t in tasks if t["id"] not in done and t["id"] not in failed]
    running = {}                                                # id -> (Popen, start, logfile handle)
    suspended = False
    print(f"runner: {len(tasks)} tasks, {len(done)} done, {len(failed)} failed, {len(pending)} to run", flush=True)
    while pending or running:
        ctl = read_json(ctl_path, {})
        if ctl.get("stop"):
            table = process_table()
            for tid, (p, _, fh) in running.items():
                for q in tree(p.pid, table):
                    terminate(q)
                fh.close()
            write_json(run_path, {})
            ctl["stop"] = False
            write_json(ctl_path, ctl)
            print("runner: stopped on request", flush=True)
            return
        for tid in list(running):                               # reap finished tasks
            p, start, fh = running[tid]
            rc = p.poll()
            if rc is None:
                continue
            fh.close()
            res = {"id": tid, "rc": rc, "start": start, "end": time.time(),
                   "last": last_line(os.path.join(job, "logs", f"{tid}.log"))}
            with open(os.path.join(job, "results.jsonl"), "a", encoding="utf-8") as out:
                out.write(json.dumps(res, ensure_ascii=False) + "\n")
            del running[tid]
            print(f"runner: {tid} finished rc={rc}: {res['last'][:150]}", flush=True)
        pause = bool(ctl.get("pause"))
        while not pause and pending and len(running) < int(ctl.get("workers", 1)):
            t = pending.pop(0)
            env = dict(os.environ)
            env.update(t.get("env", {}))
            fh = open(os.path.join(job, "logs", f"{t['id']}.log"), "a", encoding="utf-8")
            fh.write(f"=== start {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n")
            fh.flush()
            try:
                p = subprocess.Popen(t["cmd"], cwd=t.get("cwd"), env=env, stdout=fh, stderr=subprocess.STDOUT)
            except OSError as exc:                              # bad command: record a failure, keep going
                fh.write(f"launch failed: {exc}\n")
                fh.close()
                with open(os.path.join(job, "results.jsonl"), "a", encoding="utf-8") as out:
                    out.write(json.dumps({"id": t["id"], "rc": -1, "start": time.time(), "end": time.time(),
                                          "last": f"launch failed: {exc}"}, ensure_ascii=False) + "\n")
                print(f"runner: {t['id']} could not start: {exc}", flush=True)
                continue
            running[t["id"]] = (p, time.time(), fh)
        table = process_table()
        pids = [q for p, _, _ in running.values() for q in tree(p.pid, table)]
        pids += [q for x in ctl.get("extra_pids", []) for q in tree(int(x), table)]
        cls = PRIORITY.get(ctl.get("priority", "normal"), 0x20)
        for q in pids:
            set_priority(q, cls)
        if pause != suspended:
            for q in pids:
                (suspend if pause else resume)(q)
            suspended = pause
            print(f"runner: {'paused' if pause else 'resumed'} {len(pids)} processes", flush=True)
        write_json(run_path, {tid: p.pid for tid, (p, _, _) in running.items()})
        time.sleep(2)
    write_json(run_path, {})
    print("runner: all tasks finished", flush=True)


def cmd_status(job):
    tasks = load_tasks(job)
    res = load_results(job)
    running = read_json(os.path.join(job, "running.json"), {})
    ctl = read_json(os.path.join(job, "control.json"), {})
    done = sum(1 for r in res.values() if r["rc"] == 0)
    failed = sum(1 for r in res.values() if r["rc"] != 0)
    print(f"{job}: {len(tasks)} tasks; done {done}, failed {failed}, running {len(running)}, "
          f"waiting {len(tasks) - done - failed - len(running)}; control {ctl}")
    for tid in running:
        print(f"  RUN  {tid}: {last_line(os.path.join(job, 'logs', f'{tid}.log'))[:160]}")
    for r in sorted(res.values(), key=lambda r: r["end"])[-10:]:
        print(f"  {'DONE' if r['rc'] == 0 else 'FAIL'} {r['id']} ({(r['end'] - r['start']) / 60:.1f} min): {r['last'][:140]}")


def cmd_ctl(job, pairs):
    path = os.path.join(job, "control.json")
    ctl = read_json(path, {})
    for kv in pairs:
        k, v = kv.split("=", 1)
        if k in ("pause", "stop"):
            ctl[k] = v.lower() in ("1", "true", "yes", "on")
        elif k == "workers":
            ctl[k] = int(v)
        elif k == "extra_pids":
            ctl[k] = [int(x) for x in v.split(",") if x]
        else:
            ctl[k] = v
    write_json(path, ctl)
    print(ctl)


def cmd_retry(job):
    res = load_results(job)
    keep = [r for r in res.values() if r["rc"] == 0]
    with open(os.path.join(job, "results.jsonl"), "w", encoding="utf-8") as fh:
        for r in keep:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(f"forgot {len(res) - len(keep)} failed results")


if __name__ == "__main__":
    c, job = sys.argv[1], sys.argv[2]
    if c == "init":
        cmd_init(job, sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else None)
    elif c == "run":
        cmd_run(job)
    elif c == "status":
        cmd_status(job)
    elif c == "ctl":
        cmd_ctl(job, sys.argv[3:])
    elif c == "retry":
        cmd_retry(job)
