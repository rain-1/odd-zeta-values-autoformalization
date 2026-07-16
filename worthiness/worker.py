"""Remote audit worker: run (a, n) jobs from a JSONL file, append results.

Usage: python3 worker.py jobs.jsonl results.jsonl [pool]
Resumable: jobs whose (a, n) already appear in results.jsonl are skipped.
"""

import json
import sys
from multiprocessing import Pool

from audit_map import job


def main():
    jobs_path, results_path = sys.argv[1], sys.argv[2]
    pool_size = int(sys.argv[3]) if len(sys.argv) > 3 else 4

    done = set()
    try:
        for line in open(results_path):
            r = json.loads(line)
            done.add((tuple(r["a"]), r["n"]))
    except FileNotFoundError:
        pass

    jobs = []
    for line in open(jobs_path):
        j = json.loads(line)
        if (tuple(j["a"]), j["n"]) not in done:
            jobs.append((j["a"], j["n"]))
    print(f"{len(jobs)} jobs to run ({len(done)} already done), "
          f"pool={pool_size}", flush=True)

    with Pool(pool_size) as pool, open(results_path, "a") as out:
        for row in pool.imap_unordered(job, jobs):
            out.write(json.dumps(row) + "\n")
            out.flush()
            tag = "ERR " + row["error"][:60] if "error" in row \
                else f"den(P)~10^{len(row['denP'])}"
            print(f"  a={row['a']} n={row['n']} {tag} "
                  f"[{row['secs']}s]", flush=True)
    print("all done", flush=True)


if __name__ == "__main__":
    main()
