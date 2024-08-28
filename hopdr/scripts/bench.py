# This file is generated by [scripts/bench/gen.py](https://github.com/moratorium08/hflmc2/blob/master/scripts/bench/gen.py)
import argparse
import os
import signal
import subprocess
import json
import time

base = "/home/katsura/github.com/moratorium08/hflmc2/benchmark"
class ParseError(Exception):
    pass
# assumption: this script is placed at <project_root>/scripts
project_root = os.path.realpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../'))
base = os.path.join(project_root, './benchmark')
TARGET = '../target/release/check'
cmd_template = TARGET + ' {} --do-hoice-preprocess --print-stat --input {}'  # <option> <filename>
#cmd_template = TARGET + ' {} --no-mode-analysis --do-hoice-preprocess --input {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return 'cargo build --features stat --features "no_simplify_by_finding_eq" --bin check --release'
    #return 'cargo build --features "no_simplify_by_finding_eq" --bin check --release'


def config(c):
    global cfg
    cfg = c


def cli_arg(parser):
    return parser


def gen_cmd(file):
    args = []
    if file.endswith('.smt2'):
        args.append("--chc")
    ag = ' '.join(args)
    return cmd_template.format(ag, file)

def parse_dict_stat(title, data):
    l = data.split("\n")
    idx = None

    for (i, x) in enumerate(l):
        if x.startswith(title):
            idx = i
            break
    if idx is None:
        print("{} data not found".format(title))
        return None
    entries = dict()
    idx += 2
    while l[idx].startswith("- ") and idx < len(l):
        line = l[idx]
        name = line.split(":")[0][2:]
        data = line.split(":")[1].strip(" ").split(",")
        cnt = data[0].split(" ")[0]
        sec = data[1].strip(" ").split(" ")[0]
        entries[name] = dict()
        entries[name]["count"] = cnt
        entries[name]["time"] = sec
        idx += 1
    return entries

def parse_preprocess_stat(data):
    return parse_dict_stat("[Preprocess]", data)

def parse_check_stat(data):
    return parse_dict_stat("[Check]", data)

def parse_random_testing_stats(data):
    ls = data.split("\n")
    idx = 0
    target = None
    while idx < len(ls):
        l = ls[idx]
        if l.startswith("[[Random Testing Stats]]"):
            target = idx + 1
            break
        idx += 1
    if target is None:
        return None
    
    line = ls[target].replace(" ", "")
    d = {}
    for x in line.split(","):
        xs = x.split(":")
        d[xs[0]] = int(xs[1])
    return d


def parse_stat(data, title, keys):
    l = data.split("\n")
    idx = None
    for (i, x) in enumerate(l):
        if x.startswith(title):
            idx = i
            break
    if idx is None:
        print("{} data not found".format(title))
        return None
    idx += 1
    entries = dict()
    for (line, key) in zip(l[idx:], keys):
        entries[key] = line.replace(key+":", '').strip(" ")
    return entries

smt_keys = ["number of invokes of SMT solver", "total time"]
interpol_keys = ["count", "total time"]
chc_keys = interpol_keys
qe_keys = ["number of invokes of SMT solver", "total time"]


def parse_stdout(stdout):
    result_data = dict()
    import re
    m = re.search(r"linearity check (\d+)", stdout)
    if m is not None:
      result_data['nonlinearity'] = int(m.group(1))

    result_data['result'] = 'invalid' if 'Verification Result: Invalid' in stdout else 'unknown' if 'Verification Result: Unknown' in stdout else 'fail'

    preprocess = parse_preprocess_stat(stdout)
    if preprocess is not None:
        result_data['preprocess'] = preprocess
    check = parse_check_stat(stdout)
    if check is not None:
        result_data['check'] = check 
    smt = parse_stat(stdout, "[SMT]", smt_keys)
    if smt is not None:
        result_data['smt'] = smt
    interpol = parse_stat(stdout, "[Interpolation]", interpol_keys)
    if interpol is not None:
        result_data['interpol'] = interpol
    chc = parse_stat(stdout, "[CHC]", chc_keys)
    if chc is not None:
        result_data['chc'] = chc
    qe = parse_stat(stdout, "[QE]", chc_keys)
    if qe is not None:
        result_data['qe'] = qe
    count_stat = parse_random_testing_stats(stdout)
    if count_stat is not None:
        result_data['count_stat'] = count_stat
    return result_data

def p(file, result):
    if result['ok']:
        print(f'{file}\t{result["result"]}\t{result["total"]}\t{result["solver"]}')
    else:
        print(f'{file}\t{result["error"]}\t{cfg.args.timeout}\t{result["solver"]}')


def callback(file, result):
    print(file)

def stat(results):
    print(results)


TIMEOUT = 10
RETRY_COOLDOWN = 10

class Config:
    def __init__(self):
        pass

parser = argparse.ArgumentParser()
parser.add_argument("list", help="benchmark target name")
parser.add_argument("--timeout", help="timeout", default=TIMEOUT, type=int)
parser.add_argument('--json', help="set filename in which results will be saved", default=None)
parser.add_argument("--basedir", help="base directory", default=base)
parser = cli_arg(parser)
args = parser.parse_args()

cfg = Config()
cfg.args = args
cfg.root = './'
cfg.retry = 0
cfg.base = 'inputs'
config(cfg)

def preexec_fn():
    os.chdir(cfg.root)
    os.setsid()

def run(cmd, timeout=None):
    if timeout is None:
        timeout=args.timeout
    st = time.perf_counter()
    with subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, preexec_fn=preexec_fn) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
            ed = time.perf_counter()
            elapsed = ed - st
            return output, elapsed
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGINT)
                output, _ = p.communicate(timeout=10)
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except Exception as e:
                    print(e)
                    pass
                return output, timeout
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except Exception as e:
                    print(e)
                    pass
            except Exception as e:
                print(e)
                pass
            raise


def p(file, result):
    print(result)


results = []
def handle(file, parser, callback=p, retry=0):
    cmd = gen_cmd(file)
    try:
        stdout, t = run(cmd)
        stdout = stdout.decode('utf-8')
        result = parser(stdout)
        result['time'] = t
    except subprocess.TimeoutExpired:
        result = {'ok': False, 'error': 'timeout'}
        result['time'] = args.timeout
    if 'result' not in result:
        result['result'] = 'fail'
    if result['result'] == 'fail' and retry > 0:
        time.sleep(RETRY_COOLDOWN)
        handle(file, parser, callback, retry - 1)
    else:
        result['file'] = file
        result['size'] = os.path.getsize(file)
        callback(file, result)
        results.append(result)


def save_json(filename):
    with open(filename, "w") as f:
        json.dump(results, f)


def main():
    out, _ = run(pre_cmd(), timeout=1000)
    print(out.decode('utf-8'))
    with open(os.path.join(args.basedir, 'lists', args.list)) as f:
        files = f.read().strip('\n').split('\n')
    for file in files:
        handle(os.path.join(args.basedir, cfg.base, file), parse_stdout,
                callback=callback, retry=cfg.retry)
    stat(results)
    if args.json is not None:
        save_json(args.json)

main()
