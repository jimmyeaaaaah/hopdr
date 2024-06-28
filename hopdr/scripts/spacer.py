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
TARGET = 'z3'
options = "fp.xform.tail_simplifier_pve=false fp.validate=true fp.spacer.mbqi=false fp.spacer.use_iuc=true fp.spacer.global=true  fp.spacer.expand_bnd=true fp.spacer.q3.use_qgen=true fp.spacer.q3.instantiate=true fp.spacer.q3=true fp.spacer.ground_pobs=false"
cmd_template = TARGET + ' ' + options + ' {} {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return 'echo spacer'


def config(c):
    global cfg
    cfg = c


def cli_arg(parser):
    return parser


def gen_cmd(file):
    args = []
    ag = ' '.join(args)
    return cmd_template.format(ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'unsat' in stdout else 'valid' if 'sat' in stdout else 'fail'
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
                os.killpg(p.pid, signal.SIGKILL)
            except:
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